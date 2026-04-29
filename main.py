from fastapi import FastAPI, Request, Form, Depends, HTTPException
from fastapi.staticfiles import StaticFiles
from fastapi.templating import Jinja2Templates
from passlib.context import CryptContext
from pydantic import BaseModel
from urllib.parse import urlencode, urlparse, parse_qs
from fastapi.responses import RedirectResponse, Response,JSONResponse, StreamingResponse
from xml.sax.saxutils import escape
from urllib.parse import quote

import calendar
import json
from sqlmodel import Session, select
from sqlalchemy import func, or_, delete, text  # 用于搜索逻辑；text 用于团队硬删除时兼容清理工资结算表
from datetime import date, datetime,timedelta,time
from typing import Optional, List, Tuple
import itertools

#  导入数据库模型
from database import (GameRecord,Store, Room, User,
                      Customer, CustomerStoreLink,
                      Blacklist, BrandBlacklistEntry, PlayFrequency, create_db_and_tables, get_session,
                      ShiftSchedule, MaintenanceRecord, upsert_shift, get_month_shifts_map, get_month_date_range,
                      get_manager_performance_stats, get_shift_performance_stats,
                      HandoverTodo, HandoverTodoCustomerLink, FormedGameHandoverLink,SelfArrivalRecord,
                        # V3 员工管理 / 请假 / 考勤 / 工资流水 / 团队管理
                      EmployeeProfile,
                      EmployeeLeaveRequest,
                      EmployeeAttendanceRecord,
                      SalaryFlowRecord,
                      MonthlySalarySettlement,
                      EmployeeNotification,

                      EmployeeTeam,
                      EmployeeTeamMember,
                      TeamStoreAssignment,
                      TeamMonthlyAssessment,
                      TeamAssessmentDeductionItem,

                      engine)

app = FastAPI()

# 密码加密工具
pwd_context = CryptContext(schemes=["pbkdf2_sha256"], deprecated="auto")

# 挂载静态文件和模板
app.mount("/static", StaticFiles(directory="static"), name="static")
templates = Jinja2Templates(directory="templates")


# === 辅助函数 ===
def verify_password(plain_password, hashed_password):
    return pwd_context.verify(plain_password, hashed_password)

def get_password_hash(password):
    return pwd_context.hash(password)

def _get_all_store_list(session: Session):
    all_rooms = session.exec(select(Room)).all()
    return sorted(list(set([r.store_name for r in all_rooms])))

def _is_ajax_request(request: Request) -> bool:
    return request.headers.get("x-requested-with") == "XMLHttpRequest"

def _ajax_or_redirect_error(
    request: Request,
    *,
    message: str,
    redirect_url: str,
    status_code: int = 400
):
    if _is_ajax_request(request):
        return JSONResponse(
            {
                "ok": False,
                "message": message
            },
            status_code=status_code
        )
    return RedirectResponse(url=redirect_url, status_code=303)

def _safe_float(x):
    try:
        return float(x or 0)
    except:
        return 0.0

# =========================
# V3 员工请假 / 考勤 / 工资辅助函数
# =========================

def _get_shift_type_for_employee_on_date(
        session: Session,
        employee_name: str,
        work_date: date
) -> str:
    """
    获取某员工某天的排班班次。

    当前排班表 ShiftSchedule 是按 operator_name 存员工显示名，
    所以这里用 User.display_name / employee_name_snapshot 去匹配。

    返回值约定：
    - early   早班
    - mid     中班
    - bigmid  大中班
    - night   晚班
    - off     休息

    如果当天没有排班记录，第一版默认视为 off。
    """
    shift = session.exec(
        select(ShiftSchedule).where(
            ShiftSchedule.operator_name == employee_name,
            ShiftSchedule.work_date == work_date
        )
    ).first()

    if not shift:
        return "off"

    return shift.shift_type or "off"


def _get_employee_salary_profile(
        session: Session,
        user_id: int,
        employee_name: str
) -> EmployeeProfile:
    """
    获取员工工资档案。

    说明：
    第一阶段已经新增 EmployeeProfile。
    为了防止历史账号没有自动生成档案，这里做兜底：
    如果查不到档案，就即时创建一个默认档案。
    """
    profile = session.exec(
        select(EmployeeProfile).where(EmployeeProfile.user_id == user_id)
    ).first()

    if profile:
        return profile

    now = datetime.now()
    profile = EmployeeProfile(
        user_id=user_id,
        employee_no=None,
        display_name_snapshot=employee_name,
        position="普通员工",
        base_salary=2800.0,
        normal_daily_salary=105.74,
        bigmid_extra_salary=23.48,
        bigmid_daily_salary=129.22,
        hourly_salary=11.74,
        join_date=None,
        leave_date=None,
        remark="系统在请假流程中自动补建员工档案",
        created_at=now,
        updated_at=now
    )
    session.add(profile)
    session.commit()
    session.refresh(profile)
    return profile


def _calc_leave_deduct_amount(
        session: Session,
        user_id: int,
        employee_name: str,
        shift_type: str
) -> float:
    """
    计算请假扣款金额。

    业务规则：
    1. 休息日请假：不扣款；
    2. 大中班请假：扣大中班日薪 129.22；
    3. 其他上班班次请假：扣普通日薪 105.74；
    4. 审批通过的请假不影响全勤奖。
    """
    profile = _get_employee_salary_profile(session, user_id, employee_name)

    if shift_type == "off":
        return 0.0

    if shift_type == "bigmid":
        return round(float(profile.bigmid_daily_salary or 129.22), 2)

    return round(float(profile.normal_daily_salary or 105.74), 2)


def _shift_type_label(shift_type: str) -> str:
    """
    班次中文展示。
    """
    mapping = {
        "off": "休息",
        "early": "早班",
        "mid": "中班",
        "bigmid": "大中班",
        "night": "晚班",
    }
    return mapping.get(shift_type or "off", shift_type or "未知")


def _leave_status_label(status: str) -> str:
    """
    请假状态中文展示。
    """
    mapping = {
        "pending": "待审批",
        "approved": "已通过",
        "rejected": "已拒绝",
        "cancelled": "已撤销",
    }
    return mapping.get(status or "pending", status or "未知")


def _build_employees_url(
        store: str,
        tab: str,
        status_filter: str = "active",
        success: str = "",
        error: str = ""
) -> str:
    """
    构造员工管理模块跳转 URL。

    说明：
    你现在系统很多操作都是 RedirectResponse + query 参数提示，
    这里统一封装，避免中文参数导致 URL 混乱。
    """
    params = {
        "store": store or "",
        "tab": tab or "employee_list",
        "status_filter": status_filter or "active",
    }

    if success:
        params["success"] = success

    if error:
        params["error"] = error

    return "/employees?" + urlencode(params)

# =========================
# V3 员工管理：AJAX 局部刷新辅助函数
# =========================

def _employee_user_payload(emp: User, current_user: User) -> dict:
    """
    员工列表行局部刷新用的数据结构。

    用途：
    前端执行“停用 / 恢复”后，不刷新整个页面，
    只根据这里返回的数据更新当前员工这一行。
    """
    return {
        "id": emp.id,
        "username": emp.username,
        "display_name": emp.display_name,
        "role": emp.role,
        "role_label": "管理员" if emp.role == "admin" else "普通员工",
        "is_active": bool(getattr(emp, "is_active", True)),
        "status_label": "在职" if getattr(emp, "is_active", True) else "已停用",
        "deleted_at": emp.deleted_at.strftime("%Y-%m-%d %H:%M:%S") if getattr(emp, "deleted_at", None) else "",
        "is_current_user": emp.id == current_user.id,
    }


def _leave_request_payload(item: EmployeeLeaveRequest) -> dict:
    """
    请假申请行局部刷新用的数据结构。

    用途：
    1. 员工提交请假后，前端可以新增一行；
    2. 管理员审批通过/拒绝后，前端只更新当前请假记录这一行。
    """
    return {
        "id": item.id,
        "user_id": item.user_id,
        "employee_name": item.employee_name_snapshot,
        "leave_date": str(item.leave_date),
        "apply_date": str(item.apply_date),
        "shift_type": item.shift_type,
        "shift_label": _shift_type_label(item.shift_type),
        "reason": item.reason or "",
        "remark": item.remark or "",
        "status": item.status,
        "status_label": _leave_status_label(item.status),
        "estimated_deduct_amount": round(float(item.estimated_deduct_amount or 0), 2),
        "final_deduct_amount": round(float(item.final_deduct_amount or 0), 2),
        "approved_by_name": item.approved_by_name or "",
        "approved_at": item.approved_at.strftime("%Y-%m-%d %H:%M:%S") if item.approved_at else "",
        "approval_note": item.approval_note or "",
        "attendance_record_id": item.attendance_record_id,
        "salary_flow_id": item.salary_flow_id,
    }

def _attendance_event_type_label(event_type: str) -> str:
    """
    考勤事件类型中文展示。

    注意：
    工作失误不属于考勤事件，不放在这里；
    工作失误造成的扣款，后续进入“工资调整流水”。
    """
    mapping = {
        "leave": "请假",
        "late": "迟到",
        "absent": "旷工",
        "other": "其他",
    }
    return mapping.get(event_type or "other", event_type or "未知")


def _attendance_record_payload(item: EmployeeAttendanceRecord) -> dict:
    """
    考勤记录行局部刷新用的数据结构。

    用途：
    管理员新增迟到 / 旷工 / 工作失误后，
    前端不刷新页面，只把这条记录插入表格顶部。
    """
    return {
        "id": item.id,
        "user_id": item.user_id,
        "employee_name": item.employee_name_snapshot,
        "event_date": str(item.event_date),
        "event_type": item.event_type,
        "event_type_label": _attendance_event_type_label(item.event_type),
        "shift_type": item.shift_type,
        "shift_label": _shift_type_label(item.shift_type),
        "reason": item.reason or "",
        "remark": item.remark or "",
        "status": item.status,
        "affect_full_attendance": bool(item.affect_full_attendance),
        "deduct_amount": round(float(item.deduct_amount or 0), 2),
        "is_salary_generated": bool(item.is_salary_generated),
        "salary_flow_id": item.salary_flow_id,
        "created_by_name": item.created_by_name or "",
        "created_at": item.created_at.strftime("%Y-%m-%d %H:%M:%S") if item.created_at else "",
    }

def _salary_flow_category_label(flow_category: str) -> str:
    """
    工资流水大类中文展示。

    说明：
    这里主要服务管理员“工资调整”页展示。
    后续“我的工资”也可以复用。
    """
    mapping = {
        "base_salary": "基础工资",
        "personal_commission": "个人提成",
        "team_commission": "团队提成",
        "bonus": "奖金",
        "deduction": "扣款",
        "attendance": "考勤相关",
        "manual_adjustment": "手工调整",
        "replacement_work": "顶班/加班",
        "settlement": "结算修正",
    }
    return mapping.get(flow_category or "manual_adjustment", flow_category or "其他")


def _salary_flow_type_label(flow_type: str) -> str:
    """
    工资流水类型中文展示。

    注意：
    工作失误扣款属于工资调整流水，不属于考勤记录，不影响全勤奖。
    """
    mapping = {
        "mistake_deduct": "工作失误扣款",
        "replacement_pay": "顶班补贴",
        "overtime_pay": "加班补贴",
        "manual_bonus": "临时奖金",
        "manual_deduct": "临时扣款",
        "manual_correction": "工资修正",
        "other_adjustment": "其他调整",

        # 兼容后续自动流水
        "leave_deduct": "请假扣款",
        "late_deduct": "迟到扣款",
        "absent_deduct": "旷工扣款",
        "monthly_base_salary": "月基础工资",
        "personal_order_commission": "个人订单提成",
        "team_bonus_share": "团队奖金分摊",
        "team_target_bonus_share": "团队目标奖金分摊",
        "team_non_result_bonus_share": "团队非结果性奖金分摊",
        "team_zero_mistake_bonus_share": "团队零失误奖分摊",
        "full_attendance_bonus": "全勤奖",
        "sales_champion_bonus": "销冠奖",
    }
    return mapping.get(flow_type or "other_adjustment", flow_type or "其他调整")


def _salary_flow_payload(item: SalaryFlowRecord) -> dict:
    """
    工资流水行局部刷新用的数据结构。

    用途：
    1. 管理员新增工资调整后，前端只在表格顶部新增一行；
    2. 管理员删除工资调整后，前端只删除当前行。
    """
    return {
        "id": item.id,
        "user_id": item.user_id,
        "employee_name": item.employee_name_snapshot,
        "salary_year": item.salary_year,
        "salary_month": item.salary_month,
        "flow_date": str(item.flow_date),
        "flow_category": item.flow_category,
        "flow_category_label": _salary_flow_category_label(item.flow_category),
        "flow_type": item.flow_type,
        "flow_type_label": _salary_flow_type_label(item.flow_type),
        "amount": round(float(item.amount or 0), 2),
        "title": item.title or "",
        "description": item.description or "",
        "source_type": item.source_type or "",
        "source_id": item.source_id,
        "is_auto": bool(item.is_auto),
        "is_locked": bool(item.is_locked),
        "is_visible_to_employee": bool(item.is_visible_to_employee),
        "created_by_name": item.created_by_name or "",
        "created_at": item.created_at.strftime("%Y-%m-%d %H:%M:%S") if item.created_at else "",
    }

# =========================
# V3 员工管理：我的工资辅助函数
# =========================

def _salary_settlement_status_label(status: str) -> str:
    """
    月度工资结算状态中文展示。

    当前工资结算三态：
    - draft：草稿，可重算，可继续调整；
    - confirmed：已确认，不直接重算，可发放，可退回草稿；
    - paid：已发放并锁定，不可重算，不可删除当月工资流水。

    兼容旧状态：
    - locked：旧版单独锁定状态，仍按“已发放并锁定”展示。
    """
    mapping = {
        "draft": "草稿",
        "confirmed": "已确认",
        "paid": "已发放并锁定",

        # 兼容旧数据
        "locked": "已发放并锁定",
    }
    return mapping.get(status or "draft", status or "未知")


def _build_my_salary_data(
        session: Session,
        user: User,
        year: int,
        month: int
) -> dict:
    """
    构建“我的工资”页面数据。

    第一版展示口径：
    1. 只展示当前登录员工自己的工资数据；
    2. 工资明细来自 SalaryFlowRecord；
    3. 只展示 is_visible_to_employee=True 的流水；
    4. 如果 MonthlySalarySettlement 已经生成，则展示最终工资和结算状态；
    5. 如果尚未生成结算，则只展示当前工资流水净变化，不假装已经完成最终工资结算。

    注意：
    本函数只读数据，不生成工资流水，不生成结算。
    后续“工资结算”模块才负责统一生成基础工资、提成、团队奖金、全勤奖、销冠奖等自动流水。
    """
    # ===== 1. 查询员工工资档案 =====
    # 说明：
    # 这里不调用 _get_employee_salary_profile，避免用户打开页面时隐式写库。
    profile = session.exec(
        select(EmployeeProfile).where(EmployeeProfile.user_id == user.id)
    ).first()

    # ===== 2. 查询员工本月可见工资流水 =====
    salary_flows = session.exec(
        select(SalaryFlowRecord).where(
            SalaryFlowRecord.user_id == user.id,
            SalaryFlowRecord.salary_year == year,
            SalaryFlowRecord.salary_month == month,
            SalaryFlowRecord.is_visible_to_employee == True
        ).order_by(
            SalaryFlowRecord.flow_date.desc(),
            SalaryFlowRecord.id.desc()
        )
    ).all()

    # ===== 3. 查询员工本月工资结算汇总 =====
    settlement = session.exec(
        select(MonthlySalarySettlement).where(
            MonthlySalarySettlement.user_id == user.id,
            MonthlySalarySettlement.salary_year == year,
            MonthlySalarySettlement.salary_month == month
        )
    ).first()

    # ===== 4. 汇总工资流水 =====
    income_total = 0.0
    deduction_total = 0.0
    net_change_total = 0.0

    category_map = {}

    for flow in salary_flows:
        amount = round(float(flow.amount or 0), 2)
        net_change_total += amount

        if amount >= 0:
            income_total += amount
            category_income = amount
            category_deduction = 0.0
        else:
            deduction_total += abs(amount)
            category_income = 0.0
            category_deduction = abs(amount)

        category_key = flow.flow_category or "manual_adjustment"

        if category_key not in category_map:
            category_map[category_key] = {
                "flow_category": category_key,
                "flow_category_label": _salary_flow_category_label(category_key),
                "income_total": 0.0,
                "deduction_total": 0.0,
                "net_total": 0.0,
                "count": 0,
            }

        category_map[category_key]["income_total"] += category_income
        category_map[category_key]["deduction_total"] += category_deduction
        category_map[category_key]["net_total"] += amount
        category_map[category_key]["count"] += 1

    income_total = round(income_total, 2)
    deduction_total = round(deduction_total, 2)
    net_change_total = round(net_change_total, 2)

    category_rows = list(category_map.values())

    for row in category_rows:
        row["income_total"] = round(row["income_total"], 2)
        row["deduction_total"] = round(row["deduction_total"], 2)
        row["net_total"] = round(row["net_total"], 2)

    # 收入高、扣款高、净额变化明显的类别优先展示
    category_rows.sort(
        key=lambda x: (abs(x["net_total"]), x["income_total"], x["deduction_total"]),
        reverse=True
    )

    # ===== 5. 输出给模板 =====
    return {
        "year": year,
        "month": month,

        # 员工基础档案
        "profile": profile,

        # 工资流水
        "salary_flows": salary_flows,
        "flow_count": len(salary_flows),
        "income_total": income_total,
        "deduction_total": deduction_total,
        "net_change_total": net_change_total,
        "category_rows": category_rows,

        # 月度结算
        "settlement": settlement,
        "has_settlement": settlement is not None,
        "settlement_status_label": _salary_settlement_status_label(settlement.status) if settlement else "未结算",
    }

# =========================
# V3 员工管理：工资结算辅助函数
# =========================

def _calc_personal_order_commission(order_count: int) -> float:
    """
    计算个人订单提成。

    规则：
    1. 660 单以内：2 元 / 单；
    2. 660-710：超出部分 3 元 / 单；
    3. 710-760：超出部分 4 元 / 单；
    4. 之后每 50 单，单价 +1 元；
    5. 示例：850 单 = 660*2 + 50*3 + 50*4 + 50*5 + 40*6 = 2160。
    """
    order_count = int(order_count or 0)

    if order_count <= 0:
        return 0.0

    if order_count <= 660:
        return round(order_count * 2.0, 2)

    total = 660 * 2.0
    remaining = order_count - 660
    unit_price = 3.0

    while remaining > 0:
        current_tier_count = min(remaining, 50)
        total += current_tier_count * unit_price
        remaining -= current_tier_count
        unit_price += 1.0

    return round(total, 2)


def _get_employee_order_count_for_month(
        session: Session,
        employee_name: str,
        year: int,
        month: int
) -> int:
    """
    统计某员工某月个人订单数。

    业务口径：
    1. 按 GameRecord.who_did 统计；
    2. 只统计 status == 'formed'；
    3. 使用 record_date 落在当月范围内；
    4. 包含常规牌局、自主到店、溢出单，因为当前 who_did 是既定个人单量统计口径。
    """
    month_start, month_end = _get_month_start_end(year, month)

    return len(session.exec(
        select(GameRecord).where(
            GameRecord.status == "formed",
            GameRecord.who_did == employee_name,
            GameRecord.record_date >= month_start,
            GameRecord.record_date <= month_end
        )
    ).all())


def _build_employee_order_count_map(
        session: Session,
        year: int,
        month: int
) -> dict:
    """
    构建本月员工订单数字典。

    用途：
    1. 计算个人提成；
    2. 判断销冠；
    3. 销冠并列时都发 200 元。
    """
    month_start, month_end = _get_month_start_end(year, month)

    games = session.exec(
        select(GameRecord).where(
            GameRecord.status == "formed",
            GameRecord.record_date >= month_start,
            GameRecord.record_date <= month_end
        )
    ).all()

    count_map = {}

    for g in games:
        name = _normalize_text(g.who_did)
        if not name:
            continue
        count_map[name] = count_map.get(name, 0) + 1

    return count_map


def _employee_has_full_attendance_bonus(
        session: Session,
        user_id: int,
        year: int,
        month: int
) -> bool:
    """
    判断员工本月是否有全勤奖。

    当前口径：
    1. 请假审批通过不影响全勤，所以 leave 且 affect_full_attendance=False 不影响；
    2. 迟到、旷工、管理员标记影响全勤的其他考勤异常，会取消全勤；
    3. 工作失误不在考勤表，不影响全勤。
    """
    month_start, month_end = _get_month_start_end(year, month)

    hit = session.exec(
        select(EmployeeAttendanceRecord).where(
            EmployeeAttendanceRecord.user_id == user_id,
            EmployeeAttendanceRecord.event_date >= month_start,
            EmployeeAttendanceRecord.event_date <= month_end,
            EmployeeAttendanceRecord.affect_full_attendance == True
        )
    ).first()

    return hit is None


def _get_employee_team_for_month(
        session: Session,
        user_id: int,
        year: int,
        month: int
) -> Tuple[Optional[EmployeeTeam], Optional[EmployeeTeamMember]]:
    """
    获取员工某月所属团队。

    第一版口径：
    1. 优先找当前 is_active=True 的团队成员关系；
    2. 如果以后需要严格按 joined_at / left_at 判断历史月份，可在这里扩展；
    3. 如果一个员工被误加入多个团队，取 id 最小的一条，保证结算可运行。
    """
    member = session.exec(
        select(EmployeeTeamMember).where(
            EmployeeTeamMember.user_id == user_id,
            EmployeeTeamMember.is_active == True
        ).order_by(EmployeeTeamMember.id)
    ).first()

    if not member:
        return None, None

    team = session.get(EmployeeTeam, member.team_id)
    if not team:
        return None, member

    return team, member


def _delete_unlocked_auto_settlement_flows(
        session: Session,
        user_id: int,
        year: int,
        month: int,
        settlement_id: Optional[int] = None
):
    """
    删除某员工某月旧的“工资结算自动流水”。

    说明：
    1. 只删除 source_type == salary_settlement 的自动流水；
    2. 不删除请假、迟到、旷工、工资调整等来源流水；
    3. 如果旧流水已锁定，则禁止重算。
    """
    query = select(SalaryFlowRecord).where(
        SalaryFlowRecord.user_id == user_id,
        SalaryFlowRecord.salary_year == year,
        SalaryFlowRecord.salary_month == month,
        SalaryFlowRecord.source_type == "salary_settlement",
        SalaryFlowRecord.is_auto == True
    )

    old_flows = session.exec(query).all()

    if settlement_id:
        extra_flows = session.exec(
            select(SalaryFlowRecord).where(
                SalaryFlowRecord.source_type == "salary_settlement",
                SalaryFlowRecord.source_id == settlement_id,
                SalaryFlowRecord.is_auto == True
            )
        ).all()

        for f in extra_flows:
            if f not in old_flows:
                old_flows.append(f)

    for f in old_flows:
        if getattr(f, "is_locked", False):
            raise ValueError("该员工存在已锁定的工资结算流水，不能重算")

    for f in old_flows:
        session.delete(f)


def _create_salary_settlement_flow(
        session: Session,
        *,
        user_obj: User,
        year: int,
        month: int,
        amount: float,
        flow_category: str,
        flow_type: str,
        title: str,
        description: str,
        settlement_id: int,
        operator: User
):
    """
    创建工资结算自动流水。

    说明：
    1. 只处理由工资结算模块自动生成的项目；
    2. 请假扣款、迟到扣款、工资调整等已有流水不在这里重复生成；
    3. amount 为 0 时不生成，避免员工“我的工资”里出现无意义流水。
    """
    amount = round(float(amount or 0), 2)
    if amount == 0:
        return None

    flow = SalaryFlowRecord(
        user_id=user_obj.id,
        employee_name_snapshot=user_obj.display_name,
        salary_year=year,
        salary_month=month,
        flow_date=date(year, month, calendar.monthrange(year, month)[1]),

        flow_category=flow_category,
        flow_type=flow_type,
        amount=amount,

        title=title,
        description=description,

        source_type="salary_settlement",
        source_id=settlement_id,

        is_auto=True,
        is_locked=False,
        is_visible_to_employee=True,

        created_by_user_id=operator.id,
        created_by_name=operator.display_name,

        created_at=datetime.now(),
        updated_at=datetime.now()
    )

    session.add(flow)
    return flow


def _sum_salary_flows_for_settlement(
        session: Session,
        user_id: int,
        year: int,
        month: int
) -> dict:
    """
    汇总员工某月全部工资流水，用于写入 MonthlySalarySettlement。

    注意：
    1. final_salary 直接等于全部工资流水 amount 总和；
    2. deduction_total 是所有负数流水绝对值合计；
    3. manual_adjustment_total 统计管理员手工流水净额，方便后台查看。
    """
    flows = session.exec(
        select(SalaryFlowRecord).where(
            SalaryFlowRecord.user_id == user_id,
            SalaryFlowRecord.salary_year == year,
            SalaryFlowRecord.salary_month == month
        )
    ).all()

    result = {
        "base_salary_total": 0.0,
        "personal_commission_total": 0.0,
        "team_commission_total": 0.0,
        "bonus_total": 0.0,
        "deduction_total": 0.0,
        "manual_adjustment_total": 0.0,
        "final_salary": 0.0,
    }

    for f in flows:
        amount = round(float(f.amount or 0), 2)
        category = f.flow_category or ""

        result["final_salary"] += amount

        if category == "base_salary":
            result["base_salary_total"] += amount
        elif category == "personal_commission":
            result["personal_commission_total"] += amount
        elif category == "team_commission":
            result["team_commission_total"] += amount
        elif category == "bonus":
            result["bonus_total"] += amount

        if amount < 0:
            result["deduction_total"] += abs(amount)

        if not f.is_auto:
            result["manual_adjustment_total"] += amount

    for k in result:
        result[k] = round(result[k], 2)

    return result


def _salary_settlement_payload(item: MonthlySalarySettlement) -> dict:
    """
    工资结算行局部刷新数据。

    用途：
    管理员生成、确认、发放、锁定工资后，前端只更新当前员工这一行。
    """
    final_salary = round(float(item.final_salary or 0), 2)
    social_security_amount = round(float(getattr(item, "social_security_amount", 0) or 0), 2)
    actual_salary = round(final_salary - social_security_amount, 2)

    return {
        "id": item.id,
        "user_id": item.user_id,
        "employee_name": item.employee_name_snapshot,
        "salary_year": item.salary_year,
        "salary_month": item.salary_month,

        "base_salary_total": round(float(item.base_salary_total or 0), 2),
        "personal_commission_total": round(float(item.personal_commission_total or 0), 2),
        "team_commission_total": round(float(item.team_commission_total or 0), 2),
        "bonus_total": round(float(item.bonus_total or 0), 2),
        "deduction_total": round(float(item.deduction_total or 0), 2),
        "manual_adjustment_total": round(float(item.manual_adjustment_total or 0), 2),
        "final_salary": final_salary,
        "social_security_amount": social_security_amount,
        "actual_salary": actual_salary,

        "personal_order_count": item.personal_order_count or 0,

        "team_id": item.team_id,
        "team_name": item.team_name_snapshot or "",

        "status": item.status,
        "status_label": _salary_settlement_status_label(item.status),

        "calculated_at": item.calculated_at.strftime("%Y-%m-%d %H:%M:%S") if item.calculated_at else "",
        "confirmed_by_name": item.confirmed_by_name or "",
        "confirmed_at": item.confirmed_at.strftime("%Y-%m-%d %H:%M:%S") if item.confirmed_at else "",
        "paid_at": item.paid_at.strftime("%Y-%m-%d %H:%M:%S") if item.paid_at else "",
    }


def _calculate_salary_for_one_employee(
        session: Session,
        *,
        user_obj: User,
        year: int,
        month: int,
        operator: User,
        all_order_count_map: dict
) -> MonthlySalarySettlement:
    """
    计算单个员工某月工资。

    本函数会：
    1. 获取或创建 MonthlySalarySettlement；
    2. 删除旧的未锁定工资结算自动流水；
    3. 重新生成基础工资、个人提成、团队奖金、全勤奖、销冠奖流水；
    4. 汇总所有工资流水，写入 MonthlySalarySettlement。
    """
    now = datetime.now()

    settlement = session.exec(
        select(MonthlySalarySettlement).where(
            MonthlySalarySettlement.user_id == user_obj.id,
            MonthlySalarySettlement.salary_year == year,
            MonthlySalarySettlement.salary_month == month
        )
    ).first()

    # 只有草稿工资允许重算。
    # 已确认工资如果要重算，必须先退回草稿；
    # 已发放并锁定工资永远不允许重算。
    if settlement and settlement.status in {"confirmed", "paid", "locked"}:
        raise ValueError(
            f"{user_obj.display_name} 的工资当前为【{_salary_settlement_status_label(settlement.status)}】，不能直接重算")

    if not settlement:
        settlement = MonthlySalarySettlement(
            user_id=user_obj.id,
            employee_name_snapshot=user_obj.display_name,
            salary_year=year,
            salary_month=month,
            status="draft",
            created_at=now,
            updated_at=now
        )
        session.add(settlement)
        session.flush()

    # 删除旧的工资结算自动流水，避免重复生成基础工资、提成、奖金。
    _delete_unlocked_auto_settlement_flows(
        session=session,
        user_id=user_obj.id,
        year=year,
        month=month,
        settlement_id=settlement.id
    )
    session.flush()

    profile = _get_employee_salary_profile(
        session=session,
        user_id=user_obj.id,
        employee_name=user_obj.display_name
    )

    personal_order_count = all_order_count_map.get(user_obj.display_name, 0)
    personal_commission = _calc_personal_order_commission(personal_order_count)

    # ===== 团队奖金 =====
    team, _ = _get_employee_team_for_month(session, user_obj.id, year, month)

    team_bonus = 0.0
    team_id = None
    team_name_snapshot = None

    if team:
        team_assessment = _calculate_team_assessment(
            session=session,
            team=team,
            year=year,
            month=month
        )
        team_bonus = round(float(team_assessment.per_member_bonus_amount or 0), 2)
        team_id = team.id
        team_name_snapshot = team.name

    # ===== 全勤奖 =====
    has_full_attendance = _employee_has_full_attendance_bonus(
        session=session,
        user_id=user_obj.id,
        year=year,
        month=month
    )
    full_attendance_bonus = 200.0 if has_full_attendance else 0.0

    # ===== 销冠奖：并列都发 200 =====
    max_order_count = max(all_order_count_map.values()) if all_order_count_map else 0
    sales_champion_bonus = 0.0
    if personal_order_count > 0 and personal_order_count == max_order_count:
        sales_champion_bonus = 200.0

    # ===== 生成自动工资流水 =====
    base_salary = round(float(profile.base_salary or 2800.0), 2)

    _create_salary_settlement_flow(
        session=session,
        user_obj=user_obj,
        year=year,
        month=month,
        amount=base_salary,
        flow_category="base_salary",
        flow_type="monthly_base_salary",
        title="基础工资",
        description=f"{year}年{month}月基础工资。",
        settlement_id=settlement.id,
        operator=operator
    )

    _create_salary_settlement_flow(
        session=session,
        user_obj=user_obj,
        year=year,
        month=month,
        amount=personal_commission,
        flow_category="personal_commission",
        flow_type="personal_order_commission",
        title="个人订单提成",
        description=f"{year}年{month}月个人订单 {personal_order_count} 单，对应提成 {personal_commission:.2f} 元。",
        settlement_id=settlement.id,
        operator=operator
    )

    _create_salary_settlement_flow(
        session=session,
        user_obj=user_obj,
        year=year,
        month=month,
        amount=team_bonus,
        flow_category="team_commission",
        flow_type="team_bonus_share",
        title="团队奖金分摊",
        description=f"{year}年{month}月团队【{team_name_snapshot or '-'}】人均团队奖金 {team_bonus:.2f} 元。",
        settlement_id=settlement.id,
        operator=operator
    )

    _create_salary_settlement_flow(
        session=session,
        user_obj=user_obj,
        year=year,
        month=month,
        amount=full_attendance_bonus,
        flow_category="bonus",
        flow_type="full_attendance_bonus",
        title="全勤奖",
        description="本月无影响全勤的迟到、旷工或其他考勤异常，发放全勤奖 200 元。",
        settlement_id=settlement.id,
        operator=operator
    )

    _create_salary_settlement_flow(
        session=session,
        user_obj=user_obj,
        year=year,
        month=month,
        amount=sales_champion_bonus,
        flow_category="bonus",
        flow_type="sales_champion_bonus",
        title="销冠奖",
        description=f"本月个人订单数 {personal_order_count} 单，为本月最高单量，发放销冠奖 200 元。",
        settlement_id=settlement.id,
        operator=operator
    )

    session.flush()

    totals = _sum_salary_flows_for_settlement(
        session=session,
        user_id=user_obj.id,
        year=year,
        month=month
    )

    settlement.employee_name_snapshot = user_obj.display_name
    settlement.base_salary_total = totals["base_salary_total"]
    settlement.personal_commission_total = totals["personal_commission_total"]
    settlement.team_commission_total = totals["team_commission_total"]
    settlement.bonus_total = totals["bonus_total"]
    settlement.deduction_total = totals["deduction_total"]
    settlement.manual_adjustment_total = totals["manual_adjustment_total"]
    settlement.final_salary = totals["final_salary"]

    settlement.personal_order_count = personal_order_count

    settlement.team_id = team_id
    settlement.team_name_snapshot = team_name_snapshot

    settlement.status = "draft"
    settlement.calculated_at = now
    settlement.updated_at = now

    session.add(settlement)
    session.flush()

    return settlement


def _build_salary_settlement_data(
        session: Session,
        year: int,
        month: int
) -> dict:
    """
    构建管理员“工资结算”页面数据。

    说明：
    1. 展示所有在职员工；
    2. 如果某员工已有本月结算记录，则展示结算数据；
    3. 如果还没有生成结算，前端显示“未生成”。
    """
    employees = session.exec(
        select(User).where(
            User.is_active == True
        ).order_by(User.role, User.id)
    ).all()

    settlements = session.exec(
        select(MonthlySalarySettlement).where(
            MonthlySalarySettlement.salary_year == year,
            MonthlySalarySettlement.salary_month == month
        )
    ).all()

    settlement_map = {s.user_id: s for s in settlements}

    rows = []

    for emp in employees:
        item = settlement_map.get(emp.id)
        rows.append({
            "employee": emp,
            "settlement": item,
            "payload": _salary_settlement_payload(item) if item else None,
        })

    generated_count = len([r for r in rows if r["settlement"]])
    total_final_salary = round(sum(float(r["settlement"].final_salary or 0) for r in rows if r["settlement"]), 2)
    # paid 是新版“已发放并锁定”状态；
    # locked 是旧版遗留状态，这里合并计入已归档数量。
    paid_count = len([
        r for r in rows
        if r["settlement"] and r["settlement"].status in {"paid", "locked"}
    ])

    # locked_count 保留给前端旧字段使用；新版不再单独强调。
    locked_count = len([
        r for r in rows
        if r["settlement"] and r["settlement"].status == "locked"
    ])

    return {
        "year": year,
        "month": month,
        "rows": rows,
        "employee_count": len(rows),
        "generated_count": generated_count,
        "paid_count": paid_count,
        "locked_count": locked_count,
        "total_final_salary": total_final_salary,
    }

def _salary_settlement_summary_payload(data: dict) -> dict:
    """
    工资结算顶部概览的 AJAX 安全返回结构。

    说明：
    _build_salary_settlement_data() 是给 Jinja2 模板用的，
    里面包含 User / MonthlySalarySettlement 等 ORM 对象，不能直接放进 JSONResponse。
    所以 AJAX 返回时，只取前端需要刷新的纯数字字段。
    """
    return {
        "year": data.get("year"),
        "month": data.get("month"),
        "employee_count": int(data.get("employee_count") or 0),
        "generated_count": int(data.get("generated_count") or 0),
        "paid_count": int(data.get("paid_count") or 0),
        "locked_count": int(data.get("locked_count") or 0),
        "total_final_salary": round(float(data.get("total_final_salary") or 0), 2),
    }


# =========================
# V3 员工管理：激励白板辅助函数
# =========================

def _get_month_start_end(year: int, month: int) -> Tuple[date, date]:
    """
    获取某年某月的起止日期。

    用途：
    激励白板只看“本月”数据：
    - 门店本月订单量
    - 员工本月订单量
    - 本月考勤异常记录
    """
    last_day = calendar.monthrange(year, month)[1]
    return date(year, month, 1), date(year, month, last_day)


def _get_store_active_room_count(session: Session, store_obj: Store) -> int:
    """
    统计某门店启用包间数。

    兼容规则：
    1. 优先按新版 store_id 查询 Room；
    2. 如果查不到，再按旧字段 Room.store_name 查询；
    3. 只统计 is_active=True 的包间；
    4. 返回值用于计算门店目标订单量：
       启用包间数 × 当月天数 × 2。
    """
    room_names = set()

    # 新版：通过 store_id 关联
    if getattr(store_obj, "id", None) and store_obj.id > 0:
        rooms_by_id = session.exec(
            select(Room).where(
                Room.store_id == store_obj.id,
                Room.is_active == True
            )
        ).all()

        for r in rooms_by_id:
            if r.name:
                room_names.add(r.name)

    # 兼容旧数据：通过 store_name 关联
    rooms_by_name = session.exec(
        select(Room).where(
            Room.store_name == store_obj.name,
            Room.is_active == True
        )
    ).all()

    for r in rooms_by_name:
        if r.name:
            room_names.add(r.name)

    return len(room_names)


def _build_employee_whiteboard_data(
        session: Session,
        year: int,
        month: int
) -> dict:
    """
    构建员工管理 -> 激励白板数据。

    统计口径：
    1. 门店订单量：
       GameRecord.status == 'formed'
       record_date 在本月内
       按 store_name 统计
       包含 normal / self_arrival / overflow，因为这里看的是“订单总量/桌数激励”。

    2. 门店目标订单量：
       启用包间数 × 当月天数 × 2。

    3. 员工订单量：
       按 GameRecord.who_did 统计。
       0 单员工不展示。

    4. 考勤异常：
       展示 EmployeeAttendanceRecord 本月记录。
       包含 leave / late / absent / other。
    """
    month_start, month_end = _get_month_start_end(year, month)
    days_in_month = calendar.monthrange(year, month)[1]

    # ===== 1. 门店订单量 =====
    active_store_objs = [
        s for s in get_store_list(session)
        if getattr(s, "is_active", True)
    ]

    month_games = session.exec(
        select(GameRecord).where(
            GameRecord.status == "formed",
            GameRecord.record_date >= month_start,
            GameRecord.record_date <= month_end
        )
    ).all()

    store_order_count_map = {}
    employee_order_count_map = {}

    for g in month_games:
        store_name = _normalize_text(g.store_name)
        if store_name:
            store_order_count_map[store_name] = store_order_count_map.get(store_name, 0) + 1

        # 员工单量固定按 GameRecord.who_did 统计
        who_did = _normalize_text(g.who_did)
        if who_did:
            employee_order_count_map[who_did] = employee_order_count_map.get(who_did, 0) + 1

    store_rows = []
    for store_obj in active_store_objs:
        active_room_count = _get_store_active_room_count(session, store_obj)
        target_order_count = active_room_count * days_in_month * 2
        actual_order_count = store_order_count_map.get(store_obj.name, 0)

        achievement_rate = 0.0
        if target_order_count > 0:
            achievement_rate = round(actual_order_count / target_order_count * 100, 2)

        store_rows.append({
            "store_name": store_obj.name,
            "active_room_count": active_room_count,
            "days_in_month": days_in_month,
            "target_order_count": target_order_count,
            "actual_order_count": actual_order_count,
            "remaining_order_count": max(target_order_count - actual_order_count, 0),
            "is_reached": actual_order_count >= target_order_count if target_order_count > 0 else False,
            "achievement_rate": achievement_rate,
        })

    # 门店按实际订单量倒序展示，方便看差距
    store_rows.sort(key=lambda x: (x["actual_order_count"], x["target_order_count"]), reverse=True)

    max_store_bar_value = max(
        [max(row["actual_order_count"], row["target_order_count"]) for row in store_rows] or [1]
    )

    for row in store_rows:
        row["actual_percent"] = round(row["actual_order_count"] / max_store_bar_value * 100, 2) if max_store_bar_value else 0
        row["target_percent"] = round(row["target_order_count"] / max_store_bar_value * 100, 2) if max_store_bar_value else 0

    # ===== 2. 员工订单量 =====
    employee_rows = []

    # 当前月份应该展示的员工名：在职员工 + 本月仍展示的已停用员工
    visible_employee_names = set(_get_visible_employee_names_for_month(session, year, month))

    # who_did 里可能存在历史名字，所以这里以实际有订单的人为准，0 单不展示
    for employee_name, order_count in employee_order_count_map.items():
        if order_count <= 0:
            continue

        employee_rows.append({
            "employee_name": employee_name,
            "order_count": order_count,
            "is_visible_employee": employee_name in visible_employee_names,
        })

    employee_rows.sort(key=lambda x: x["order_count"], reverse=True)

    max_employee_order_count = max([row["order_count"] for row in employee_rows] or [1])

    # 个人提成关键节点：660 起，每 50 单一个节点，至少展示到 860；
    # 如果实际最高单量超过 860，则自动继续补节点。
    commission_nodes = [660, 710, 760, 810, 860]
    while commission_nodes[-1] < max_employee_order_count:
        commission_nodes.append(commission_nodes[-1] + 50)

    employee_axis_max = max(max_employee_order_count, commission_nodes[-1], 1)

    for row in employee_rows:
        row["bar_percent"] = round(row["order_count"] / employee_axis_max * 100, 2)

    commission_node_rows = [
        {
            "value": node,
            "percent": round(node / employee_axis_max * 100, 2),
        }
        for node in commission_nodes
        if node <= employee_axis_max
    ]

    # ===== 3. 本月考勤异常/请假记录 =====
    attendance_rows = session.exec(
        select(EmployeeAttendanceRecord).where(
            EmployeeAttendanceRecord.event_date >= month_start,
            EmployeeAttendanceRecord.event_date <= month_end
        ).order_by(
            EmployeeAttendanceRecord.event_date.desc(),
            EmployeeAttendanceRecord.id.desc()
        )
    ).all()

    attendance_display_rows = []
    for item in attendance_rows:
        attendance_display_rows.append({
            "id": item.id,
            "employee_name": item.employee_name_snapshot,
            "event_date": item.event_date,
            "event_type": item.event_type,
            "event_type_label": _attendance_event_type_label(item.event_type),
            "shift_type": item.shift_type,
            "shift_label": _shift_type_label(item.shift_type),
            "reason": item.reason or "",
            "remark": item.remark or "",
            "deduct_amount": round(float(item.deduct_amount or 0), 2),
            "affect_full_attendance": bool(item.affect_full_attendance),
            "is_salary_generated": bool(item.is_salary_generated),
            "created_by_name": item.created_by_name or "",
            "created_at": item.created_at.strftime("%Y-%m-%d %H:%M:%S") if item.created_at else "",
        })

    # ===== 4. 顶部概览 =====
    reached_store_count = len([row for row in store_rows if row["is_reached"]])
    total_actual_orders = sum(row["actual_order_count"] for row in store_rows)
    total_target_orders = sum(row["target_order_count"] for row in store_rows)

    top_employee = employee_rows[0] if employee_rows else None

    return {
        "year": year,
        "month": month,
        "month_start": month_start,
        "month_end": month_end,
        "days_in_month": days_in_month,

        "store_rows": store_rows,
        "store_count": len(store_rows),
        "reached_store_count": reached_store_count,
        "total_actual_orders": total_actual_orders,
        "total_target_orders": total_target_orders,

        "employee_rows": employee_rows,
        "employee_count": len(employee_rows),
        "top_employee": top_employee,
        "commission_nodes": commission_node_rows,
        "employee_axis_max": employee_axis_max,

        "attendance_rows": attendance_display_rows,
        "attendance_count": len(attendance_display_rows),
    }

# =========================
# V3 员工管理：团队管理 / 团队考核辅助函数
# =========================

def _team_member_payload(member: EmployeeTeamMember, user_obj: Optional[User]) -> dict:
    """
    团队成员行局部刷新数据。

    说明：
    EmployeeTeamMember 表只存 user_id；
    前端展示姓名、角色、状态时需要结合 User 表。
    """
    return {
        "id": member.id,
        "team_id": member.team_id,
        "user_id": member.user_id,
        "display_name": user_obj.display_name if user_obj else f"员工ID {member.user_id}",
        "role": user_obj.role if user_obj else "",
        "role_label": "管理员" if user_obj and user_obj.role == "admin" else "普通员工",
        "is_user_active": bool(getattr(user_obj, "is_active", True)) if user_obj else False,
        "joined_at": str(member.joined_at) if member.joined_at else "",
        "is_active": bool(member.is_active),
        "remark": member.remark or "",
    }


def _team_store_payload(assignment: TeamStoreAssignment) -> dict:
    """
    团队负责门店行局部刷新数据。

    说明：
    用于 AJAX 新增 / 取消负责门店后，仅更新当前团队的门店列表区域。
    """
    return {
        "id": assignment.id,
        "team_id": assignment.team_id,
        "store_id": assignment.store_id,
        "store_name": assignment.store_name_snapshot,
        "is_active": bool(assignment.is_active),
    }


def _team_payload(team: EmployeeTeam) -> dict:
    """
    团队卡片局部刷新数据。

    当前主要用于新增团队后，前端提示用户刷新或局部插入。
    第一版为了稳妥，新增团队后建议提示刷新页面。
    """
    return {
        "id": team.id,
        "name": team.name,
        "description": team.description or "",
        "is_active": bool(team.is_active),
    }


def _team_non_result_release_rate(score: float) -> float:
    """
    非结果性考核奖金发放比例。

    规则：
    - 80 分及以上：100%
    - 60-80 分：80%
    - 50-60 分：50%
    - 40-50 分：40%
    - 30-40 分：30%
    - 20-30 分：20%
    - 10-20 分：10%
    - 10 分以下：0%
    """
    score = float(score or 0)

    if score >= 80:
        return 1.0
    if score >= 60:
        return 0.8
    if score >= 50:
        return 0.5
    if score >= 40:
        return 0.4
    if score >= 30:
        return 0.3
    if score >= 20:
        return 0.2
    if score >= 10:
        return 0.1
    return 0.0


def _get_or_create_team_assessment(
        session: Session,
        team: EmployeeTeam,
        year: int,
        month: int
) -> TeamMonthlyAssessment:
    """
    获取或创建某团队某月考核记录。

    说明：
    团队考核页面所有扣分项都要挂到某个月度考核记录下；
    如果管理员第一次进入本月团队考核，还没有记录，就自动创建草稿。
    """
    assessment = session.exec(
        select(TeamMonthlyAssessment).where(
            TeamMonthlyAssessment.team_id == team.id,
            TeamMonthlyAssessment.year == year,
            TeamMonthlyAssessment.month == month
        )
    ).first()

    if assessment:
        return assessment

    now = datetime.now()
    assessment = TeamMonthlyAssessment(
        team_id=team.id,
        team_name_snapshot=team.name,
        year=year,
        month=month,
        status="draft",
        created_at=now,
        updated_at=now
    )
    session.add(assessment)
    session.commit()
    session.refresh(assessment)
    return assessment


def _calculate_team_assessment(
        session: Session,
        team: EmployeeTeam,
        year: int,
        month: int
) -> TeamMonthlyAssessment:
    """
    计算团队某月考核结果。

    计算口径：
    1. 团队成员数量：EmployeeTeamMember.is_active=True；
    2. 团队奖金池：1000 × 团队成员数；
    3. 目标业绩池：团队奖金池 × 60%；
    4. 非结果性考核池：团队奖金池 × 40%；
    5. 门店目标：启用包间数 × 当月天数 × 2；
    6. 负责门店达标一个，释放目标业绩池的 1 / 负责门店数；
    7. 非结果性考核分 = 100 - 扣分项合计；
    8. 若非结果性考核分为 100 分，额外加入团队零失误奖 1000 元；
    9. 团队总奖金平均分给团队成员。
    """
    month_start, month_end = _get_month_start_end(year, month)
    days_in_month = calendar.monthrange(year, month)[1]

    assessment = _get_or_create_team_assessment(session, team, year, month)

    active_members = session.exec(
        select(EmployeeTeamMember).where(
            EmployeeTeamMember.team_id == team.id,
            EmployeeTeamMember.is_active == True
        )
    ).all()

    active_assignments = session.exec(
        select(TeamStoreAssignment).where(
            TeamStoreAssignment.team_id == team.id,
            TeamStoreAssignment.is_active == True
        )
    ).all()

    team_member_count = len(active_members)
    responsible_store_count = len(active_assignments)

    base_pool_amount = 1000.0 * team_member_count
    target_pool_amount = base_pool_amount * 0.6
    non_result_pool_amount = base_pool_amount * 0.4

    target_reached_store_count = 0

    for assignment in active_assignments:
        store_obj = session.get(Store, assignment.store_id)
        if not store_obj:
            continue

        active_room_count = _get_store_active_room_count(session, store_obj)
        target_order_count = active_room_count * days_in_month * 2

        actual_order_count = len(session.exec(
            select(GameRecord).where(
                GameRecord.status == "formed",
                GameRecord.store_name == store_obj.name,
                GameRecord.record_date >= month_start,
                GameRecord.record_date <= month_end
            )
        ).all())

        if target_order_count > 0 and actual_order_count >= target_order_count:
            target_reached_store_count += 1

    if responsible_store_count > 0:
        target_bonus_released_amount = round(
            target_pool_amount / responsible_store_count * target_reached_store_count,
            2
        )
    else:
        target_bonus_released_amount = 0.0

    deduction_items = session.exec(
        select(TeamAssessmentDeductionItem).where(
            TeamAssessmentDeductionItem.assessment_id == assessment.id
        )
    ).all()

    total_deduct_points = round(sum(float(x.deduct_points or 0) for x in deduction_items), 2)
    non_result_score = max(0.0, round(100.0 - total_deduct_points, 2))
    non_result_release_rate = _team_non_result_release_rate(non_result_score)
    non_result_bonus_amount = round(non_result_pool_amount * non_result_release_rate, 2)

    zero_mistake_bonus_amount = 1000.0 if non_result_score == 100.0 else 0.0

    total_team_bonus_amount = round(
        target_bonus_released_amount + non_result_bonus_amount + zero_mistake_bonus_amount,
        2
    )

    per_member_bonus_amount = round(
        total_team_bonus_amount / team_member_count,
        2
    ) if team_member_count > 0 else 0.0

    now = datetime.now()

    assessment.team_name_snapshot = team.name
    assessment.team_member_count = team_member_count
    assessment.base_pool_amount = round(base_pool_amount, 2)
    assessment.target_pool_amount = round(target_pool_amount, 2)
    assessment.non_result_pool_amount = round(non_result_pool_amount, 2)
    assessment.responsible_store_count = responsible_store_count
    assessment.target_reached_store_count = target_reached_store_count
    assessment.target_bonus_released_amount = target_bonus_released_amount
    assessment.non_result_score = non_result_score
    assessment.non_result_release_rate = non_result_release_rate
    assessment.non_result_bonus_amount = non_result_bonus_amount
    assessment.zero_mistake_bonus_amount = zero_mistake_bonus_amount
    assessment.total_team_bonus_amount = total_team_bonus_amount
    assessment.per_member_bonus_amount = per_member_bonus_amount
    assessment.updated_at = now

    session.add(assessment)
    session.commit()
    session.refresh(assessment)
    return assessment


def _team_assessment_payload(assessment: TeamMonthlyAssessment) -> dict:
    """
    团队考核结果局部刷新数据。

    用途：
    管理员点击“计算本月考核”后，前端只更新对应团队的考核结果卡片。
    """
    return {
        "id": assessment.id,
        "team_id": assessment.team_id,
        "team_name": assessment.team_name_snapshot,
        "year": assessment.year,
        "month": assessment.month,
        "team_member_count": assessment.team_member_count,
        "base_pool_amount": round(float(assessment.base_pool_amount or 0), 2),
        "target_pool_amount": round(float(assessment.target_pool_amount or 0), 2),
        "non_result_pool_amount": round(float(assessment.non_result_pool_amount or 0), 2),
        "responsible_store_count": assessment.responsible_store_count,
        "target_reached_store_count": assessment.target_reached_store_count,
        "target_bonus_released_amount": round(float(assessment.target_bonus_released_amount or 0), 2),
        "non_result_score": round(float(assessment.non_result_score or 0), 2),
        "non_result_release_rate": round(float(assessment.non_result_release_rate or 0), 2),
        "non_result_bonus_amount": round(float(assessment.non_result_bonus_amount or 0), 2),
        "zero_mistake_bonus_amount": round(float(assessment.zero_mistake_bonus_amount or 0), 2),
        "total_team_bonus_amount": round(float(assessment.total_team_bonus_amount or 0), 2),
        "per_member_bonus_amount": round(float(assessment.per_member_bonus_amount or 0), 2),
        "status": assessment.status,
    }


def _build_team_management_data(
        session: Session,
        year: int,
        month: int
) -> dict:
    """
    构建团队管理页数据。

    页面展示：
    1. 团队列表；
    2. 每个团队的成员；
    3. 每个团队负责门店；
    4. 每个团队本月考核；
    5. 每个团队本月扣分项；
    6. 可选员工、可选门店。
    """
    teams = session.exec(
        select(EmployeeTeam).order_by(EmployeeTeam.is_active.desc(), EmployeeTeam.id)
    ).all()

    users = session.exec(
        select(User).order_by(User.is_active.desc(), User.role, User.id)
    ).all()
    user_map = {u.id: u for u in users}

    stores = [
        s for s in get_store_list(session)
        if getattr(s, "is_active", True)
    ]
    store_map = {s.id: s for s in stores if getattr(s, "id", None)}

    team_cards = []

    for team in teams:
        members = session.exec(
            select(EmployeeTeamMember).where(
                EmployeeTeamMember.team_id == team.id
            ).order_by(
                EmployeeTeamMember.is_active.desc(),
                EmployeeTeamMember.id
            )
        ).all()

        assignments = session.exec(
            select(TeamStoreAssignment).where(
                TeamStoreAssignment.team_id == team.id
            ).order_by(
                TeamStoreAssignment.is_active.desc(),
                TeamStoreAssignment.id
            )
        ).all()

        assessment = _get_or_create_team_assessment(session, team, year, month)

        deduction_items = session.exec(
            select(TeamAssessmentDeductionItem).where(
                TeamAssessmentDeductionItem.assessment_id == assessment.id
            ).order_by(
                TeamAssessmentDeductionItem.deduct_date.desc(),
                TeamAssessmentDeductionItem.id.desc()
            )
        ).all()

        active_member_user_ids = {
            m.user_id for m in members if m.is_active
        }

        active_store_ids = {
            a.store_id for a in assignments if a.is_active
        }

        available_users = [
            u for u in users
            if getattr(u, "is_active", True) and u.id not in active_member_user_ids
        ]

        available_stores = [
            s for s in stores
            if s.id not in active_store_ids
        ]

        team_cards.append({
            "team": team,
            "members": members,
            "assignments": assignments,
            "assessment": assessment,
            "deduction_items": deduction_items,
            "available_users": available_users,
            "available_stores": available_stores,
        })

    return {
        "year": year,
        "month": month,
        "team_cards": team_cards,
        "all_active_users": [u for u in users if getattr(u, "is_active", True)],
        "all_active_stores": stores,
        "user_map": user_map,
        "store_map": store_map,
    }

def _create_employee_notification_for_attendance(
        session: Session,
        *,
        attendance: EmployeeAttendanceRecord,
        operator: User
):
    """
    为考勤扣款事件生成员工通知。

    业务规则：
    1. 管理员新增迟到 / 旷工 / 工作失误记录后，通知其他在职员工；
    2. 第一版采用“每个接收人一条通知”，便于每个员工独立标记已读；
    3. 不通知被登记的员工本人；
    4. 当前只生成通知记录，后续全局弹窗轮询接口会读取 EmployeeNotification。
    """
    # 没有扣款金额时，不生成扣款通告。
    if float(attendance.deduct_amount or 0) <= 0:
        return

    event_label = _attendance_event_type_label(attendance.event_type)

    title = f"{event_label}扣款通告"
    content = (
        f"{attendance.employee_name_snapshot}因{attendance.reason}"
        f"扣款{float(attendance.deduct_amount or 0):.2f}元"
    )

    receivers = session.exec(
        select(User).where(
            User.is_active == True,
            User.id != attendance.user_id
        ).order_by(User.id)
    ).all()

    now = datetime.now()

    for receiver in receivers:
        notice = EmployeeNotification(
            target_user_id=receiver.id,
            target_user_name_snapshot=receiver.display_name,
            title=title,
            content=content,
            notification_type=f"attendance_{attendance.event_type}",
            source_type="attendance_record",
            source_id=attendance.id,
            is_read=False,
            read_at=None,
            created_at=now
        )
        session.add(notice)


def _employee_module_counts_payload(session: Session) -> dict:
    """
    员工模块顶部统计局部刷新数据。

    当前用于“停用 / 恢复”后同步顶部统计卡片。
    """
    all_users = session.exec(select(User).order_by(User.id)).all()
    active_users = [u for u in all_users if getattr(u, "is_active", True)]
    inactive_users = [u for u in all_users if not getattr(u, "is_active", True)]

    return {
        "total_count": len(all_users),
        "active_count": len(active_users),
        "inactive_count": len(inactive_users),
        "admin_count": len([u for u in active_users if u.role == "admin"]),
        "operator_count": len([u for u in active_users if u.role != "admin"]),
    }


def _employee_ajax_success(
        *,
        message: str,
        action: str,
        payload: Optional[dict] = None
):
    """
    员工管理 AJAX 成功响应统一格式。
    """
    return JSONResponse({
        "ok": True,
        "message": message,
        "action": action,
        "payload": payload or {}
    })


def _employee_ajax_error(message: str, status_code: int = 400):
    """
    员工管理 AJAX 错误响应统一格式。
    """
    return JSONResponse({
        "ok": False,
        "message": message
    }, status_code=status_code)

def _get_visible_employee_names_for_month(
        session: Session,
        year: int,
        month: int
) -> List[str]:
    """
    V3 员工管理联动规则：
    1. 在职员工：始终展示；
    2. 已停用员工：展示到停用月份为止；
       例如 2026-04-24 停用，则 2026年4月仍展示，2026年5月开始不展示。
    3. 这样排班表和店长业绩页不会在下个月继续出现离职/停用员工。
    """
    month_start = date(year, month, 1)

    if month == 12:
        next_month_start = date(year + 1, 1, 1)
    else:
        next_month_start = date(year, month + 1, 1)

    users = session.exec(
        select(User).order_by(User.id)
    ).all()

    visible_names = []

    for u in users:
        # 被设置为隐藏展示的账号：仍可登录，但不进入排班表和各班次业绩展示
        if getattr(u, "hide_from_schedule_performance", False):
            continue

        is_active = getattr(u, "is_active", True)

        # 1. 在职员工始终展示
        if is_active:
            visible_names.append(u.display_name)
            continue

        # 2. 兼容旧数据：如果没有 deleted_at，默认不展示已停用员工
        deleted_at = getattr(u, "deleted_at", None)
        if not deleted_at:
            continue

        # 3. 如果 deleted_at 是字符串，做一次兼容解析
        if isinstance(deleted_at, str):
            parsed = None
            for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M", "%Y-%m-%d"):
                try:
                    parsed = datetime.strptime(deleted_at[:19], fmt)
                    break
                except Exception:
                    pass
            if not parsed:
                continue
            deleted_at = parsed

        deleted_month_start = date(deleted_at.year, deleted_at.month, 1)

        # 4. 展示到停用月份为止：选中月份 <= 停用月份，则仍展示
        if month_start <= deleted_month_start:
            visible_names.append(u.display_name)

    # 去重，防止 display_name 重复导致前端行重复
    return list(dict.fromkeys(visible_names))




SELF_ARRIVAL_PAYMENT_METHODS = [
    "代客收款",
    "代客验券",
    "用户小程序自定",
    "美团团购",
    "抖音团购",
    "美团预定",
]

FORMED_SOURCE_NORMAL = "normal"
FORMED_SOURCE_SELF_ARRIVAL = "self_arrival"
FORMED_SOURCE_OVERFLOW = "overflow"

FORMED_SOURCE_OPTIONS = {
    FORMED_SOURCE_NORMAL,
    FORMED_SOURCE_SELF_ARRIVAL,
    FORMED_SOURCE_OVERFLOW,
}

OVERFLOW_PAYMENT_METHOD = "溢出收款"


def _normalize_formed_source_filter(source_filter: Optional[str]) -> str:
    source_filter = _normalize_text(source_filter) or FORMED_SOURCE_NORMAL
    if source_filter not in FORMED_SOURCE_OPTIONS:
        return FORMED_SOURCE_NORMAL
    return source_filter

def _has_any_system_receipt(game: GameRecord) -> bool:
    return (_safe_float(game.wechat_pay) > 0) or (_safe_float(game.Alipay) > 0)


def _parse_required_self_arrival_order_start_time(order_start_time_full: str) -> Tuple[date, str]:
    """
    自主到店登记专用：
    必填订单开始时间，输出：
    - record_date: date
    - order_start_time: 'YYYY-%m-%d %H:%M'
    """
    raw = _normalize_text(order_start_time_full)
    if not raw:
        raise ValueError("订单开始时间不能为空")

    for fmt in ("%Y-%m-%dT%H:%M", "%Y-%m-%d %H:%M"):
        try:
            dt_obj = datetime.strptime(raw, fmt)
            return dt_obj.date(), dt_obj.strftime("%Y-%m-%d %H:%M")
        except ValueError:
            pass

    raise ValueError("订单开始时间格式不正确")




def _game_wechat_list(game: GameRecord):
    wx_list = [
        game.player_1_wechat,
        game.player_2_wechat,
        game.player_3_wechat,
        game.player_4_wechat,
    ]
    # 去空、去重
    return list({wx.strip() for wx in wx_list if wx and wx.strip()})

def _build_formed_redirect_url(
    store: str,
    source_filter: str = FORMED_SOURCE_NORMAL,
    pay_status: str = "all",
    date_filter: str = "today",
    start_date: str = "",
    end_date: str = "",
    payment_method_filter: str = "all",
    error: str = "",
    focus_game_id: Optional[int] = None,
    duplicate_warning_message: str = "",
    reopen_edit_game_id: Optional[int] = None,
) -> str:
    params = {
        "store": store,
        "source_filter": _normalize_formed_source_filter(source_filter),
        "pay_status": pay_status or "all",
        "date_filter": date_filter or "today",
        "start_date": start_date or "",
        "end_date": end_date or "",
        "payment_method_filter": payment_method_filter or "all",
    }

    if error:
        params["error"] = error
    if focus_game_id:
        params["focus_game_id"] = int(focus_game_id)
    if duplicate_warning_message:
        params["duplicate_warning_message"] = duplicate_warning_message
    if reopen_edit_game_id:
        params["reopen_edit_game_id"] = int(reopen_edit_game_id)

    return "/formed-games?" + urlencode(params)


def _normalize_text(v: Optional[str]) -> str:
    return (v or "").strip()

def _daterange(start_date: date, end_date: date):
    cur = start_date
    while cur <= end_date:
        yield cur
        cur += timedelta(days=1)

def _normalize_player_slots(
    player_1: str, player_2: str, player_3: str, player_4: str,
    player_1_wechat: str, player_2_wechat: str, player_3_wechat: str, player_4_wechat: str
) -> List[dict]:
    """
    统一整理 4 个参与人坑位，便于做规则校验。
    """
    return [
        {"idx": 1, "name": _normalize_text(player_1), "wechat": _normalize_text(player_1_wechat)},
        {"idx": 2, "name": _normalize_text(player_2), "wechat": _normalize_text(player_2_wechat)},
        {"idx": 3, "name": _normalize_text(player_3), "wechat": _normalize_text(player_3_wechat)},
        {"idx": 4, "name": _normalize_text(player_4), "wechat": _normalize_text(player_4_wechat)},
    ]

def _get_active_brand_blacklist_entry_by_wechat(session: Session, wechat_id: Optional[str]) -> Optional[BrandBlacklistEntry]:
    wx = _normalize_text(wechat_id)
    if not wx:
        return None

    return session.exec(
        select(BrandBlacklistEntry).where(
            BrandBlacklistEntry.wechat_id == wx,
            BrandBlacklistEntry.is_active == True
        )
    ).first()


def _get_active_brand_blacklist_entry_by_identity(
    session: Session,
    nickname: Optional[str],
    wechat_id: Optional[str]
) -> Optional[BrandBlacklistEntry]:
    """
    品牌黑名单命中规则：
    1. 优先按 wechat_id 精确命中
    2. 若 wechat_id 为空，再允许 nickname 精确命中兜底
       （防止前端只输昵称未回填微信号时漏掉明显已拉黑的人）
    """
    wx = _normalize_text(wechat_id)
    nm = _normalize_text(nickname)

    if wx:
        hit = session.exec(
            select(BrandBlacklistEntry).where(
                BrandBlacklistEntry.wechat_id == wx,
                BrandBlacklistEntry.is_active == True
            )
        ).first()
        if hit:
            return hit

    if nm and not wx:
        hit = session.exec(
            select(BrandBlacklistEntry).where(
                BrandBlacklistEntry.nickname == nm,
                BrandBlacklistEntry.is_active == True
            )
        ).first()
        if hit:
            return hit

    return None


def _check_brand_blacklist_for_slots(session: Session, slots: List[dict]) -> Tuple[bool, str]:
    """
    品牌黑名单校验：
    任一参与人命中品牌黑名单，则整单禁止创建/修改。
    """
    for s in slots:
        entry = _get_active_brand_blacklist_entry_by_identity(
            session=session,
            nickname=s.get("name"),
            wechat_id=s.get("wechat")
        )
        if entry:
            display_name = _normalize_text(s.get("name")) or entry.nickname or "该用户"
            display_wx = _normalize_text(s.get("wechat")) or entry.wechat_id or "未填写微信号"
            reason = _normalize_text(entry.reason) or "未填写原因"
            return False, f"参与人【{display_name} / {display_wx}】已被加入品牌黑名单，原因：{reason}，无法创建/修改本牌局"

    return True, ""


def _validate_players_and_customer_binding_detailed(
    session: Session,
    slots: List[dict]
) -> Tuple[bool, str, List[int], str]:
    """
    参与人规则（详细返回版）：
    返回：
      ok, msg, indices, error_type

    error_type 约定：
    - pair_required
    - duplicate_wechat_diff_name_in_game
    - wechat_bound_other_nickname
    """
    # 1) 坑位内成对校验
    for s in slots:
        if (s["name"] and not s["wechat"]) or (s["wechat"] and not s["name"]):
            return False, f"参与人{s['idx']}的昵称和微信号必须同时填写", [s["idx"]], "pair_required"

    # 2) 同一局内：相同微信号 + 不同昵称 => 禁止
    wechat_to_slot = {}
    wechat_to_name = {}

    for s in slots:
        wx = s["wechat"]
        nm = s["name"]
        if not wx:
            continue

        if wx in wechat_to_name and wechat_to_name[wx] != nm:
            conflict_indices = sorted(list({wechat_to_slot[wx], s["idx"]}))
            return False, f"同一局中微信号【{wx}】对应了不同昵称，无法提交", conflict_indices, "duplicate_wechat_diff_name_in_game"

        wechat_to_name[wx] = nm
        wechat_to_slot[wx] = s["idx"]

    # 3) 顾客库严格模式：微信号已存在，但昵称不一致
    for s in slots:
        wx = s["wechat"]
        nm = s["name"]
        if not wx:
            continue

        existing_customer = session.exec(
            select(Customer).where(Customer.wechat_id == wx)
        ).first()

        if existing_customer and _normalize_text(existing_customer.nickname) != nm:
            return False, "该微信号已绑定其他昵称，请核对", [s["idx"]], "wechat_bound_other_nickname"

    return True, "", [], ""


def _validate_players_and_customer_binding(session: Session, slots: List[dict]) -> Tuple[bool, str]:
    """
    兼容旧调用：仅返回 ok, msg
    """
    ok, msg, _, _ = _validate_players_and_customer_binding_detailed(session, slots)
    return ok, msg

def _parse_reservation_datetime_local(start_time_full: str) -> Tuple[date, str]:
    """
    解析前端 datetime-local：
    输入示例：2026-03-26T19:30
    输出：
      - record_date: 2026-03-26
      - start_time:  "03-26 19:30"
    这里继续沿用你当前前端更容易兼容的显示格式。
    """
    try:
        dt_obj = datetime.strptime(start_time_full, "%Y-%m-%dT%H:%M")
        return dt_obj.date(), dt_obj.strftime("%m-%d %H:%M")
    except ValueError:
        # 兜底：使用今天 + 原字符串
        return date.today(), start_time_full


def _get_monthly_serial_number(session: Session, store_name: str, reservation_date: date) -> int:
    """
    V2 月序号规则：
    同一门店、同一自然月内递增；
    按预约时间所属月份计算。
    """
    month_start = reservation_date.replace(day=1)
    month_end = reservation_date.replace(day=calendar.monthrange(reservation_date.year, reservation_date.month)[1])

    stmt = select(func.max(GameRecord.serial_number)).where(
        GameRecord.store_name == store_name,
        GameRecord.record_date >= month_start,
        GameRecord.record_date <= month_end
    )
    max_serial = session.exec(stmt).first()
    return (max_serial or 0) + 1


def _parse_self_arrival_order_start_time(order_start_time_full: str) -> Tuple[date, str]:
    """
    解析自主到店登记的订单开始时间。
    输入示例：2026-03-28T19:30
    输出：
      - order_date: 2026-03-28
      - order_start_time: "2026-03-28 19:30"
    """
    raw = _normalize_text(order_start_time_full)
    try:
        dt_obj = datetime.strptime(raw, "%Y-%m-%dT%H:%M")
        return dt_obj.date(), dt_obj.strftime("%Y-%m-%d %H:%M")
    except ValueError:
        try:
            dt_obj = datetime.strptime(raw, "%Y-%m-%d %H:%M")
            return dt_obj.date(), dt_obj.strftime("%Y-%m-%d %H:%M")
        except ValueError:
            return date.today(), raw


def _get_self_arrival_monthly_serial_number(session: Session, store_name: str, order_date: date) -> int:
    """
    自主到店登记月序号：
    同一门店、同一自然月内递增。
    """
    month_start = order_date.replace(day=1)
    month_end = order_date.replace(day=calendar.monthrange(order_date.year, order_date.month)[1])

    stmt = select(func.max(SelfArrivalRecord.serial_number)).where(
        SelfArrivalRecord.store_name == store_name,
        SelfArrivalRecord.order_date >= month_start,
        SelfArrivalRecord.order_date <= month_end
    )
    max_serial = session.exec(stmt).first()
    return (max_serial or 0) + 1

def _can_delete_unformed_game(user: User, game: GameRecord) -> bool:
    """
    未组齐撤销规则：
    - 超管：随时可撤销
    - 创建人：6小时内可撤销
    - 任意店长：超过6小时且仍未组齐后可撤销
    """
    if user.role == "admin":
        return True

    if game.status != "unformed":
        return False

    now = datetime.now()
    created_at = game.created_at or now
    over_6_hours = (now - created_at) >= timedelta(hours=6)

    if over_6_hours:
        return True

    # 6小时内，只允许创建人撤销
    return game.who_did == user.display_name

def _parse_optional_order_start_time(order_start_time_full: Optional[str]) -> Optional[str]:
    """
    解析已组齐区“订单开始时间”。
    前端若传 datetime-local，如：2026-03-26T19:30
    数据库存字符串，如：2026-03-26 19:30
    """
    raw = _normalize_text(order_start_time_full)
    if not raw:
        return None

    try:
        dt_obj = datetime.strptime(raw, "%Y-%m-%dT%H:%M")
        return dt_obj.strftime("%Y-%m-%d %H:%M")
    except ValueError:
        try:
            dt_obj = datetime.strptime(raw, "%Y-%m-%d %H:%M")
            return dt_obj.strftime("%Y-%m-%d %H:%M")
        except ValueError:
            return raw


def _player_changed(old_name: Optional[str], old_wechat: Optional[str],
                    new_name: Optional[str], new_wechat: Optional[str]) -> bool:
    """
    判断某个参与人坑位是否变化。
    只要昵称或微信号任一变化，就算变化。
    """
    return _normalize_text(old_name) != _normalize_text(new_name) or \
           _normalize_text(old_wechat) != _normalize_text(new_wechat)


def _game_effective_order_dt(game: GameRecord) -> datetime:
    """
    已组齐列表排序/筛选/查重使用的有效订单时间：
    1. 优先 order_start_time
    2. 为空时回退 record_date + start_time（兼容旧数据）
    """
    if game.order_start_time:
        for fmt in ("%Y-%m-%d %H:%M", "%Y-%m-%dT%H:%M"):
            try:
                return datetime.strptime(game.order_start_time, fmt)
            except ValueError:
                pass

    try:
        st = _normalize_text(game.start_time)
        if len(st) >= 11 and "-" in st and ":" in st:
            dt_str = f"{game.record_date.year}-{st}"
            return datetime.strptime(dt_str, "%Y-%m-%d %H:%M")
    except Exception:
        pass

    return datetime.combine(game.record_date, datetime.min.time())

def _format_duplicate_game_label(game: GameRecord) -> str:
    order_time_text = _normalize_text(game.order_start_time)
    if not order_time_text:
        order_time_text = _game_effective_order_dt(game).strftime("%Y-%m-%d %H:%M")

    if _normalize_text(game.record_source) == FORMED_SOURCE_OVERFLOW:
        ext_store_text = _normalize_text(game.external_store_name) or "未填写外部门店"
        room_text = _normalize_text(game.room_name) or "未填写外部包间"
        return f"#{game.serial_number}（{ext_store_text}｜{room_text}｜{order_time_text}）"

    room_text = _normalize_text(game.room_name) or "未填写包间"
    return f"#{game.serial_number}（{room_text}｜{order_time_text}）"


def _find_possible_duplicate_formed_game(
    session: Session,
    current_game: GameRecord,
    tolerance_minutes: int = 10
) -> Optional[GameRecord]:
    current_source = _normalize_text(current_game.record_source) or FORMED_SOURCE_NORMAL
    current_dt = _game_effective_order_dt(current_game)
    tolerance_seconds = tolerance_minutes * 60

    base_stmt = select(GameRecord).where(
        GameRecord.id != current_game.id,
        GameRecord.status == "formed",
        GameRecord.store_name == current_game.store_name,
        GameRecord.record_source == current_source
    )

    if current_source == FORMED_SOURCE_OVERFLOW:
        ext_store = _normalize_text(current_game.external_store_name)
        room_name = _normalize_text(current_game.room_name)
        if not ext_store or not room_name:
            return None

        candidates = session.exec(
            base_stmt.where(
                GameRecord.external_store_name == ext_store,
                GameRecord.room_name == room_name
            )
        ).all()
    else:
        room_name = _normalize_text(current_game.room_name)
        if not room_name:
            return None

        candidates = session.exec(
            base_stmt.where(GameRecord.room_name == room_name)
        ).all()

    hit_list = []
    for other in candidates:
        other_dt = _game_effective_order_dt(other)
        delta_seconds = abs((other_dt - current_dt).total_seconds())
        if delta_seconds <= tolerance_seconds:
            hit_list.append((delta_seconds, other))

    if not hit_list:
        return None

    hit_list.sort(key=lambda x: (x[0], -x[1].id))
    return hit_list[0][1]

"""
已组齐区复合筛选：
1. 全部 / 已收齐 / 未收齐
2. 当日 / 昨日 / 近两日 / 近七天 / 本月 / 上月 / 自定义区间
3. payment_method
"""
def _match_formed_game_filters(
    game: GameRecord,
    source_filter: str,
    pay_status: str,
    date_filter: str,
    start_date: Optional[str],
    end_date: Optional[str],
    payment_method_filter: str
) -> bool:
    source_filter = _normalize_formed_source_filter(source_filter)

    if _normalize_text(game.record_source or FORMED_SOURCE_NORMAL) != source_filter:
        return False

    # 1) 支付状态
    if pay_status == "paid" and not game.is_payAll:
        return False
    if pay_status == "unpaid" and game.is_payAll:
        return False

    # 2) 下单/支付方式
    if payment_method_filter and payment_method_filter != "all":
        if _normalize_text(game.payment_method) != payment_method_filter:
            return False

    # 3) 时间
    game_dt = _game_effective_order_dt(game)
    game_d = game_dt.date()
    today = date.today()

    if date_filter == "today":
        if game_d != today:
            return False
    elif date_filter == "yesterday":
        if game_d != (today - timedelta(days=1)):
            return False
    elif date_filter == "last2days":
        if game_d < (today - timedelta(days=1)) or game_d > today:
            return False
    elif date_filter == "last7":
        if game_d < (today - timedelta(days=6)) or game_d > today:
            return False
    elif date_filter == "this_month":
        if game_d.year != today.year or game_d.month != today.month:
            return False
    elif date_filter == "last_month":
        if today.month == 1:
            y, m = today.year - 1, 12
        else:
            y, m = today.year, today.month - 1
        if game_d.year != y or game_d.month != m:
            return False
    elif date_filter == "custom":
        if start_date:
            try:
                sd = datetime.strptime(start_date, "%Y-%m-%d").date()
                if game_d < sd:
                    return False
            except ValueError:
                pass
        if end_date:
            try:
                ed = datetime.strptime(end_date, "%Y-%m-%d").date()
                if game_d > ed:
                    return False
            except ValueError:
                pass

    return True


def _parse_export_date_range(
    export_date_filter: str,
    export_start_date: Optional[str],
    export_end_date: Optional[str]
) -> Tuple[date, date]:
    today = date.today()

    if export_date_filter == "today":
        return today, today

    if export_date_filter == "yesterday":
        d = today - timedelta(days=1)
        return d, d

    if export_date_filter == "last2days":
        return today - timedelta(days=1), today

    if export_date_filter == "last7":
        return today - timedelta(days=6), today

    if export_date_filter == "this_month":
        return today.replace(day=1), today

    if export_date_filter == "last_month":
        if today.month == 1:
            y, m = today.year - 1, 12
        else:
            y, m = today.year, today.month - 1
        start_d = date(y, m, 1)
        end_d = date(y, m, calendar.monthrange(y, m)[1])
        return start_d, end_d

    if export_date_filter == "custom":
        try:
            start_d = datetime.strptime((export_start_date or "").strip(), "%Y-%m-%d").date()
            end_d = datetime.strptime((export_end_date or "").strip(), "%Y-%m-%d").date()
        except Exception:
            raise HTTPException(status_code=400, detail="自定义导出时间格式不正确")

        if start_d > end_d:
            start_d, end_d = end_d, start_d
        return start_d, end_d

    return today, today

def _xml_cell(value) -> str:
    if value is None:
        value = ""

    if isinstance(value, bool):
        return f'<Cell><Data ss:Type="String">{"是" if value else "否"}</Data></Cell>'

    if isinstance(value, (int, float)):
        return f'<Cell><Data ss:Type="Number">{value}</Data></Cell>'

    text = escape(str(value))
    return f'<Cell><Data ss:Type="String">{text}</Data></Cell>'


def _build_formed_games_excel_xml(records: List[GameRecord], store_name: str, start_d: date, end_d: date) -> str:
    headers = [
        "ID",
        "门店",
        "月序号",
        "状态",
        "预约日期",
        "预约时间",
        "订单开始时间",
        "包间",
        "分数",
        "玩法",

        "参与人1昵称", "参与人1微信号", "参与人1备注",
        "参与人2昵称", "参与人2微信号", "参与人2备注",
        "参与人3昵称", "参与人3微信号", "参与人3备注",
        "参与人4昵称", "参与人4微信号", "参与人4备注",

        "整桌备注",
        "特殊备注",
        "下单/支付方式",
        "本单金额",
        "是否已收齐",
        "微信收款",
        "支付宝收款",
        "未收金额",
        "接待店长",
        "创建时间",
        "最后更新时间",
        "最后更新人"
    ]

    title = f"已组齐订单导出（{store_name}｜{start_d} ~ {end_d}）"
    rows_xml = []

    rows_xml.append(
        f'''
        <Row ss:AutoFitHeight="0" ss:Height="24">
            <Cell ss:MergeAcross="{len(headers)-1}" ss:StyleID="Title">
                <Data ss:Type="String">{escape(title)}</Data>
            </Cell>
        </Row>
        '''
    )

    header_cells = "".join(
        [f'<Cell ss:StyleID="Header"><Data ss:Type="String">{escape(h)}</Data></Cell>' for h in headers]
    )
    rows_xml.append(f'<Row>{header_cells}</Row>')

    for g in records:
        remaining = round((g.room_fee or 0) - (g.wechat_pay or 0) - (g.Alipay or 0), 2)
        if remaining < 0:
            remaining = 0

        row_data = [
            g.id,
            g.store_name,
            g.serial_number,
            g.status,
            str(g.record_date) if g.record_date else "",
            g.start_time or "",
            g.order_start_time or "",
            g.room_name or "",
            g.stakes or "",
            g.game_type or "",

            g.player_1 or "", g.player_1_wechat or "", g.player_1_note or "",
            g.player_2 or "", g.player_2_wechat or "", g.player_2_note or "",
            g.player_3 or "", g.player_3_wechat or "", g.player_3_note or "",
            g.player_4 or "", g.player_4_wechat or "", g.player_4_note or "",

            g.table_note or "",
            g.tags or "",
            g.payment_method or "",
            g.room_fee or 0,
            "是" if g.is_payAll else "否",
            g.wechat_pay or 0,
            g.Alipay or 0,
            remaining,
            g.who_did or "",
            g.created_at.strftime("%Y-%m-%d %H:%M:%S") if g.created_at else "",
            g.updated_at.strftime("%Y-%m-%d %H:%M:%S") if g.updated_at else "",
            g.updated_by or ""
        ]

        cell_xml = "".join([_xml_cell(v) for v in row_data])
        rows_xml.append(f"<Row>{cell_xml}</Row>")

    xml_content = f'''<?xml version="1.0" encoding="UTF-8"?>
<?mso-application progid="Excel.Sheet"?>
<Workbook xmlns="urn:schemas-microsoft-com:office:spreadsheet"
 xmlns:o="urn:schemas-microsoft-com:office:office"
 xmlns:x="urn:schemas-microsoft-com:office:excel"
 xmlns:ss="urn:schemas-microsoft-com:office:spreadsheet"
 xmlns:html="http://www.w3.org/TR/REC-html40">

    <Styles>
        <Style ss:ID="Default" ss:Name="Normal">
            <Alignment ss:Vertical="Center"/>
            <Borders/>
            <Font ss:FontName="Microsoft YaHei" ss:Size="10"/>
            <Interior/>
            <NumberFormat/>
            <Protection/>
        </Style>

        <Style ss:ID="Title">
            <Alignment ss:Horizontal="Center" ss:Vertical="Center"/>
            <Font ss:FontName="Microsoft YaHei" ss:Size="14" ss:Bold="1" ss:Color="#FFFFFF"/>
            <Interior ss:Color="#1D4ED8" ss:Pattern="Solid"/>
        </Style>

        <Style ss:ID="Header">
            <Alignment ss:Horizontal="Center" ss:Vertical="Center"/>
            <Font ss:FontName="Microsoft YaHei" ss:Size="10" ss:Bold="1" ss:Color="#FFFFFF"/>
            <Interior ss:Color="#2563EB" ss:Pattern="Solid"/>
        </Style>
    </Styles>

    <Worksheet ss:Name="已组齐订单导出">
        <Table>
            <Column ss:Width="60"/>
            <Column ss:Width="100"/>
            <Column ss:Width="60"/>
            <Column ss:Width="70"/>
            <Column ss:Width="90"/>
            <Column ss:Width="90"/>
            <Column ss:Width="120"/>
            <Column ss:Width="90"/>
            <Column ss:Width="90"/>
            <Column ss:Width="90"/>

            <Column ss:Width="90"/><Column ss:Width="120"/><Column ss:Width="160"/>
            <Column ss:Width="90"/><Column ss:Width="120"/><Column ss:Width="160"/>
            <Column ss:Width="90"/><Column ss:Width="120"/><Column ss:Width="160"/>
            <Column ss:Width="90"/><Column ss:Width="120"/><Column ss:Width="160"/>

            <Column ss:Width="160"/>
            <Column ss:Width="160"/>
            <Column ss:Width="120"/>
            <Column ss:Width="90"/>
            <Column ss:Width="80"/>
            <Column ss:Width="90"/>
            <Column ss:Width="90"/>
            <Column ss:Width="90"/>
            <Column ss:Width="90"/>
            <Column ss:Width="130"/>
            <Column ss:Width="130"/>
            <Column ss:Width="100"/>

            {''.join(rows_xml)}
        </Table>
        <WorksheetOptions xmlns="urn:schemas-microsoft-com:office:excel">
            <FreezePanes/>
            <FrozenNoSplit/>
            <SplitHorizontal>2</SplitHorizontal>
            <TopRowBottomPane>2</TopRowBottomPane>
            <ActivePane>2</ActivePane>
        </WorksheetOptions>
    </Worksheet>
</Workbook>
'''
    return xml_content


def _safe_ascii_export_filename(store: str, start_d: date, end_d: date) -> str:
    """
    避免某些环境/浏览器在 Content-Disposition 中处理中文文件名时报错
    """
    return f"formed_games_export_{start_d}_{end_d}.xls"



"""
dimension:
  - brand
  - store

统计口径：
1. 营收/订单：按时间区间统计，且仅统计 status='formed'
2. 顾客总数：历史总数，不受时间区间影响
3. 新增顾客数：按 created_at 落在时间区间内
4. 新增顾客转化率：新增顾客中，在当前时间区间内完成过 >=1 次成功组局
5. 复购顾客数：当前时间区间内完成过 >=2 次成功组局的顾客数
6. 顾客复购率：复购顾客数 / 顾客总数
"""
def get_brand_store_dashboard_stats(
    session: Session,
    dimension: str,
    store_name: Optional[str],
    start_date: date,
    end_date: date
):
    """
    dimension:
      - brand
      - store

    统计口径：
    1. 营收：溢出单不计入门店/品牌正常收支
    2. 桌数/订单数：溢出单要计入
    3. 顾客总数：历史总数，不受时间区间影响
    4. 新增顾客数：按 created_at 落在时间区间内
    5. 新增顾客转化率：新增顾客中，在当前时间区间内完成过 >=1 次成功组局
    6. 复购顾客数：当前时间区间内完成过 >=2 次成功组局的顾客数
    7. 顾客复购率：复购顾客数 / 顾客总数
    """

    is_store = (dimension == "store" and store_name)

    # ========= 1. 顾客主数据 =========
    all_customers = session.exec(select(Customer)).all()
    wechat_to_customer_id = {c.wechat_id: c.id for c in all_customers if c.wechat_id}

    # ========= 2. 历史顾客总数（不按时间过滤） =========
    if is_store:
        links = session.exec(
            select(CustomerStoreLink).where(CustomerStoreLink.store_name == store_name)
        ).all()
        customer_total_ids = set([l.customer_id for l in links])
        customer_total = len(customer_total_ids)
    else:
        customer_total_ids = set([c.id for c in all_customers])
        customer_total = len(customer_total_ids)

    # ========= 3. 选定范围内的成功组局 =========
    game_stmt = select(GameRecord).where(
        GameRecord.status == "formed",
        GameRecord.record_date >= start_date,
        GameRecord.record_date <= end_date
    )

    if is_store:
        game_stmt = game_stmt.where(GameRecord.store_name == store_name)

    period_games = session.exec(game_stmt).all()

    # 正常营收单：排除 overflow
    normal_period_games = [
        g for g in period_games
        if _normalize_text(g.record_source) != FORMED_SOURCE_OVERFLOW
    ]

    # 溢出单：单独统计
    overflow_period_games = [
        g for g in period_games
        if _normalize_text(g.record_source) == FORMED_SOURCE_OVERFLOW
    ]

    # ========= 4. 营收（溢出单不计入） =========
    total_revenue = round(sum(_safe_float(g.wechat_pay) + _safe_float(g.Alipay) for g in normal_period_games), 2)

    offline_revenue = round(sum(
        (_safe_float(g.wechat_pay) + _safe_float(g.Alipay))
        for g in normal_period_games
        if g.payment_method == "代客收款"
    ), 2)

    voucher_revenue = round(sum(
        (_safe_float(g.wechat_pay) + _safe_float(g.Alipay))
        for g in normal_period_games
        if g.payment_method == "代客验券"
    ), 2)

    other_revenue = round(total_revenue - offline_revenue - voucher_revenue, 2)
    if other_revenue < 0:
        other_revenue = 0.0

    # ========= 5. 桌数 / 订单数（溢出单要计入） =========
    order_count = len(period_games)

    # ========= 6. 当前时间区间内顾客成功组局次数 =========
    # 这里继续按全部 formed 统计，包含溢出单
    period_visit_count_by_customer_id = {}
    for g in period_games:
        wx_list = _game_wechat_list(g)
        for wx in wx_list:
            cid = wechat_to_customer_id.get(wx)
            if cid:
                period_visit_count_by_customer_id[cid] = period_visit_count_by_customer_id.get(cid, 0) + 1

    # ========= 7. 新增顾客数 =========
    if is_store:
        new_links = session.exec(
            select(CustomerStoreLink).where(
                CustomerStoreLink.store_name == store_name,
                CustomerStoreLink.created_at >= start_date,
                CustomerStoreLink.created_at <= end_date
            )
        ).all()
        new_customer_ids = set([l.customer_id for l in new_links])
    else:
        new_customers = session.exec(
            select(Customer).where(
                Customer.created_at >= start_date,
                Customer.created_at <= end_date
            )
        ).all()
        new_customer_ids = set([c.id for c in new_customers])

    new_customer_count = len(new_customer_ids)

    # ========= 8. 新增顾客转化 =========
    converted_new_customer_ids = {
        cid for cid in new_customer_ids
        if period_visit_count_by_customer_id.get(cid, 0) >= 1
    }
    converted_new_customer_count = len(converted_new_customer_ids)

    new_customer_conversion_rate = round(
        (converted_new_customer_count / new_customer_count * 100) if new_customer_count else 0,
        2
    )

    # ========= 9. 复购顾客数 =========
    repurchase_customer_ids = {
        cid for cid, cnt in period_visit_count_by_customer_id.items()
        if cnt >= 2
    }
    repurchase_customer_count = len(repurchase_customer_ids)

    repurchase_rate = round(
        (repurchase_customer_count / customer_total * 100) if customer_total else 0,
        2
    )

    # ========= 10. 趋势图（日） =========
    revenue_by_day = {d.strftime("%Y-%m-%d"): 0.0 for d in _daterange(start_date, end_date)}
    orders_by_day = {d.strftime("%Y-%m-%d"): 0 for d in _daterange(start_date, end_date)}

    # 收入趋势：只算正常营收单
    for g in normal_period_games:
        day_key = g.record_date.strftime("%Y-%m-%d")
        revenue_by_day[day_key] += (_safe_float(g.wechat_pay) + _safe_float(g.Alipay))

    # 桌数趋势：全部 formed 都算，包含溢出单
    for g in period_games:
        day_key = g.record_date.strftime("%Y-%m-%d")
        orders_by_day[day_key] += 1

    trend_labels = list(revenue_by_day.keys())
    revenue_trend = [round(revenue_by_day[k], 2) for k in trend_labels]
    order_trend = [orders_by_day[k] for k in trend_labels]

    # ========= 11. 溢出单补充统计 =========
    overflow_order_count = len(overflow_period_games)
    overflow_profit_total = round(sum(
        (_safe_float(g.wechat_pay) + _safe_float(g.Alipay) - _safe_float(g.room_fee))
        for g in overflow_period_games
    ), 2)

    entity_name = "耍牌（品牌）" if not is_store else store_name

    return {
        "entity_name": entity_name,
        "dimension": "store" if is_store else "brand",
        "store_name": store_name if is_store else "",

        "revenue": {
            "total": total_revenue,
            "offline": offline_revenue,
            "voucher": voucher_revenue,
            "other": other_revenue,
        },

        "customer": {
            "total": customer_total,
            "new": new_customer_count,
            "converted_new": converted_new_customer_count,
            "new_conversion_rate": new_customer_conversion_rate,
            "repurchase": repurchase_customer_count,
            "repurchase_rate": repurchase_rate,
        },

        "order": {
            "count": order_count
        },

        "overflow": {
            "order_count": overflow_order_count,
            "profit_total": overflow_profit_total,
        },

        "charts": {
            "trend_labels": trend_labels,
            "revenue_trend": revenue_trend,
            "order_trend": order_trend,
            "revenue_composition": [
                offline_revenue,
                voucher_revenue,
                other_revenue
            ],
            "customer_funnel": [
                customer_total,
                new_customer_count,
                converted_new_customer_count,
                repurchase_customer_count
            ]
        }
    }


def get_all_store_list(session: Session):
    all_rooms = session.exec(select(Room)).all()
    return sorted(list(set([r.store_name for r in all_rooms])))

def check_room_belongs_to_store(session: Session, store_name: str, room_name: str) -> bool:
    room = session.exec(
        select(Room).where(
            Room.store_name == store_name,
            Room.name == room_name
        )
    ).first()
    return room is not None

def check_customer_belongs_to_store(session: Session, customer_id: int, store_name: str) -> bool:
    link = session.exec(
        select(CustomerStoreLink).where(
            CustomerStoreLink.customer_id == customer_id,
            CustomerStoreLink.store_name == store_name
        )
    ).first()
    return link is not None

def get_active_store_name_list(session: Session) -> List[str]:
    """
    获取所有启用中的门店名称
    """
    store_objs = get_store_list(session)
    return [s.name for s in store_objs if getattr(s, "is_active", True)]


def get_customer_store_visit_count(
    session: Session,
    customer: Customer,
    store_name: str
) -> int:
    """
    统计某顾客在某门店的已组齐场次
    """
    stmt = select(func.count(GameRecord.id)).where(
        GameRecord.store_name == store_name,
        GameRecord.status == "formed",
        or_(
            GameRecord.player_1_wechat == customer.wechat_id,
            GameRecord.player_2_wechat == customer.wechat_id,
            GameRecord.player_3_wechat == customer.wechat_id,
            GameRecord.player_4_wechat == customer.wechat_id
        )
    )
    return int(session.exec(stmt).one() or 0)


def require_login(user: Optional[User]):
    if not user:
        raise HTTPException(status_code=401, detail="请先登录")


def require_admin(user: Optional[User]):
    if not user:
        raise HTTPException(status_code=401, detail="请先登录")
    if user.role != "admin":
        raise HTTPException(status_code=403, detail="无权限，仅超级管理员可操作")


def get_store_list(session: Session):
    """
    优先从 Store 表读取门店；若 Store 为空，则兼容从 Room.store_name 去重读取。
    """
    stores = session.exec(
        select(Store).order_by(Store.sort_order, Store.id)
    ).all()

    if stores:
        return stores

    all_rooms = session.exec(select(Room)).all()
    fallback_names = sorted(list(set([r.store_name for r in all_rooms if r.store_name])))
    return [
        Store(
            id=-idx - 1,
            name=name,
            short_name=None,
            is_active=True,
            sort_order=0
        )
        for idx, name in enumerate(fallback_names)
    ]


def get_active_room_list_by_store(session: Session, store_name: str) -> List[str]:
    """
    读取某门店下启用的包间名称列表。
    优先使用 store_id 关联；兼容旧数据 fallback 到 Room.store_name。
    返回值统一为 ['要春夏', '要秋冬', ...]，避免前端把整个 Room 对象渲染出来。
    """
    store_obj = session.exec(
        select(Store).where(Store.name == store_name)
    ).first()

    if store_obj:
        rooms = session.exec(
            select(Room).where(
                Room.store_id == store_obj.id,
                Room.is_active == True
            ).order_by(Room.sort_order, Room.id)
        ).all()

        if rooms:
            return [r.name for r in rooms if r.name]

    # 兼容旧逻辑
    rooms = session.exec(
        select(Room).where(
            Room.store_name == store_name
        ).order_by(Room.sort_order, Room.id)
    ).all()

    return [r.name for r in rooms if r.name]

    # 兼容旧逻辑
    return session.exec(
        select(Room).where(
            Room.store_name == store_name
        ).order_by(Room.sort_order, Room.id)
    ).all()


# ===================== 待办及信息同步 =====================

def get_store_list_for_page(session: Session) -> List[str]:
    """
    获取所有门店名称（去重后排序）
    """
    all_rooms = session.exec(select(Room)).all()
    return sorted(list(set([r.store_name for r in all_rooms])))


def get_room_list_by_store(session: Session, store_name: str) -> List[Room]:
    """
    获取某门店下的所有包间
    """
    return session.exec(
        select(Room).where(Room.store_name == store_name).order_by(Room.id)
    ).all()

def get_store_by_name(session: Session, store_name: str) -> Optional[Store]:
    return session.exec(
        select(Store).where(Store.name == store_name)
    ).first()


def get_customer_options_by_store(session: Session, store_name: str) -> List[dict]:
    """
    获取某门店下可选顾客列表，用于前端下拉框。
    返回格式：
    [
        {"id": 1, "nickname": "张三", "wechat_id": "abc"},
        ...
    ]
    """
    customer_ids = session.exec(
        select(CustomerStoreLink.customer_id).where(CustomerStoreLink.store_name == store_name)
    ).all()

    unique_ids = sorted(list(set(customer_ids)))
    if not unique_ids:
        return []

    customers = session.exec(
        select(Customer).where(Customer.id.in_(unique_ids)).order_by(Customer.id)
    ).all()

    return [
        {
            "id": c.id,
            "nickname": c.nickname,
            "wechat_id": c.wechat_id
        }
        for c in customers
    ]


def normalize_customer_ids_for_store(session: Session, store_name: str, customer_ids: Optional[List[int]]) -> List[int]:
    """
    规范化并校验“某门店下可关联的顾客ID列表”
    逻辑：
    1. 去重
    2. 过滤 None / 非法值
    3. 只保留属于当前门店的顾客
    """
    if not customer_ids:
        return []

    cleaned = []
    for cid in customer_ids:
        if cid is None:
            continue
        try:
            cleaned.append(int(cid))
        except Exception:
            continue

    cleaned = list(dict.fromkeys(cleaned))  # 去重且保序

    valid_customer_ids = set(session.exec(
        select(CustomerStoreLink.customer_id).where(CustomerStoreLink.store_name == store_name)
    ).all())

    return [cid for cid in cleaned if cid in valid_customer_ids]


def build_handover_stats(session: Session, store_name: str, start_date: date, end_date: date) -> dict:
    """
    构建顶部统计区数据：
    1. 未收金额总数 = room_fee - wechat_pay - Alipay（最小不低于0）
       这里只统计正常已组齐单，不统计溢出单
    2. 存储押金总数（当前门店关联顾客的全局押金之和）
    3. 未解决待办数
    4. 已置顶待办数
    """
    game_rows = session.exec(
        select(GameRecord).where(
            GameRecord.store_name == store_name,
            GameRecord.status == "formed",
            GameRecord.record_date >= start_date,
            GameRecord.record_date <= end_date,
            GameRecord.record_source != FORMED_SOURCE_OVERFLOW
        )
    ).all()

    unreceived_amount = 0.0
    for g in game_rows:
        left_amount = (g.room_fee or 0.0) - (g.wechat_pay or 0.0) - (g.Alipay or 0.0)
        unreceived_amount += max(left_amount, 0.0)

    store_customer_ids = session.exec(
        select(CustomerStoreLink.customer_id).where(CustomerStoreLink.store_name == store_name)
    ).all()
    store_customer_ids = sorted(list(set(store_customer_ids)))

    deposit_amount = 0.0
    if store_customer_ids:
        customers = session.exec(
            select(Customer).where(Customer.id.in_(store_customer_ids))
        ).all()
        deposit_amount = sum((c.guarantee_deposit or 0.0) for c in customers)

    unresolved_count = len(session.exec(
        select(HandoverTodo).where(
            HandoverTodo.store_name == store_name,
            HandoverTodo.status == "unresolved"
        )
    ).all())

    pinned_count = len(session.exec(
        select(HandoverTodo).where(
            HandoverTodo.store_name == store_name,
            HandoverTodo.status == "unresolved",
            HandoverTodo.is_pinned == True
        )
    ).all())

    return {
        "unreceived_amount": round(unreceived_amount, 2),
        "deposit_amount": round(deposit_amount, 2),
        "unresolved_count": unresolved_count,
        "pinned_count": pinned_count
    }


def build_handover_cards(session: Session, todos: List[HandoverTodo]) -> List[dict]:
    """
    把待办主表数据组装成前端展示卡片结构。
    包括：
    - 多顾客名称拼接
    - 时间格式化
    - 详情展开数据
    - 编辑模态框需要的数据
    - 去重兜底（防历史脏数据）
    """
    if not todos:
        return []

    todo_ids = [t.id for t in todos]

    # 1. 批量查关联顾客链接
    links = session.exec(
        select(HandoverTodoCustomerLink).where(HandoverTodoCustomerLink.todo_id.in_(todo_ids))
    ).all()

    # 2. 批量查顾客
    customer_ids = sorted(list(set([l.customer_id for l in links])))
    customer_map = {}
    if customer_ids:
        customer_rows = session.exec(
            select(Customer).where(Customer.id.in_(customer_ids))
        ).all()
        customer_map = {c.id: c for c in customer_rows}

    # 3. 构建 todo_id -> 顾客列表（去重）
    todo_customer_ids_map = {}
    todo_customer_names_map = {}
    todo_customer_detail_map = {}
    todo_customer_seen_map = {}

    for link in links:
        todo_customer_seen_map.setdefault(link.todo_id, set())
        if link.customer_id in todo_customer_seen_map[link.todo_id]:
            continue

        todo_customer_seen_map[link.todo_id].add(link.customer_id)
        todo_customer_ids_map.setdefault(link.todo_id, []).append(link.customer_id)

        cust = customer_map.get(link.customer_id)
        if cust:
            todo_customer_names_map.setdefault(link.todo_id, []).append(cust.nickname)
            todo_customer_detail_map.setdefault(link.todo_id, []).append({
                "id": cust.id,
                "nickname": cust.nickname or "",
                "wechat_id": cust.wechat_id or ""
            })

    # 4. 组装卡片
    cards = []
    for todo in todos:
        customer_ids_for_todo = todo_customer_ids_map.get(todo.id, [])
        customer_names = todo_customer_names_map.get(todo.id, [])

        if not customer_names:
            short_names = "未关联顾客"
            full_names = "未关联顾客"
        elif len(customer_names) <= 2:
            short_names = "、".join(customer_names)
            full_names = "、".join(customer_names)
        else:
            short_names = f"{customer_names[0]}、{customer_names[1]} 等{len(customer_names)}人"
            full_names = "、".join(customer_names)

        cards.append({
            "id": todo.id,
            "store_name": todo.store_name,
            "room_id": todo.room_id,
            "room_name": todo.room_name,
            "summary": todo.summary,
            "detail": todo.detail or "",
            "remark": todo.remark or "",
            "is_pinned": todo.is_pinned,
            "status": todo.status,
            "process_note": todo.process_note or "",
            "created_by_name": todo.created_by_name,
            "handled_by_name": todo.handled_by_name,
            "created_at_str": todo.created_at.strftime("%Y-%m-%d %H:%M") if todo.created_at else "",
            "updated_at_str": todo.updated_at.strftime("%Y-%m-%d %H:%M") if todo.updated_at else "",
            "resolved_at_str": todo.resolved_at.strftime("%Y-%m-%d %H:%M") if todo.resolved_at else "",
            "customer_ids": customer_ids_for_todo,
            "customer_names_short": short_names,
            "customer_names_full": full_names,
            "customers": todo_customer_detail_map.get(todo.id, [])
        })

    return cards


def handover_sort_key(todo: HandoverTodo):
    """
    列表排序规则：
    1. 已置顶 且 未解决
    2. 未置顶 且 未解决
    3. 已解决
    组内再按登记时间倒序
    """
    if todo.status == "unresolved" and todo.is_pinned:
        group = 0
    elif todo.status == "unresolved":
        group = 1
    else:
        group = 2

    ts = todo.created_at.timestamp() if todo.created_at else 0
    return (group, -ts)


def resolve_store_from_request(
    request: Request,
    session: Session,
    store: Optional[str] = None
) -> str:
    """
    门店继承规则：
    1. 优先使用当前请求显式传入的 store
    2. 若未传，则尝试从上一个页面 Referer 的 query 中继承 store
    3. 若仍无，则回退到第一个有效门店
    4. 若门店列表为空，再兜底为“牛王庙店”
    """
    store_list = get_store_list_for_page(session)

    # 1. 当前请求明确传了 store
    if store and store in store_list:
        return store

    # 2. 从 Referer 中继承
    referer = request.headers.get("referer", "")
    if referer:
        try:
            parsed = urlparse(referer)
            qs = parse_qs(parsed.query)
            referer_store = (qs.get("store") or [None])[0]
            if referer_store and referer_store in store_list:
                return referer_store
        except Exception:
            pass

    # 3. 回退到第一个门店
    if store_list:
        return store_list[0]

    # 4. 最终兜底
    return "牛王庙店"

HANDOVER_EMPTY_NOTE_SYSTEM_HINT = "【系统提示】该牌局当前已无参与人备注，请人工确认该同步事项是否仍需继续跟进。"

def get_game_noted_players_snapshot(session: Session, game: GameRecord) -> List[dict]:
    """
    提取当前牌局中“有备注的参与人”快照。
    仅统计 player_1_note ~ player_4_note 非空的参与人。

    返回格式：
    [
        {
            "slot": 1,
            "nickname": "张三",
            "wechat_id": "wx123",
            "note": "最近情绪不稳定",
            "customer_id": 12   # 若能匹配到顾客则有值，否则为 None
        },
        ...
    ]
    """
    result = []

    for idx in range(1, 5):
        nickname = _normalize_text(getattr(game, f"player_{idx}", None))
        wechat_id = _normalize_text(getattr(game, f"player_{idx}_wechat", None))
        note = _normalize_text(getattr(game, f"player_{idx}_note", None))

        if not note:
            continue

        customer_id = None
        if wechat_id:
            cust = session.exec(
                select(Customer).where(Customer.wechat_id == wechat_id)
            ).first()
            if cust:
                customer_id = cust.id

        result.append({
            "slot": idx,
            "nickname": nickname,
            "wechat_id": wechat_id,
            "note": note,
            "customer_id": customer_id
        })

    return result

def build_formed_game_handover_summary(game: GameRecord) -> str:
    """
    事件概述固定模板：
    已组齐牌局备注同步（时间+#月序号）

    时间优先取订单开始时间；没有则回退到预约时间展示。
    """
    time_text = ""

    if _normalize_text(game.order_start_time):
        time_text = _normalize_text(game.order_start_time)
    elif game.record_date:
        time_text = f"{game.record_date} {game.start_time or ''}".strip()
    else:
        time_text = game.start_time or ""

    return f"已组齐牌局备注同步（{time_text} #{game.serial_number}）"

def build_formed_game_handover_detail(game: GameRecord, noted_players: List[dict]) -> str:
    """
    自动拼接联动待办的详细说明。
    """
    lines = []

    lines.append("【来源】已组齐牌局参与人备注自动同步")
    lines.append(f"门店：{game.store_name or ''}")
    lines.append(f"牌局月序号：#{game.serial_number}")

    if _normalize_text(game.order_start_time):
        lines.append(f"订单开始时间：{_normalize_text(game.order_start_time)}")
    else:
        lines.append(f"预约时间：{game.record_date or ''} {game.start_time or ''}".strip())

    lines.append(f"包间：{game.room_name or '未填写'}")
    lines.append("")

    if noted_players:
        lines.append("【当前有备注的参与人】")
        for p in noted_players:
            nickname = p["nickname"] or "未填写昵称"
            wechat_id = p["wechat_id"] or "未填写微信号"
            note = p["note"] or ""
            lines.append(f"- 坑位{p['slot']}：{nickname}（{wechat_id}）")
            lines.append(f"  备注：{note}")
    else:
        lines.append("【当前有备注的参与人】")
        lines.append("- 当前无参与人备注")

    return "\n".join(lines).strip()


def strip_empty_note_system_hint(detail: Optional[str]) -> str:
    """
    去除“备注已清空”系统提示，避免重复追加。
    """
    raw = (detail or "").strip()
    if not raw:
        return ""

    lines = [line.rstrip() for line in raw.splitlines()]
    filtered = [line for line in lines if line.strip() != HANDOVER_EMPTY_NOTE_SYSTEM_HINT]
    return "\n".join(filtered).strip()


def handover_note_snapshot_changed(old_players: List[dict], new_players: List[dict]) -> bool:
    """
    判断“当前有备注参与人快照”是否变化。
    只要以下任一变化即视为变更：
    - 有备注的顾客变化
    - 备注文本变化
    - 坑位变化
    """
    def normalize(players: List[dict]):
        items = []
        for p in players:
            items.append((
                int(p.get("slot") or 0),
                _normalize_text(p.get("nickname")),
                _normalize_text(p.get("wechat_id")),
                _normalize_text(p.get("note")),
                int(p.get("customer_id") or 0)
            ))
        return sorted(items)

    return normalize(old_players) != normalize(new_players)


def get_game_noted_players_snapshot_from_raw(
    session: Session,
    player_data: List[dict]
) -> List[dict]:
    """
    根据原始参与人数据构造“有备注参与人快照”。
    player_data 示例：
    [
        {"slot":1, "nickname":"张三", "wechat_id":"wx", "note":"xxx"},
        ...
    ]
    """
    result = []
    for item in player_data:
        note = _normalize_text(item.get("note"))
        if not note:
            continue

        nickname = _normalize_text(item.get("nickname"))
        wechat_id = _normalize_text(item.get("wechat_id"))
        customer_id = None

        if wechat_id:
            cust = session.exec(
                select(Customer).where(Customer.wechat_id == wechat_id)
            ).first()
            if cust:
                customer_id = cust.id

        result.append({
            "slot": int(item.get("slot") or 0),
            "nickname": nickname,
            "wechat_id": wechat_id,
            "note": note,
            "customer_id": customer_id
        })

    return result


def sync_handover_todo_customer_links(
    session: Session,
    todo_id: int,
    customer_ids: List[int]
):
    """
    用最新顾客集合覆盖待办-顾客关联。
    """
    final_customer_ids = []
    seen = set()

    for cid in customer_ids:
        try:
            cid = int(cid)
        except Exception:
            continue
        if cid <= 0 or cid in seen:
            continue
        seen.add(cid)
        final_customer_ids.append(cid)

    session.exec(
        delete(HandoverTodoCustomerLink).where(HandoverTodoCustomerLink.todo_id == todo_id)
    )
    session.flush()

    for cid in final_customer_ids:
        session.add(HandoverTodoCustomerLink(todo_id=todo_id, customer_id=cid))


def sync_formed_game_note_to_handover(
    session: Session,
    game: GameRecord,
    operator: User,
    old_noted_players_snapshot: List[dict]
):
    """
    已组齐牌局备注 -> 待办联动核心逻辑

    规则：
    1. 只看 player_1_note ~ player_4_note
    2. 有备注：
       - 无关联待办则新建
       - 有关联待办则更新
    3. 备注全清空：
       - 若无关联待办，直接不处理
       - 若有待办且未解决，则保留并追加系统提示
    4. 若待办已解决，但备注内容变化，则自动改回未解决
    5. 不覆盖 process_note / remark / is_pinned
    """
    link = session.exec(
        select(FormedGameHandoverLink).where(FormedGameHandoverLink.game_id == game.id)
    ).first()

    new_noted_players = get_game_noted_players_snapshot(session, game)
    new_customer_ids = [p["customer_id"] for p in new_noted_players if p.get("customer_id")]

    summary = build_formed_game_handover_summary(game)
    detail = build_formed_game_handover_detail(game, new_noted_players)

    note_changed = handover_note_snapshot_changed(old_noted_players_snapshot, new_noted_players)

    # ========= A. 当前有备注 =========
    if new_noted_players:
        # 1) 无关联待办 -> 新建
        if not link:
            room_obj = None
            if game.room_name:
                room_obj = session.exec(
                    select(Room).where(
                        Room.store_name == game.store_name,
                        Room.name == game.room_name
                    )
                ).first()

            now = datetime.now()
            todo = HandoverTodo(
                store_name=game.store_name,
                room_id=room_obj.id if room_obj else None,
                room_name=game.room_name or None,
                summary=summary,
                detail=detail,
                remark=None,
                is_pinned=False,
                status="unresolved",
                process_note=None,
                created_by_user_id=operator.id,
                created_by_name=operator.display_name,
                handled_by_user_id=None,
                handled_by_name=None,
                created_at=now,
                updated_at=now,
                resolved_at=None
            )
            session.add(todo)
            session.flush()

            sync_handover_todo_customer_links(session, todo.id, new_customer_ids)

            session.add(FormedGameHandoverLink(
                game_id=game.id,
                todo_id=todo.id,
                created_at=now
            ))
            session.flush()
            return

        # 2) 已有关联待办 -> 更新
        todo = session.get(HandoverTodo, link.todo_id)
        if not todo:
            # 极端脏数据兜底：关联表在，但待办没了，则重建
            session.exec(
                delete(FormedGameHandoverLink).where(FormedGameHandoverLink.id == link.id)
            )
            session.flush()
            return sync_formed_game_note_to_handover(session, game, operator, old_noted_players_snapshot)

        room_obj = None
        if game.room_name:
            room_obj = session.exec(
                select(Room).where(
                    Room.store_name == game.store_name,
                    Room.name == game.room_name
                )
            ).first()

        old_summary = _normalize_text(todo.summary)

        todo.store_name = game.store_name
        todo.room_id = room_obj.id if room_obj else None
        todo.room_name = game.room_name or None
        todo.detail = detail
        todo.updated_at = datetime.now()

        # summary 默认不乱改；只有时间/月序号变化导致 summary 文本变化时才同步
        if old_summary != summary:
            todo.summary = summary

        # 已解决但备注发生变化 -> 自动 reopen
        if todo.status == "resolved" and note_changed:
            todo.status = "unresolved"
            todo.resolved_at = None
            todo.handled_by_user_id = operator.id
            todo.handled_by_name = operator.display_name

        session.add(todo)
        sync_handover_todo_customer_links(session, todo.id, new_customer_ids)
        session.flush()
        return

    # ========= B. 当前无备注 =========
    if not link:
        # 没有关联待办，则无事可做
        return

    todo = session.get(HandoverTodo, link.todo_id)
    if not todo:
        session.exec(
            delete(FormedGameHandoverLink).where(FormedGameHandoverLink.id == link.id)
        )
        session.flush()
        return

    clean_detail = strip_empty_note_system_hint(todo.detail)
    merged_detail = clean_detail

    if todo.status == "unresolved":
        if merged_detail:
            merged_detail = merged_detail + "\n\n" + HANDOVER_EMPTY_NOTE_SYSTEM_HINT
        else:
            merged_detail = HANDOVER_EMPTY_NOTE_SYSTEM_HINT

    todo.store_name = game.store_name
    todo.room_name = game.room_name or None
    todo.detail = merged_detail or None
    todo.updated_at = datetime.now()

    # 若时间/月序号变化，summary 仍允许同步
    if _normalize_text(todo.summary) != summary:
        todo.summary = summary

    # 若原来已解决，且备注状态发生变化（从有备注 -> 无备注），按规则 reopen
    if todo.status == "resolved" and note_changed:
        todo.status = "unresolved"
        todo.resolved_at = None
        todo.handled_by_user_id = operator.id
        todo.handled_by_name = operator.display_name

    session.add(todo)

    # 当前无备注 -> 顾客关联清空
    sync_handover_todo_customer_links(session, todo.id, [])
    session.flush()





# === 核心依赖：获取当前登录用户 ===
# 逻辑：从 Cookie 中读取 user_id，如果没读到或者用户不存在，就返回 None
async def get_current_user(
        request: Request,
        session: Session = Depends(get_session)
) -> Optional[User]:
    user_id = request.cookies.get("user_id")
    if not user_id:
        return None

    try:
        user_id_int = int(user_id)
    except Exception:
        return None

    user = session.get(User, user_id_int)
    if not user:
        return None

    # V3 员工管理：已停用账号视为未登录
    if not getattr(user, "is_active", True):
        return None

    return user

# 初始化数据库 (第一次运行时会自动建表)
# 初始化管理员
# 修改 startup 事件：增加初始化默认包间数据的逻辑
@app.on_event("startup")
def on_startup():
    create_db_and_tables()

    with Session(engine) as session:
        # 初始化默认门店/包间（仅当两张配置表都还是空时）
        existing_store = session.exec(select(Store)).first()
        existing_room = session.exec(select(Room)).first()

        if not existing_store and not existing_room:
            print("正在初始化默认门店和包间数据...")

            store_a = Store(name="牛王庙店", sort_order=1, is_active=True)

            session.add(store_a)
            session.commit()

            session.refresh(store_a)

            default_rooms = [
                Room(
                    name="耍春夏",
                    store_id=store_a.id,
                    store_name=store_a.name,
                    is_active=True,
                    sort_order=1
                ),
                Room(
                    name="耍秋冬",
                    store_id=store_a.id,
                    store_name=store_a.name,
                    is_active=True,
                    sort_order=2
                ),
            ]
            session.add_all(default_rooms)
            session.commit()

        # 初始化管理员账号
        existing_usernames = set(
            session.exec(
                select(User.username).where(User.username.in_(["13198550326", "18989218583"]))
            ).all()
        )

        users_to_add = []

        if "13198550326" not in existing_usernames:
            users_to_add.append(
                User(
                    username="13198550326",
                    hashed_password=get_password_hash("shuaipai882008"),
                    display_name="大总管",
                    role="admin"
                )
            )

        if "18989218583" not in existing_usernames:
            users_to_add.append(
                User(
                    username="18989218583",
                    hashed_password=get_password_hash("Jtf18989218583"),
                    display_name="耍牌最有法的男人·贾哥",
                    role="admin"
                )
            )

        if users_to_add:
            session.add_all(users_to_add)
            session.commit()


# === 1. 登录与注册页面接口 ===
@app.get("/login")
async def login_page(request: Request):
    return templates.TemplateResponse("login.html", {"request": request})


@app.get("/register")
async def register_page(request: Request):
    return templates.TemplateResponse("register.html", {"request": request})


# === 登录动作接口 ===
@app.post("/login")
async def login_action(
        response: Response,
        username: str = Form(...),
        password: str = Form(...),
        session: Session = Depends(get_session)
):
    username = (username or "").strip()

    user = session.exec(
        select(User).where(User.username == username)
    ).first()

    if not user or not verify_password(password, user.hashed_password):
        return RedirectResponse(
            url="/login?error=账号或密码错误，请重试",
            status_code=303
        )

    # V3 员工管理：停用员工不允许登录
    if not getattr(user, "is_active", True):
        return RedirectResponse(
            url="/login?error=该员工账号已停用，请联系管理员",
            status_code=303
        )

    response = RedirectResponse(url="/", status_code=303)
    response.set_cookie(
        key="user_id",
        value=str(user.id),
        max_age=60 * 60 * 24 * 7
    )
    return response


@app.post("/register")
async def register_action(
        username: str = Form(...),
        password: str = Form(...),
        display_name: str = Form(...),
        session: Session = Depends(get_session)
):
    # 检查账号是否已存在
    if session.exec(select(User).where(User.username == username)).first():
        return RedirectResponse(url="/register?error=该账号已存在，请换一个试试", status_code=303)

    new_user = User(
        username=username,
        hashed_password=get_password_hash(password),
        display_name=display_name,
        role="operator"  # 默认注册的都是普通员工
    )
    session.add(new_user)
    session.commit()
    return RedirectResponse(url="/login", status_code=303)


@app.get("/logout")
async def logout():
    response = RedirectResponse(url="/login", status_code=303)
    response.delete_cookie("user_id")
    return response

# =========================
# V3 员工管理页面
# =========================
@app.get("/employees")
async def employees_page(
        request: Request,
        store: str = "牛王庙店",
        tab: str = "",
        status_filter: str = "active",

        # 我的工资页使用：
        # 不传时默认查看当前月份；传入后可查看指定年月。
        salary_year: Optional[int] = None,
        salary_month: Optional[int] = None,

        # 工资结算页使用：
        # 不传时默认结算当前月份。
        settlement_year: Optional[int] = None,
        settlement_month: Optional[int] = None,

        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    V3 员工管理总入口。

    本接口负责：
    1. 员工管理内部页签；
    2. 员工列表；
    3. 我的请假；
    4. 管理员请假审批。

    注意：
    工资结算、考勤登记、激励白板等后续继续接入。
    """
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    # ===== 1. 门店列表：兼容 base.html 的 current_store / store_list =====
    store_objs = get_store_list(session)
    store_list = [s.name for s in store_objs if s.is_active]

    if store not in store_list and store_list:
        store = store_list[0]

    # ===== 2. 页签权限控制 =====
    admin_tabs = [
        "employee_list",
        "leave_approval",
        "attendance_manage",
        "salary_flows",
        "whiteboard",
        "salary_settlement",
        "team_assessment",
    ]

    employee_tabs = [
        "my_leave",
        "my_attendance",
        "whiteboard",
        "my_salary",

        # 普通员工也可以查看团队考核页，但前端只读，不展示任何操作按钮
        "team_assessment",
    ]

    if user.role == "admin":
        allowed_tabs = admin_tabs
        default_tab = "employee_list"
    else:
        allowed_tabs = employee_tabs
        default_tab = "my_salary"

    if tab not in allowed_tabs:
        tab = default_tab

    # ===== 3. 员工列表数据 =====
    all_employees = session.exec(
        select(User).order_by(User.is_active.desc(), User.role, User.id)
    ).all()

    active_employees = [u for u in all_employees if getattr(u, "is_active", True)]
    inactive_employees = [u for u in all_employees if not getattr(u, "is_active", True)]

    if status_filter == "inactive":
        employee_list = inactive_employees
    elif status_filter == "all":
        employee_list = all_employees
    else:
        status_filter = "active"
        employee_list = active_employees

    total_count = len(all_employees)
    active_count = len(active_employees)
    inactive_count = len(inactive_employees)
    admin_count = len([u for u in active_employees if u.role == "admin"])
    operator_count = len([u for u in active_employees if u.role != "admin"])

    # ===== 4. 请假数据：普通员工看自己的，管理员看全部 =====
    my_leave_requests = []
    leave_approval_requests = []
    pending_leave_count = 0

    # ===== 5. 考勤数据 =====
    attendance_records = []
    my_attendance_records = []

    # ===== 6. 工资调整流水数据 =====
    salary_flow_records = []

    # ===== 6.1 我的工资数据 =====
    my_salary_data = None

    # ===== 6.2 工资结算数据 =====
    salary_settlement_data = None

    # ===== 7. 激励白板数据 =====
    whiteboard_data = None

    # ===== 8. 团队管理与团队考核数据 =====
    team_management_data = None

    if tab == "my_leave":
        my_leave_requests = session.exec(
            select(EmployeeLeaveRequest).where(
                EmployeeLeaveRequest.user_id == user.id
            ).order_by(
                EmployeeLeaveRequest.leave_date.desc(),
                EmployeeLeaveRequest.id.desc()
            )
        ).all()

    if tab == "leave_approval" and user.role == "admin":
        leave_approval_requests = session.exec(
            select(EmployeeLeaveRequest).order_by(
                EmployeeLeaveRequest.status,
                EmployeeLeaveRequest.leave_date.desc(),
                EmployeeLeaveRequest.id.desc()
            )
        ).all()

    if user.role == "admin":
        pending_leave_count = len(session.exec(
            select(EmployeeLeaveRequest).where(
                EmployeeLeaveRequest.status == "pending"
            )
        ).all())
        # 管理员进入“考勤记录”页签时，查看全部员工考勤异常记录
        if tab == "attendance_manage":
            attendance_records = session.exec(
                select(EmployeeAttendanceRecord).order_by(
                    EmployeeAttendanceRecord.event_date.desc(),
                    EmployeeAttendanceRecord.id.desc()
                )
            ).all()

    # 普通员工进入“我的考勤”页签时，只查看自己的考勤记录
    if tab == "my_attendance":
        my_attendance_records = session.exec(
            select(EmployeeAttendanceRecord).where(
                EmployeeAttendanceRecord.user_id == user.id
            ).order_by(
                EmployeeAttendanceRecord.event_date.desc(),
                EmployeeAttendanceRecord.id.desc()
            )
        ).all()

    # 管理员进入“工资调整”页签时，查看管理员手工创建的工资流水
    if tab == "salary_flows" and user.role == "admin":
        salary_flow_records = session.exec(
            select(SalaryFlowRecord).where(
                SalaryFlowRecord.is_auto == False
            ).order_by(
                SalaryFlowRecord.flow_date.desc(),
                SalaryFlowRecord.id.desc()
            )
        ).all()

    # 普通员工进入“我的工资”页签时，查看自己的工资流水和月度结算状态。
    # 管理员如果后续也加入 my_salary 页签，这段同样可复用。
    if tab == "my_salary":
        today = date.today()

        selected_salary_year = salary_year or today.year
        selected_salary_month = salary_month or today.month

        # 月份参数兜底，避免 URL 手动传错导致页面异常。
        if selected_salary_month < 1 or selected_salary_month > 12:
            selected_salary_year = today.year
            selected_salary_month = today.month

        my_salary_data = _build_my_salary_data(
            session=session,
            user=user,
            year=selected_salary_year,
            month=selected_salary_month
        )

    # 管理员进入“工资结算”页签时，加载指定月份工资结算数据。
    if tab == "salary_settlement" and user.role == "admin":
        today = date.today()

        selected_settlement_year = settlement_year or today.year
        selected_settlement_month = settlement_month or today.month

        # 月份参数兜底，避免 URL 手动传错导致页面异常。
        if selected_settlement_month < 1 or selected_settlement_month > 12:
            selected_settlement_year = today.year
            selected_settlement_month = today.month

        salary_settlement_data = _build_salary_settlement_data(
            session=session,
            year=selected_settlement_year,
            month=selected_settlement_month
        )

    # 全员可见：进入“激励白板”页签时，构建本月激励数据
    if tab == "whiteboard":
        today = date.today()
        whiteboard_data = _build_employee_whiteboard_data(
            session=session,
            year=today.year,
            month=today.month
        )

    # 全员可见：
    # 管理员进入团队考核页时，可以查看 + 操作；
    # 普通员工进入团队考核页时，只读查看，不允许维护团队、成员、门店、扣分项、重新计算。
    if tab == "team_assessment":
        today = date.today()
        team_management_data = _build_team_management_data(
            session=session,
            year=today.year,
            month=today.month
        )

    tomorrow = date.today() + timedelta(days=1)

    return templates.TemplateResponse("employees.html", {
        "request": request,
        "page_name": "employees",
        "current_user": user,
        "current_store": store,
        "store_list": store_list,

        # 当前页签
        "active_tab": tab,
        "allowed_tabs": allowed_tabs,

        # 员工列表数据
        "employee_list": employee_list,
        "status_filter": status_filter,

        # 顶部统计数据
        "total_count": total_count,
        "active_count": active_count,
        "inactive_count": inactive_count,
        "admin_count": admin_count,
        "operator_count": operator_count,

        # 请假模块数据
        "my_leave_requests": my_leave_requests,
        "leave_approval_requests": leave_approval_requests,
        "pending_leave_count": pending_leave_count,
        "tomorrow_date": tomorrow,
        "shift_type_label": _shift_type_label,
        "leave_status_label": _leave_status_label,

        # 考勤模块数据
        "attendance_records": attendance_records,
        "my_attendance_records": my_attendance_records,
        "attendance_event_type_label": _attendance_event_type_label,

        # 管理员登记考勤时可选员工
        "active_employees": active_employees,
        "today_date": date.today(),

        # 工资调整模块数据
        "salary_flow_records": salary_flow_records,
        "salary_flow_category_label": _salary_flow_category_label,
        "salary_flow_type_label": _salary_flow_type_label,

        # 我的工资模块数据
        "my_salary_data": my_salary_data,
        "salary_settlement_status_label": _salary_settlement_status_label,

        # 工资结算模块数据
        "salary_settlement_data": salary_settlement_data,

        # 激励白板数据
        "whiteboard_data": whiteboard_data,

        # 团队管理与团队考核模块数据
        "team_management_data": team_management_data,
    })


# =========================
# V3 停用员工：软删除，不物理删除
# =========================
@app.post("/employees/delete/{employee_id}")
async def delete_employee(
        request: Request,
        employee_id: int,
        store: str = Form(""),
        status_filter: str = Form("active"),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    停用员工。

    兼容两种模式：
    1. 普通表单提交：RedirectResponse 整页返回；
    2. AJAX 提交：返回 JSON，前端只更新当前员工行，不刷新页面。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以停用员工", 403)
        return RedirectResponse(
            url=f"/employees?store={store}&tab=employee_list&status_filter={status_filter}&error=只有管理员可以停用员工",
            status_code=303
        )

    employee = session.get(User, employee_id)
    if not employee:
        if _is_ajax_request(request):
            return _employee_ajax_error("员工不存在", 404)
        return RedirectResponse(
            url=f"/employees?store={store}&tab=employee_list&status_filter={status_filter}&error=员工不存在",
            status_code=303
        )

    if not getattr(employee, "is_active", True):
        if _is_ajax_request(request):
            return _employee_ajax_error("该员工已经是停用状态")
        return RedirectResponse(
            url=f"/employees?store={store}&tab=employee_list&status_filter={status_filter}&error=该员工已经是停用状态",
            status_code=303
        )

    if employee.id == user.id:
        if _is_ajax_request(request):
            return _employee_ajax_error("不能停用当前登录账号")
        return RedirectResponse(
            url=f"/employees?store={store}&tab=employee_list&status_filter={status_filter}&error=不能停用当前登录账号",
            status_code=303
        )

    if employee.role == "admin":
        active_admin_count = len(session.exec(
            select(User).where(
                User.role == "admin",
                User.is_active == True
            )
        ).all())

        if active_admin_count <= 1:
            if _is_ajax_request(request):
                return _employee_ajax_error("不能停用最后一个管理员账号")
            return RedirectResponse(
                url=f"/employees?store={store}&tab=employee_list&status_filter={status_filter}&error=不能停用最后一个管理员账号",
                status_code=303
            )

    employee.is_active = False
    employee.deleted_at = datetime.now()

    session.add(employee)
    session.commit()
    session.refresh(employee)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="员工已停用，历史业绩和订单记录已保留",
            action="employee_disabled",
            payload={
                "employee": _employee_user_payload(employee, user),
                "counts": _employee_module_counts_payload(session)
            }
        )

    return RedirectResponse(
        url=f"/employees?store={store}&tab=employee_list&status_filter=inactive&success=员工已停用，历史业绩和订单记录已保留",
        status_code=303
    )


# =========================
# V3 恢复员工
# =========================
@app.post("/employees/restore/{employee_id}")
async def restore_employee(
        request: Request,
        employee_id: int,
        store: str = Form(""),
        status_filter: str = Form("inactive"),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    恢复员工。

    兼容：
    1. 普通表单提交；
    2. AJAX 局部刷新当前员工行。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以恢复员工", 403)
        return RedirectResponse(
            url=f"/employees?store={store}&tab=employee_list&status_filter={status_filter}&error=只有管理员可以恢复员工",
            status_code=303
        )

    employee = session.get(User, employee_id)
    if not employee:
        if _is_ajax_request(request):
            return _employee_ajax_error("员工不存在", 404)
        return RedirectResponse(
            url=f"/employees?store={store}&tab=employee_list&status_filter={status_filter}&error=员工不存在",
            status_code=303
        )

    if getattr(employee, "is_active", True):
        if _is_ajax_request(request):
            return _employee_ajax_error("该员工当前已经是在职状态")
        return RedirectResponse(
            url=f"/employees?store={store}&tab=employee_list&status_filter={status_filter}&error=该员工当前已经是在职状态",
            status_code=303
        )

    employee.is_active = True
    employee.deleted_at = None

    session.add(employee)
    session.commit()
    session.refresh(employee)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="员工已恢复",
            action="employee_restored",
            payload={
                "employee": _employee_user_payload(employee, user),
                "counts": _employee_module_counts_payload(session)
            }
        )

    return RedirectResponse(
        url=f"/employees?store={store}&tab=employee_list&status_filter=active&success=员工已恢复",
        status_code=303
    )

# =========================
# V3 员工请假：提交申请
# =========================
@app.post("/employees/leaves/apply")
async def employee_leave_apply(
        request: Request,
        store: str = Form(""),
        leave_date: str = Form(...),
        reason: str = Form(...),
        remark: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    普通员工提交请假申请。

    AJAX 模式：
    成功后返回新建的请假申请数据，前端只在“我的请假”表格里新增一行。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    try:
        leave_d = datetime.strptime(leave_date, "%Y-%m-%d").date()
    except Exception:
        if _is_ajax_request(request):
            return _employee_ajax_error("请假日期格式不正确")
        return RedirectResponse(
            url=_build_employees_url(store, "my_leave", error="请假日期格式不正确"),
            status_code=303
        )

    today = date.today()

    if leave_d <= today:
        if _is_ajax_request(request):
            return _employee_ajax_error("当天无法请假，请至少提前一天提交请假申请")
        return RedirectResponse(
            url=_build_employees_url(store, "my_leave", error="当天无法请假，请至少提前一天提交请假申请"),
            status_code=303
        )

    reason = _normalize_text(reason)
    remark = _normalize_text(remark)

    if not reason:
        if _is_ajax_request(request):
            return _employee_ajax_error("请假原因不能为空")
        return RedirectResponse(
            url=_build_employees_url(store, "my_leave", error="请假原因不能为空"),
            status_code=303
        )

    existing = session.exec(
        select(EmployeeLeaveRequest).where(
            EmployeeLeaveRequest.user_id == user.id,
            EmployeeLeaveRequest.leave_date == leave_d,
            EmployeeLeaveRequest.status.in_(["pending", "approved"])
        )
    ).first()

    if existing:
        if _is_ajax_request(request):
            return _employee_ajax_error("该日期已有待审批或已通过的请假申请，请勿重复提交")
        return RedirectResponse(
            url=_build_employees_url(store, "my_leave", error="该日期已有待审批或已通过的请假申请，请勿重复提交"),
            status_code=303
        )

    shift_type = _get_shift_type_for_employee_on_date(
        session=session,
        employee_name=user.display_name,
        work_date=leave_d
    )

    estimated_deduct = _calc_leave_deduct_amount(
        session=session,
        user_id=user.id,
        employee_name=user.display_name,
        shift_type=shift_type
    )

    now = datetime.now()

    leave_req = EmployeeLeaveRequest(
        user_id=user.id,
        employee_name_snapshot=user.display_name,
        leave_date=leave_d,
        apply_date=today,
        shift_type=shift_type,
        reason=reason,
        remark=remark or None,

        status="pending",
        is_before_one_day=True,
        estimated_deduct_amount=estimated_deduct,
        final_deduct_amount=0.0,

        approved_by_user_id=None,
        approved_by_name=None,
        approved_at=None,
        approval_note=None,

        attendance_record_id=None,
        salary_flow_id=None,

        created_at=now,
        updated_at=now
    )

    session.add(leave_req)
    session.commit()
    session.refresh(leave_req)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="请假申请已提交，等待管理员审批",
            action="leave_created",
            payload={
                "leave": _leave_request_payload(leave_req)
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "my_leave", success="请假申请已提交，等待管理员审批"),
        status_code=303
    )

# =========================
# V3 员工请假：管理员审批通过
# =========================
@app.post("/employees/leaves/approve/{leave_id}")
async def employee_leave_approve(
        request: Request,
        leave_id: int,
        store: str = Form(""),
        approval_note: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    管理员审批通过请假申请。

    AJAX 模式：
    成功后返回更新后的请假申请数据，前端只更新当前审批行。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以审批请假", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "my_leave", error="只有管理员可以审批请假"),
            status_code=303
        )

    leave_req = session.get(EmployeeLeaveRequest, leave_id)
    if not leave_req:
        if _is_ajax_request(request):
            return _employee_ajax_error("请假申请不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "leave_approval", error="请假申请不存在"),
            status_code=303
        )

    if leave_req.status != "pending":
        if _is_ajax_request(request):
            return _employee_ajax_error("该请假申请已处理，请勿重复审批")
        return RedirectResponse(
            url=_build_employees_url(store, "leave_approval", error="该请假申请已处理，请勿重复审批"),
            status_code=303
        )

    applicant = session.get(User, leave_req.user_id)
    if not applicant:
        if _is_ajax_request(request):
            return _employee_ajax_error("请假员工账号不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "leave_approval", error="请假员工账号不存在"),
            status_code=303
        )

    shift_type = _get_shift_type_for_employee_on_date(
        session=session,
        employee_name=leave_req.employee_name_snapshot,
        work_date=leave_req.leave_date
    )

    final_deduct = _calc_leave_deduct_amount(
        session=session,
        user_id=leave_req.user_id,
        employee_name=leave_req.employee_name_snapshot,
        shift_type=shift_type
    )

    now = datetime.now()
    approval_note = _normalize_text(approval_note)

    leave_req.status = "approved"
    leave_req.shift_type = shift_type
    leave_req.final_deduct_amount = final_deduct
    leave_req.approved_by_user_id = user.id
    leave_req.approved_by_name = user.display_name
    leave_req.approved_at = now
    leave_req.approval_note = approval_note or None
    leave_req.updated_at = now

    session.add(leave_req)
    session.flush()

    attendance = EmployeeAttendanceRecord(
        user_id=leave_req.user_id,
        employee_name_snapshot=leave_req.employee_name_snapshot,
        event_date=leave_req.leave_date,
        event_type="leave",
        shift_type=shift_type,
        reason=leave_req.reason,
        status="approved",
        affect_full_attendance=False,
        deduct_amount=final_deduct,
        is_salary_generated=False,
        salary_flow_id=None,
        leave_request_id=leave_req.id,

        created_by_user_id=user.id,
        created_by_name=user.display_name,
        approved_by_user_id=user.id,
        approved_by_name=user.display_name,
        approved_at=now,
        approval_note=approval_note or None,

        created_at=now,
        updated_at=now
    )

    session.add(attendance)
    session.flush()

    salary_flow = SalaryFlowRecord(
        user_id=leave_req.user_id,
        employee_name_snapshot=leave_req.employee_name_snapshot,
        salary_year=leave_req.leave_date.year,
        salary_month=leave_req.leave_date.month,
        flow_date=leave_req.leave_date,

        flow_category="attendance",
        flow_type="leave_deduct",

        amount=round(-final_deduct, 2),

        title="请假扣款" if final_deduct > 0 else "请假记录（休息日不扣款）",
        description=(
            f"{leave_req.employee_name_snapshot} 请假，"
            f"日期：{leave_req.leave_date}，"
            f"班次：{_shift_type_label(shift_type)}，"
            f"扣款：{final_deduct:.2f} 元。"
            f"审批通过请假不影响全勤奖。"
        ),

        source_type="leave_request",
        source_id=leave_req.id,

        is_auto=True,
        is_locked=False,
        is_visible_to_employee=True,

        created_by_user_id=user.id,
        created_by_name=user.display_name,

        created_at=now,
        updated_at=now
    )

    session.add(salary_flow)
    session.flush()

    attendance.is_salary_generated = True
    attendance.salary_flow_id = salary_flow.id

    leave_req.attendance_record_id = attendance.id
    leave_req.salary_flow_id = salary_flow.id

    session.add(attendance)
    session.add(leave_req)
    session.commit()
    session.refresh(leave_req)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="请假申请已通过，并已生成考勤记录和工资流水",
            action="leave_approved",
            payload={
                "leave": _leave_request_payload(leave_req)
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "leave_approval", success="请假申请已通过，并已生成考勤记录和工资流水"),
        status_code=303
    )

# =========================
# V3 员工请假：管理员拒绝
# =========================
@app.post("/employees/leaves/reject/{leave_id}")
async def employee_leave_reject(
        request: Request,
        leave_id: int,
        store: str = Form(""),
        approval_note: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    管理员拒绝请假申请。

    AJAX 模式：
    成功后返回更新后的请假申请数据，前端只更新当前审批行。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以审批请假", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "my_leave", error="只有管理员可以审批请假"),
            status_code=303
        )

    leave_req = session.get(EmployeeLeaveRequest, leave_id)
    if not leave_req:
        if _is_ajax_request(request):
            return _employee_ajax_error("请假申请不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "leave_approval", error="请假申请不存在"),
            status_code=303
        )

    if leave_req.status != "pending":
        if _is_ajax_request(request):
            return _employee_ajax_error("该请假申请已处理，请勿重复审批")
        return RedirectResponse(
            url=_build_employees_url(store, "leave_approval", error="该请假申请已处理，请勿重复审批"),
            status_code=303
        )

    now = datetime.now()
    approval_note = _normalize_text(approval_note)

    leave_req.status = "rejected"
    leave_req.approved_by_user_id = user.id
    leave_req.approved_by_name = user.display_name
    leave_req.approved_at = now
    leave_req.approval_note = approval_note or None
    leave_req.updated_at = now

    session.add(leave_req)
    session.commit()
    session.refresh(leave_req)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="请假申请已拒绝",
            action="leave_rejected",
            payload={
                "leave": _leave_request_payload(leave_req)
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "leave_approval", success="请假申请已拒绝"),
        status_code=303
    )

# =========================
# V3 员工考勤：管理员登记迟到 / 旷工 / 其他考勤异常
# =========================
@app.post("/employees/attendance/add")
async def employee_attendance_add(
        request: Request,
        store: str = Form(""),
        user_id: int = Form(...),
        event_date: str = Form(...),
        event_type: str = Form(...),
        reason: str = Form(...),
        deduct_amount: float = Form(0),
        affect_full_attendance: Optional[str] = Form(None),
        remark: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    管理员登记考勤异常。

    支持类型：
    - late：迟到，必然影响全勤；
    - absent：旷工，必然影响全勤；
    - other：其他考勤异常，由管理员自行填写原因，可选择是否影响全勤。

    注意：
    工作失误不属于考勤异常，不在这里登记。
    工作失误造成的扣款，后续应放入“工资调整流水”。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以登记考勤异常", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "attendance_manage", error="只有管理员可以登记考勤异常"),
            status_code=303
        )

    target_user = session.get(User, user_id)
    if not target_user:
        if _is_ajax_request(request):
            return _employee_ajax_error("员工不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "attendance_manage", error="员工不存在"),
            status_code=303
        )

    if not getattr(target_user, "is_active", True):
        if _is_ajax_request(request):
            return _employee_ajax_error("该员工已停用，不能新增考勤异常")
        return RedirectResponse(
            url=_build_employees_url(store, "attendance_manage", error="该员工已停用，不能新增考勤异常"),
            status_code=303
        )

    event_type = _normalize_text(event_type)

    # 工作失误不再属于考勤异常
    allowed_event_types = {"late", "absent", "other"}

    if event_type not in allowed_event_types:
        if _is_ajax_request(request):
            return _employee_ajax_error("考勤类型不正确")
        return RedirectResponse(
            url=_build_employees_url(store, "attendance_manage", error="考勤类型不正确"),
            status_code=303
        )

    try:
        event_d = datetime.strptime(event_date, "%Y-%m-%d").date()
    except Exception:
        if _is_ajax_request(request):
            return _employee_ajax_error("日期格式不正确")
        return RedirectResponse(
            url=_build_employees_url(store, "attendance_manage", error="日期格式不正确"),
            status_code=303
        )

    reason = _normalize_text(reason)
    remark = _normalize_text(remark)

    if not reason:
        if _is_ajax_request(request):
            return _employee_ajax_error("原因不能为空")
        return RedirectResponse(
            url=_build_employees_url(store, "attendance_manage", error="原因不能为空"),
            status_code=303
        )

    deduct_amount = round(_safe_float(deduct_amount), 2)
    if deduct_amount < 0:
        if _is_ajax_request(request):
            return _employee_ajax_error("扣款金额不能为负数")
        return RedirectResponse(
            url=_build_employees_url(store, "attendance_manage", error="扣款金额不能为负数"),
            status_code=303
        )

    shift_type = _get_shift_type_for_employee_on_date(
        session=session,
        employee_name=target_user.display_name,
        work_date=event_d
    )

    now = datetime.now()
    event_label = _attendance_event_type_label(event_type)

    # 迟到、旷工固定影响全勤；其他由管理员选择
    if event_type in {"late", "absent"}:
        final_affect_full_attendance = True
    else:
        final_affect_full_attendance = bool(affect_full_attendance)

    # 1. 生成考勤记录
    attendance = EmployeeAttendanceRecord(
        user_id=target_user.id,
        employee_name_snapshot=target_user.display_name,
        event_date=event_d,
        event_type=event_type,
        shift_type=shift_type,
        reason=reason,
        remark=remark or None,
        status="recorded",

        affect_full_attendance=final_affect_full_attendance,

        # 考勤表中正数存扣款金额；工资流水中用负数表示扣款
        deduct_amount=deduct_amount,

        is_salary_generated=False,
        salary_flow_id=None,
        leave_request_id=None,

        created_by_user_id=user.id,
        created_by_name=user.display_name,

        approved_by_user_id=None,
        approved_by_name=None,
        approved_at=None,
        approval_note=None,

        created_at=now,
        updated_at=now
    )

    session.add(attendance)
    session.flush()

    # 2. 有扣款金额时，生成工资流水
    if deduct_amount > 0:
        flow_type_map = {
            "late": "late_deduct",
            "absent": "absent_deduct",
            "other": "other_attendance_deduct",
        }

        salary_flow = SalaryFlowRecord(
            user_id=target_user.id,
            employee_name_snapshot=target_user.display_name,
            salary_year=event_d.year,
            salary_month=event_d.month,
            flow_date=event_d,

            flow_category="attendance",
            flow_type=flow_type_map.get(event_type, "other_attendance_deduct"),

            amount=round(-deduct_amount, 2),

            title=f"{event_label}扣款",
            description=(
                f"{target_user.display_name}因{reason}扣款{deduct_amount:.2f}元；"
                f"{'该记录影响全勤奖。' if final_affect_full_attendance else '该记录不影响全勤奖。'}"
            ),

            source_type="attendance_record",
            source_id=attendance.id,

            is_auto=True,
            is_locked=False,
            is_visible_to_employee=True,

            created_by_user_id=user.id,
            created_by_name=user.display_name,

            created_at=now,
            updated_at=now
        )

        session.add(salary_flow)
        session.flush()

        attendance.is_salary_generated = True
        attendance.salary_flow_id = salary_flow.id

        session.add(attendance)

        # 3. 生成员工通知
        _create_employee_notification_for_attendance(
            session=session,
            attendance=attendance,
            operator=user
        )

    session.commit()
    session.refresh(attendance)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message=f"{event_label}记录已登记",
            action="attendance_created",
            payload={
                "attendance": _attendance_record_payload(attendance)
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "attendance_manage", success=f"{event_label}记录已登记"),
        status_code=303
    )

# =========================
# V3 员工考勤：管理员删除考勤异常记录
# =========================
@app.post("/employees/attendance/delete/{attendance_id}")
async def employee_attendance_delete(
        request: Request,
        attendance_id: int,
        store: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    管理员删除考勤异常记录。

    删除规则：
    1. 只有管理员可以删除；
    2. 删除考勤记录时，如果它已经生成工资流水，则同步删除对应 SalaryFlowRecord；
    3. 如果对应工资流水已经锁定，则禁止删除，避免破坏已结算工资；
    4. 删除该考勤记录产生的员工通知，避免员工后续继续收到无效通知；
    5. AJAX 请求返回 JSON，前端只移除当前考勤记录行，不刷新整个页面。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以删除考勤记录", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "attendance_manage", error="只有管理员可以删除考勤记录"),
            status_code=303
        )

    attendance = session.get(EmployeeAttendanceRecord, attendance_id)
    if not attendance:
        if _is_ajax_request(request):
            return _employee_ajax_error("考勤记录不存在或已被删除", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "attendance_manage", error="考勤记录不存在或已被删除"),
            status_code=303
        )

    # ===== 1. 检查并删除关联工资流水 =====
    # 说明：
    # 如果工资流水已锁定，说明可能已经进入工资结算，不允许直接删除源考勤记录。
    related_salary_flows = []

    if getattr(attendance, "salary_flow_id", None):
        sf = session.get(SalaryFlowRecord, attendance.salary_flow_id)
        if sf:
            related_salary_flows.append(sf)

    # 兜底：即使 salary_flow_id 没有回填，也按 source_type/source_id 查一次。
    fallback_flows = session.exec(
        select(SalaryFlowRecord).where(
            SalaryFlowRecord.source_type == "attendance_record",
            SalaryFlowRecord.source_id == attendance.id
        )
    ).all()

    for sf in fallback_flows:
        if sf not in related_salary_flows:
            related_salary_flows.append(sf)

    for sf in related_salary_flows:
        if getattr(sf, "is_locked", False):
            if _is_ajax_request(request):
                return _employee_ajax_error("该考勤记录关联的工资流水已锁定，不能删除")
            return RedirectResponse(
                url=_build_employees_url(store, "attendance_manage", error="该考勤记录关联的工资流水已锁定，不能删除"),
                status_code=303
            )

    # ===== 2. 删除关联通知 =====
    # 说明：
    # 管理员新增迟到/旷工等记录时，会给其他员工生成通知。
    # 删除考勤记录后，这些通知也应同步清理。
    session.exec(
        delete(EmployeeNotification).where(
            EmployeeNotification.source_type == "attendance_record",
            EmployeeNotification.source_id == attendance.id
        )
    )

    # ===== 3. 删除关联工资流水 =====
    for sf in related_salary_flows:
        session.delete(sf)

    # ===== 4. 删除考勤记录本身 =====
    deleted_id = attendance.id
    session.delete(attendance)
    session.commit()

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="考勤记录已删除，关联工资流水和通知已同步清理",
            action="attendance_deleted",
            payload={
                "attendance_id": deleted_id
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "attendance_manage", success="考勤记录已删除，关联工资流水和通知已同步清理"),
        status_code=303
    )

# =========================
# V3 员工工资：管理员新增工资调整流水
# =========================
@app.post("/employees/salary-flows/add")
async def employee_salary_flow_add(
        request: Request,
        store: str = Form(""),
        user_id: int = Form(...),
        flow_date: str = Form(...),
        flow_type: str = Form(...),
        amount_action: str = Form(...),
        amount: float = Form(...),
        title: str = Form(""),
        description: str = Form(""),
        is_visible_to_employee: Optional[str] = Form(None),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    管理员新增工资调整流水。

    业务口径：
    1. 这里处理“非自动计算”的工资变化；
    2. 工作失误扣款放在这里，不进入考勤记录，不影响全勤；
    3. 正数表示加钱，负数表示扣钱；
    4. 本接口兼容普通表单和 AJAX；
    5. AJAX 成功后，前端只在工资流水表格顶部新增一行，不刷新整页。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以新增工资调整", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_flows", error="只有管理员可以新增工资调整"),
            status_code=303
        )

    target_user = session.get(User, user_id)
    if not target_user:
        if _is_ajax_request(request):
            return _employee_ajax_error("员工不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_flows", error="员工不存在"),
            status_code=303
        )

    if not getattr(target_user, "is_active", True):
        if _is_ajax_request(request):
            return _employee_ajax_error("该员工已停用，不能新增工资调整")
        return RedirectResponse(
            url=_build_employees_url(store, "salary_flows", error="该员工已停用，不能新增工资调整"),
            status_code=303
        )

    try:
        flow_d = datetime.strptime(flow_date, "%Y-%m-%d").date()
    except Exception:
        if _is_ajax_request(request):
            return _employee_ajax_error("日期格式不正确")
        return RedirectResponse(
            url=_build_employees_url(store, "salary_flows", error="日期格式不正确"),
            status_code=303
        )

    flow_type = _normalize_text(flow_type)
    amount_action = _normalize_text(amount_action)
    title = _normalize_text(title)
    description = _normalize_text(description)

    allowed_flow_types = {
        "mistake_deduct",
        "replacement_pay",
        "overtime_pay",
        "manual_bonus",
        "manual_deduct",
        "manual_correction",
        "other_adjustment",
    }

    if flow_type not in allowed_flow_types:
        if _is_ajax_request(request):
            return _employee_ajax_error("工资调整类型不正确")
        return RedirectResponse(
            url=_build_employees_url(store, "salary_flows", error="工资调整类型不正确"),
            status_code=303
        )

    amount_value = round(abs(_safe_float(amount)), 2)
    if amount_value <= 0:
        if _is_ajax_request(request):
            return _employee_ajax_error("金额必须大于 0")
        return RedirectResponse(
            url=_build_employees_url(store, "salary_flows", error="金额必须大于 0"),
            status_code=303
        )

    if amount_action not in {"add", "deduct"}:
        if _is_ajax_request(request):
            return _employee_ajax_error("金额方向不正确")
        return RedirectResponse(
            url=_build_employees_url(store, "salary_flows", error="金额方向不正确"),
            status_code=303
        )

    # ===== 金额方向 =====
    # add    = 加钱，金额为正
    # deduct = 扣钱，金额为负
    signed_amount = amount_value if amount_action == "add" else -amount_value

    # ===== 根据类型兜底判断金额方向 =====
    # 这些类型原则上应为扣款，如果前端误传 add，这里仍强制转成负数。
    if flow_type in {"mistake_deduct", "manual_deduct"}:
        signed_amount = -amount_value

    # 这些类型原则上应为加钱，如果前端误传 deduct，这里仍强制转成正数。
    if flow_type in {"replacement_pay", "overtime_pay", "manual_bonus"}:
        signed_amount = amount_value

    # ===== 自动归类 =====
    if flow_type in {"replacement_pay", "overtime_pay"}:
        flow_category = "replacement_work"
    elif flow_type in {"mistake_deduct", "manual_deduct"}:
        flow_category = "deduction"
    elif flow_type == "manual_bonus":
        flow_category = "bonus"
    else:
        flow_category = "manual_adjustment"

    flow_type_label = _salary_flow_type_label(flow_type)

    if not title:
        title = flow_type_label

    if not description:
        description = f"{target_user.display_name}：{title}，金额 {signed_amount:.2f} 元。"

    now = datetime.now()

    salary_flow = SalaryFlowRecord(
        user_id=target_user.id,
        employee_name_snapshot=target_user.display_name,

        salary_year=flow_d.year,
        salary_month=flow_d.month,
        flow_date=flow_d,

        flow_category=flow_category,
        flow_type=flow_type,

        amount=round(signed_amount, 2),

        title=title,
        description=description,

        # 手工工资调整没有业务来源表，统一标记 manual
        source_type="manual",
        source_id=None,

        is_auto=False,
        is_locked=False,
        is_visible_to_employee=bool(is_visible_to_employee),

        created_by_user_id=user.id,
        created_by_name=user.display_name,

        created_at=now,
        updated_at=now
    )

    session.add(salary_flow)
    session.commit()
    session.refresh(salary_flow)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="工资调整流水已新增",
            action="salary_flow_created",
            payload={
                "salary_flow": _salary_flow_payload(salary_flow)
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "salary_flows", success="工资调整流水已新增"),
        status_code=303
    )

# =========================
# V3 员工工资：管理员删除工资调整流水
# =========================
@app.post("/employees/salary-flows/delete/{flow_id}")
async def employee_salary_flow_delete(
        request: Request,
        flow_id: int,
        store: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    管理员删除工资调整流水。

    删除规则：
    1. 只有管理员可以删除；
    2. 只允许删除手工流水 is_auto=False；
    3. 已锁定流水不能删除；
    4. 自动流水，例如请假扣款、迟到扣款，不在这里删除；
       自动流水应从源记录处删除，例如删除考勤记录会同步删除对应工资流水；
    5. AJAX 成功后，前端只删除当前工资流水行。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以删除工资调整", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_flows", error="只有管理员可以删除工资调整"),
            status_code=303
        )

    salary_flow = session.get(SalaryFlowRecord, flow_id)
    if not salary_flow:
        if _is_ajax_request(request):
            return _employee_ajax_error("工资流水不存在或已被删除", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_flows", error="工资流水不存在或已被删除"),
            status_code=303
        )

    if getattr(salary_flow, "is_auto", False):
        if _is_ajax_request(request):
            return _employee_ajax_error("自动生成的工资流水不能在这里删除，请从来源记录处理")
        return RedirectResponse(
            url=_build_employees_url(store, "salary_flows", error="自动生成的工资流水不能在这里删除，请从来源记录处理"),
            status_code=303
        )

    if getattr(salary_flow, "is_locked", False):
        if _is_ajax_request(request):
            return _employee_ajax_error("该工资流水已锁定，不能删除")
        return RedirectResponse(
            url=_build_employees_url(store, "salary_flows", error="该工资流水已锁定，不能删除"),
            status_code=303
        )

    deleted_id = salary_flow.id
    session.delete(salary_flow)
    session.commit()

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="工资调整流水已删除",
            action="salary_flow_deleted",
            payload={
                "salary_flow_id": deleted_id
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "salary_flows", success="工资调整流水已删除"),
        status_code=303
    )

# =========================
# V3 工资结算：生成 / 重算全员工资
# =========================
@app.post("/employees/salary-settlement/generate-all")
async def employee_salary_settlement_generate_all(
        request: Request,
        store: str = Form(""),
        salary_year: int = Form(...),
        salary_month: int = Form(...),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    管理员生成 / 重算某月全员工资。

    生成内容：
    1. 基础工资；
    2. 个人订单提成；
    3. 团队奖金；
    4. 全勤奖；
    5. 销冠奖；
    6. 汇总已有请假扣款、迟到扣款、旷工扣款、工资调整等流水；
    7. 写入 MonthlySalarySettlement。

    注意：
    paid / locked 状态的工资不能重算。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以生成工资结算", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="只有管理员可以生成工资结算"),
            status_code=303
        )

    if salary_month < 1 or salary_month > 12:
        if _is_ajax_request(request):
            return _employee_ajax_error("月份不正确")
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="月份不正确"),
            status_code=303
        )

    active_users = session.exec(
        select(User).where(User.is_active == True).order_by(User.role, User.id)
    ).all()

    all_order_count_map = _build_employee_order_count_map(
        session=session,
        year=salary_year,
        month=salary_month
    )

    updated_rows = []

    try:
        for emp in active_users:
            # ===== 生成 / 重算规则 =====
            # 1. 没有结算记录：生成；
            # 2. 草稿：允许重算；
            # 3. 已确认：跳过，必须先退回草稿才能重算；
            # 4. 已发放并锁定：跳过，历史归档不可重算。
            existing_settlement = session.exec(
                select(MonthlySalarySettlement).where(
                    MonthlySalarySettlement.user_id == emp.id,
                    MonthlySalarySettlement.salary_year == salary_year,
                    MonthlySalarySettlement.salary_month == salary_month
                )
            ).first()

            if existing_settlement and existing_settlement.status in {"confirmed", "paid", "locked"}:
                updated_rows.append(_salary_settlement_payload(existing_settlement))
                continue

            settlement = _calculate_salary_for_one_employee(
                session=session,
                user_obj=emp,
                year=salary_year,
                month=salary_month,
                operator=user,
                all_order_count_map=all_order_count_map
            )
            updated_rows.append(_salary_settlement_payload(settlement))

        session.commit()

    except ValueError as e:
        session.rollback()
        if _is_ajax_request(request):
            return _employee_ajax_error(str(e))
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error=str(e)),
            status_code=303
        )

    except Exception as e:
        session.rollback()
        if _is_ajax_request(request):
            return _employee_ajax_error(f"生成工资结算失败：{e}", 500)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="生成工资结算失败"),
            status_code=303
        )

    if _is_ajax_request(request):
        # 重新查询一次页面概览数据。
        # 注意：_build_salary_settlement_data() 返回的数据包含 User / Settlement ORM 对象，
        # 不能直接塞进 JSONResponse，所以这里再转成纯 dict。
        summary_data = _build_salary_settlement_data(
            session=session,
            year=salary_year,
            month=salary_month
        )

        return _employee_ajax_success(
            message="本月全员工资结算已生成",
            action="salary_settlement_generated_all",
            payload={
                # rows 已经由 _salary_settlement_payload() 转成纯 dict，可以直接返回
                "rows": updated_rows,

                # summary 必须返回纯数字/字符串，不能包含 User 等 ORM 对象
                "summary": _salary_settlement_summary_payload(summary_data)
            }
        )

    return RedirectResponse(
        url=f"/employees?store={store}&tab=salary_settlement&settlement_year={salary_year}&settlement_month={salary_month}&success=本月全员工资结算已生成",
        status_code=303
    )


# =========================
# V3 工资结算：更新社保扣款
# =========================
@app.post("/employees/salary-settlement/social-security/{settlement_id}")
async def employee_salary_settlement_social_security_update(
        request: Request,
        settlement_id: int,
        social_security_amount: float = Form(0.0),
        store: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    管理员维护单个员工当月社保金额。

    规则：
    1. 只允许管理员操作；
    2. 草稿 / 已确认工资可调整社保；
    3. 已发放并锁定后不可调整；
    4. 实发工资不落库，按“应发工资 - 社保”展示。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以调整社保", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="只有管理员可以调整社保"),
            status_code=303
        )

    settlement = session.get(MonthlySalarySettlement, settlement_id)
    if not settlement:
        if _is_ajax_request(request):
            return _employee_ajax_error("工资结算记录不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="工资结算记录不存在"),
            status_code=303
        )

    if settlement.status in {"paid", "locked"}:
        if _is_ajax_request(request):
            return _employee_ajax_error("已发放并锁定的工资不能调整社保")
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="已发放并锁定的工资不能调整社保"),
            status_code=303
        )

    final_social_security = round(max(float(social_security_amount or 0), 0.0), 2)

    settlement.social_security_amount = final_social_security
    settlement.updated_at = datetime.now()

    session.add(settlement)
    session.commit()
    session.refresh(settlement)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="社保金额已保存",
            action="salary_settlement_updated",
            payload={
                "settlement": _salary_settlement_payload(settlement)
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "salary_settlement", success="社保金额已保存"),
        status_code=303
    )


# =========================
# V3 工资结算：确认单个员工工资
# =========================
@app.post("/employees/salary-settlement/confirm/{settlement_id}")
async def employee_salary_settlement_confirm(
        request: Request,
        settlement_id: int,
        store: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    管理员确认单个员工工资。

    三态流程：
    1. draft -> confirmed；
    2. confirmed 后不能直接重算；
    3. 如需重算，必须先退回草稿；
    4. paid / locked 状态不允许再次确认。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以确认工资", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="只有管理员可以确认工资"),
            status_code=303
        )

    settlement = session.get(MonthlySalarySettlement, settlement_id)
    if not settlement:
        if _is_ajax_request(request):
            return _employee_ajax_error("工资结算记录不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="工资结算记录不存在"),
            status_code=303
        )

    if settlement.status != "draft":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有草稿状态的工资可以确认")
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="只有草稿状态的工资可以确认"),
            status_code=303
        )

    now = datetime.now()

    settlement.status = "confirmed"
    settlement.confirmed_by_user_id = user.id
    settlement.confirmed_by_name = user.display_name
    settlement.confirmed_at = now
    settlement.updated_at = now

    session.add(settlement)
    session.commit()
    session.refresh(settlement)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="工资已确认",
            action="salary_settlement_updated",
            payload={
                "settlement": _salary_settlement_payload(settlement)
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "salary_settlement", success="工资已确认"),
        status_code=303
    )

# =========================
# V3 工资结算：退回草稿
# =========================
@app.post("/employees/salary-settlement/back-to-draft/{settlement_id}")
async def employee_salary_settlement_back_to_draft(
        request: Request,
        settlement_id: int,
        store: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    管理员将已确认工资退回草稿。

    规则：
    1. 只有 confirmed 可以退回 draft；
    2. paid / locked 不能退回；
    3. 退回后允许重新生成 / 重算工资；
    4. 不删除现有工资流水，后续重算时会删除旧的未锁定自动结算流水并重新生成。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以退回工资草稿", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="只有管理员可以退回工资草稿"),
            status_code=303
        )

    settlement = session.get(MonthlySalarySettlement, settlement_id)
    if not settlement:
        if _is_ajax_request(request):
            return _employee_ajax_error("工资结算记录不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="工资结算记录不存在"),
            status_code=303
        )

    if settlement.status != "confirmed":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有已确认状态的工资可以退回草稿")
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="只有已确认状态的工资可以退回草稿"),
            status_code=303
        )

    now = datetime.now()

    settlement.status = "draft"

    # 清空确认信息，表示重新进入可调整/可重算阶段
    settlement.confirmed_by_user_id = None
    settlement.confirmed_by_name = None
    settlement.confirmed_at = None
    settlement.updated_at = now

    session.add(settlement)
    session.commit()
    session.refresh(settlement)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="工资已退回草稿",
            action="salary_settlement_updated",
            payload={
                "settlement": _salary_settlement_payload(settlement)
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "salary_settlement", success="工资已退回草稿"),
        status_code=303
    )

# =========================
# V3 工资结算：发放并锁定
# =========================
@app.post("/employees/salary-settlement/paid/{settlement_id}")
async def employee_salary_settlement_paid(
        request: Request,
        settlement_id: int,
        store: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    管理员标记工资“已发放并锁定”。

    三态流程：
    1. confirmed -> paid；
    2. paid 表示已发放并锁定；
    3. paid 后不可重算；
    4. paid 后锁定该员工该月全部 SalaryFlowRecord；
    5. paid 后不可删除该员工该月工资流水。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以标记工资发放", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="只有管理员可以标记工资发放"),
            status_code=303
        )

    settlement = session.get(MonthlySalarySettlement, settlement_id)
    if not settlement:
        if _is_ajax_request(request):
            return _employee_ajax_error("工资结算记录不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="工资结算记录不存在"),
            status_code=303
        )

    if settlement.status != "confirmed":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有已确认状态的工资可以发放并锁定")
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="只有已确认状态的工资可以发放并锁定"),
            status_code=303
        )

    now = datetime.now()

    # 发放后，锁定该员工该月所有工资流水。
    # 包括自动结算流水、请假扣款、迟到扣款、工资调整流水等。
    flows = session.exec(
        select(SalaryFlowRecord).where(
            SalaryFlowRecord.user_id == settlement.user_id,
            SalaryFlowRecord.salary_year == settlement.salary_year,
            SalaryFlowRecord.salary_month == settlement.salary_month
        )
    ).all()

    for f in flows:
        f.is_locked = True
        f.updated_at = now
        session.add(f)

    settlement.status = "paid"
    settlement.paid_at = now
    settlement.updated_at = now

    session.add(settlement)
    session.commit()
    session.refresh(settlement)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="工资已发放并锁定",
            action="salary_settlement_updated",
            payload={
                "settlement": _salary_settlement_payload(settlement)
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "salary_settlement", success="工资已发放并锁定"),
        status_code=303
    )


# =========================
# V3 工资结算：锁定工资
# =========================
@app.post("/employees/salary-settlement/lock/{settlement_id}")
async def employee_salary_settlement_lock(
        request: Request,
        settlement_id: int,
        store: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    管理员锁定工资。

    锁定规则：
    1. 锁定 MonthlySalarySettlement；
    2. 同步锁定该员工该月所有 SalaryFlowRecord；
    3. 锁定后不允许重算工资，也不允许删除关联工资流水；
    4. 后续若要调整，只能新增下一笔工资修正流水。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以锁定工资", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="只有管理员可以锁定工资"),
            status_code=303
        )

    settlement = session.get(MonthlySalarySettlement, settlement_id)
    if not settlement:
        if _is_ajax_request(request):
            return _employee_ajax_error("工资结算记录不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "salary_settlement", error="工资结算记录不存在"),
            status_code=303
        )

    flows = session.exec(
        select(SalaryFlowRecord).where(
            SalaryFlowRecord.user_id == settlement.user_id,
            SalaryFlowRecord.salary_year == settlement.salary_year,
            SalaryFlowRecord.salary_month == settlement.salary_month
        )
    ).all()

    now = datetime.now()

    for f in flows:
        f.is_locked = True
        f.updated_at = now
        session.add(f)

    # 兼容旧接口：旧的“锁定”操作统一转为 paid，即“已发放并锁定”
    settlement.status = "paid"
    settlement.updated_at = now

    session.add(settlement)
    session.commit()
    session.refresh(settlement)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="工资已发放并锁定",
            action="salary_settlement_updated",
            payload={
                "settlement": _salary_settlement_payload(settlement)
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "salary_settlement", success="工资已锁定"),
        status_code=303
    )

# === 页面展示接口 ===
@app.get("/")
async def read_root(
        request: Request,
        store: str = "牛王庙店",
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user) # <--- 注入用户
):

    # 如果没登录，强制踢到登录页
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    # A. 门店列表：优先从 Store 表读取
    store_objs = get_store_list(session)
    store_list = [s.name for s in store_objs if s.is_active]

    # 当前门店兜底
    if store not in store_list and store_list:
        store = store_list[0]

    # B. 当前门店下包间：优先走 store_id 逻辑
    current_store_rooms = get_active_room_list_by_store(session, store)

    # C. 查询未组齐牌局 (逻辑不变)
    statement = select(GameRecord).where(
        GameRecord.store_name == store,
        GameRecord.status == "unformed"
    )

    results = session.exec(statement).all()

    # V2：未组齐列表优先按预约时间倒序展示
    def _unformed_sort_key(g: GameRecord):
        try:
            st = _normalize_text(g.start_time)
            # 兼容 "03-26 19:30" 这种格式
            if len(st) >= 11 and "-" in st and ":" in st:
                dt_str = f"{g.record_date.year}-{st}"
                dt_obj = datetime.strptime(dt_str, "%Y-%m-%d %H:%M")
                return dt_obj
        except Exception:
            pass
        return datetime.combine(g.record_date, datetime.min.time())

    results.sort(key=_unformed_sort_key, reverse=True)

    return templates.TemplateResponse("index.html", {
        "request": request,
        "page_name": "unformed",
        "current_store": store,
        "store_list": store_list,  # 新增：传给前端所有门店
        "room_list": current_store_rooms,  # 新增：传给前端当前门店的包间
        "game_list": results,
        "today_date": date.today(),
        "current_user": user  # <--- 把用户信息传给前端 (base.html 要用)
    })

# =========================
# V3 团队管理：新增团队
# =========================
@app.post("/employees/teams/add")
async def employee_team_add(
        request: Request,
        store: str = Form(""),
        name: str = Form(...),
        description: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    管理员新增团队。

    AJAX 说明：
    新增团队会影响整个团队卡片结构，第一版返回成功后提示刷新当前页；
    后续如果需要，也可以做前端动态插入完整团队卡片。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以新增团队", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="只有管理员可以新增团队"),
            status_code=303
        )

    name = _normalize_text(name)
    description = _normalize_text(description)

    if not name:
        if _is_ajax_request(request):
            return _employee_ajax_error("团队名称不能为空")
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="团队名称不能为空"),
            status_code=303
        )

    existing = session.exec(
        select(EmployeeTeam).where(EmployeeTeam.name == name)
    ).first()

    if existing:
        if _is_ajax_request(request):
            return _employee_ajax_error("团队名称已存在")
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="团队名称已存在"),
            status_code=303
        )

    now = datetime.now()
    team = EmployeeTeam(
        name=name,
        description=description or None,
        is_active=True,
        created_at=now,
        updated_at=now
    )

    session.add(team)
    session.commit()
    session.refresh(team)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="团队已新增，请刷新页面查看完整团队卡片",
            action="team_created",
            payload={"team": _team_payload(team)}
        )

    return RedirectResponse(
        url=_build_employees_url(store, "team_assessment", success="团队已新增"),
        status_code=303
    )

# =========================
# V3 团队管理：硬删除团队
# =========================
@app.post("/employees/teams/delete/{team_id}")
async def employee_team_delete(
        request: Request,
        team_id: int,
        store: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    管理员硬删除团队。

    硬删除规则：
    1. 只有管理员可以删除团队；
    2. 删除 EmployeeTeam 本体；
    3. 同步删除团队成员 EmployeeTeamMember；
    4. 同步删除团队负责门店 TeamStoreAssignment；
    5. 同步删除团队月度考核 TeamMonthlyAssessment；
    6. 同步删除团队扣分项 TeamAssessmentDeductionItem；
    7. 如果 monthlysalarysettlement 表里已经有历史工资结算引用该团队，
       不删除工资结算记录，只把 team_id 置空，并保留 team_name_snapshot；
    8. AJAX 请求返回 JSON，前端只移除当前团队卡片，不刷新整页。

    注意：
    这是“硬删除”，删除后团队结构和本团队考核明细不可恢复。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以删除团队", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="只有管理员可以删除团队"),
            status_code=303
        )

    team = session.get(EmployeeTeam, team_id)
    if not team:
        if _is_ajax_request(request):
            return _employee_ajax_error("团队不存在或已被删除", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="团队不存在或已被删除"),
            status_code=303
        )

    deleted_team_id = team.id
    deleted_team_name = team.name

    # ===== 1. 工资结算表兼容处理 =====
    # 说明：
    # MonthlySalarySettlement.team_id 是可空字段。
    # 如果后续某员工工资结算已经引用了该团队，硬删除团队时不能删除工资结算历史；
    # 因此这里只解除 team_id 外键关系，team_name_snapshot 仍保留历史团队名。
    try:
        table_exists = session.execute(text("""
            SELECT name
            FROM sqlite_master
            WHERE type='table' AND name='monthlysalarysettlement'
        """)).fetchone()

        if table_exists:
            session.execute(
                text("""
                    UPDATE monthlysalarysettlement
                    SET team_id = NULL
                    WHERE team_id = :team_id
                """),
                {"team_id": deleted_team_id}
            )
    except Exception:
        # 兼容旧库或表不存在场景：
        # 这里不阻断团队删除，因为工资结算模块可能还未正式启用。
        pass

    # ===== 2. 删除团队扣分项 =====
    # 说明：
    # 扣分项同时挂 team_id 和 assessment_id；
    # 必须先删扣分项，再删月度考核。
    session.exec(
        delete(TeamAssessmentDeductionItem).where(
            TeamAssessmentDeductionItem.team_id == deleted_team_id
        )
    )

    # ===== 3. 删除团队月度考核 =====
    session.exec(
        delete(TeamMonthlyAssessment).where(
            TeamMonthlyAssessment.team_id == deleted_team_id
        )
    )

    # ===== 4. 删除团队负责门店 =====
    session.exec(
        delete(TeamStoreAssignment).where(
            TeamStoreAssignment.team_id == deleted_team_id
        )
    )

    # ===== 5. 删除团队成员 =====
    session.exec(
        delete(EmployeeTeamMember).where(
            EmployeeTeamMember.team_id == deleted_team_id
        )
    )

    # ===== 6. 删除团队本体 =====
    session.delete(team)
    session.commit()

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message=f"团队【{deleted_team_name}】已硬删除",
            action="team_deleted",
            payload={
                "team_id": deleted_team_id
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "team_assessment", success=f"团队【{deleted_team_name}】已硬删除"),
        status_code=303
    )


# =========================
# V3 团队管理：添加团队成员
# =========================
@app.post("/employees/teams/{team_id}/members/add")
async def employee_team_member_add(
        request: Request,
        team_id: int,
        store: str = Form(""),
        user_id: int = Form(...),
        remark: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    给团队添加成员。

    说明：
    1. 团队成员允许包含管理员；
    2. 如果该成员以前加入过团队但已停用，则恢复为 active；
    3. 操作后 AJAX 只在当前团队成员列表追加/更新一行。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以维护团队成员", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="只有管理员可以维护团队成员"),
            status_code=303
        )

    team = session.get(EmployeeTeam, team_id)
    if not team:
        if _is_ajax_request(request):
            return _employee_ajax_error("团队不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="团队不存在"),
            status_code=303
        )

    target_user = session.get(User, user_id)
    if not target_user or not getattr(target_user, "is_active", True):
        if _is_ajax_request(request):
            return _employee_ajax_error("员工不存在或已停用")
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="员工不存在或已停用"),
            status_code=303
        )

    remark = _normalize_text(remark)
    now = datetime.now()

    member = session.exec(
        select(EmployeeTeamMember).where(
            EmployeeTeamMember.team_id == team_id,
            EmployeeTeamMember.user_id == user_id
        )
    ).first()

    if member:
        member.is_active = True
        member.left_at = None
        member.remark = remark or member.remark
        member.updated_at = now
    else:
        member = EmployeeTeamMember(
            team_id=team_id,
            user_id=user_id,
            joined_at=date.today(),
            left_at=None,
            is_active=True,
            remark=remark or None,
            created_at=now,
            updated_at=now
        )

    session.add(member)
    session.commit()
    session.refresh(member)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="团队成员已添加",
            action="team_member_added",
            payload={
                "team_id": team_id,
                "member": _team_member_payload(member, target_user)
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "team_assessment", success="团队成员已添加"),
        status_code=303
    )


# =========================
# V3 团队管理：移除团队成员
# =========================
@app.post("/employees/teams/members/remove/{member_id}")
async def employee_team_member_remove(
        request: Request,
        member_id: int,
        store: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    移除团队成员。

    说明：
    这里不物理删除，采用 is_active=False；
    保留历史团队归属，后续工资结算和历史考核可追溯。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以移除团队成员", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="只有管理员可以移除团队成员"),
            status_code=303
        )

    member = session.get(EmployeeTeamMember, member_id)
    if not member:
        if _is_ajax_request(request):
            return _employee_ajax_error("团队成员记录不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="团队成员记录不存在"),
            status_code=303
        )

    member.is_active = False
    member.left_at = date.today()
    member.updated_at = datetime.now()

    session.add(member)
    session.commit()

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="团队成员已移除",
            action="team_member_removed",
            payload={
                "member_id": member_id,
                "team_id": member.team_id
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "team_assessment", success="团队成员已移除"),
        status_code=303
    )


# =========================
# V3 团队管理：分配负责门店
# =========================
@app.post("/employees/teams/{team_id}/stores/add")
async def employee_team_store_add(
        request: Request,
        team_id: int,
        store: str = Form(""),
        store_id: int = Form(...),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    给团队分配负责门店。

    说明：
    团队目标业绩考核只统计 TeamStoreAssignment.is_active=True 的门店。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以维护团队负责门店", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="只有管理员可以维护团队负责门店"),
            status_code=303
        )

    team = session.get(EmployeeTeam, team_id)
    if not team:
        if _is_ajax_request(request):
            return _employee_ajax_error("团队不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="团队不存在"),
            status_code=303
        )

    store_obj = session.get(Store, store_id)
    if not store_obj or not getattr(store_obj, "is_active", True):
        if _is_ajax_request(request):
            return _employee_ajax_error("门店不存在或已停用")
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="门店不存在或已停用"),
            status_code=303
        )

    now = datetime.now()

    assignment = session.exec(
        select(TeamStoreAssignment).where(
            TeamStoreAssignment.team_id == team_id,
            TeamStoreAssignment.store_id == store_id
        )
    ).first()

    if assignment:
        assignment.is_active = True
        assignment.store_name_snapshot = store_obj.name
        assignment.updated_at = now
    else:
        assignment = TeamStoreAssignment(
            team_id=team_id,
            store_id=store_id,
            store_name_snapshot=store_obj.name,
            is_active=True,
            created_at=now,
            updated_at=now
        )

    session.add(assignment)
    session.commit()
    session.refresh(assignment)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="负责门店已添加",
            action="team_store_added",
            payload={
                "team_id": team_id,
                "assignment": _team_store_payload(assignment)
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "team_assessment", success="负责门店已添加"),
        status_code=303
    )


# =========================
# V3 团队管理：取消负责门店
# =========================
@app.post("/employees/teams/stores/remove/{assignment_id}")
async def employee_team_store_remove(
        request: Request,
        assignment_id: int,
        store: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    取消团队负责门店。

    说明：
    不物理删除，设置 is_active=False，保留历史配置痕迹。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以维护团队负责门店", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="只有管理员可以维护团队负责门店"),
            status_code=303
        )

    assignment = session.get(TeamStoreAssignment, assignment_id)
    if not assignment:
        if _is_ajax_request(request):
            return _employee_ajax_error("负责门店记录不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="负责门店记录不存在"),
            status_code=303
        )

    assignment.is_active = False
    assignment.updated_at = datetime.now()

    session.add(assignment)
    session.commit()

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="负责门店已取消",
            action="team_store_removed",
            payload={
                "assignment_id": assignment_id,
                "team_id": assignment.team_id
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "team_assessment", success="负责门店已取消"),
        status_code=303
    )

# =========================
# V3 团队考核：新增扣分项
# =========================
@app.post("/employees/teams/{team_id}/deductions/add")
async def employee_team_deduction_add(
        request: Request,
        team_id: int,
        store: str = Form(""),
        deduct_date: str = Form(...),
        deduct_points: float = Form(...),
        reason: str = Form(...),
        remark: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    新增团队非结果性考核扣分项。

    说明：
    1. 扣分项只影响团队非结果性考核分；
    2. 保存后不立即生成工资流水；
    3. 管理员点击“计算本月考核”后，会按扣分项重新计算团队奖金。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以新增团队扣分项", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="只有管理员可以新增团队扣分项"),
            status_code=303
        )

    team = session.get(EmployeeTeam, team_id)
    if not team:
        if _is_ajax_request(request):
            return _employee_ajax_error("团队不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="团队不存在"),
            status_code=303
        )

    try:
        deduct_d = datetime.strptime(deduct_date, "%Y-%m-%d").date()
    except Exception:
        if _is_ajax_request(request):
            return _employee_ajax_error("扣分日期格式不正确")
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="扣分日期格式不正确"),
            status_code=303
        )

    deduct_points = round(_safe_float(deduct_points), 2)
    if deduct_points <= 0:
        if _is_ajax_request(request):
            return _employee_ajax_error("扣分分值必须大于 0")
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="扣分分值必须大于 0"),
            status_code=303
        )

    reason = _normalize_text(reason)
    remark = _normalize_text(remark)

    if not reason:
        if _is_ajax_request(request):
            return _employee_ajax_error("扣分原因不能为空")
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="扣分原因不能为空"),
            status_code=303
        )

    assessment = _get_or_create_team_assessment(
        session=session,
        team=team,
        year=deduct_d.year,
        month=deduct_d.month
    )

    now = datetime.now()

    item = TeamAssessmentDeductionItem(
        assessment_id=assessment.id,
        team_id=team.id,
        deduct_date=deduct_d,
        deduct_points=deduct_points,
        reason=reason,
        remark=remark or None,
        created_by_user_id=user.id,
        created_by_name=user.display_name,
        created_at=now,
        updated_at=now
    )

    session.add(item)
    session.commit()
    session.refresh(item)

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="团队扣分项已新增",
            action="team_deduction_added",
            payload={
                "team_id": team.id,
                "item": {
                    "id": item.id,
                    "team_id": item.team_id,
                    "assessment_id": item.assessment_id,
                    "deduct_date": str(item.deduct_date),
                    "deduct_points": round(float(item.deduct_points or 0), 2),
                    "reason": item.reason,
                    "remark": item.remark or "",
                    "created_by_name": item.created_by_name,
                    "created_at": item.created_at.strftime("%Y-%m-%d %H:%M:%S") if item.created_at else "",
                }
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "team_assessment", success="团队扣分项已新增"),
        status_code=303
    )


# =========================
# V3 团队考核：删除扣分项
# =========================
@app.post("/employees/teams/deductions/delete/{item_id}")
async def employee_team_deduction_delete(
        request: Request,
        item_id: int,
        store: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    删除团队扣分项。

    说明：
    只删除扣分明细，不自动重新计算团队考核；
    删除后管理员可点击“计算本月考核”刷新结果。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以删除团队扣分项", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="只有管理员可以删除团队扣分项"),
            status_code=303
        )

    item = session.get(TeamAssessmentDeductionItem, item_id)
    if not item:
        if _is_ajax_request(request):
            return _employee_ajax_error("扣分项不存在或已删除", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="扣分项不存在或已删除"),
            status_code=303
        )

    deleted_id = item.id
    team_id = item.team_id

    session.delete(item)
    session.commit()

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="团队扣分项已删除",
            action="team_deduction_deleted",
            payload={
                "item_id": deleted_id,
                "team_id": team_id
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "team_assessment", success="团队扣分项已删除"),
        status_code=303
    )


# =========================
# V3 团队考核：计算本月团队考核
# =========================
@app.post("/employees/teams/{team_id}/assessment/calculate")
async def employee_team_assessment_calculate(
        request: Request,
        team_id: int,
        store: str = Form(""),
        year: int = Form(...),
        month: int = Form(...),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    计算团队月度考核。

    说明：
    1. 只计算并保存 TeamMonthlyAssessment；
    2. 不在本步生成工资流水；
    3. 团队奖金真正进入员工工资，会在后续“工资结算”模块里处理。
    """
    if not user:
        if _is_ajax_request(request):
            return _employee_ajax_error("请先登录", 401)
        return RedirectResponse(url="/login", status_code=303)

    if user.role != "admin":
        if _is_ajax_request(request):
            return _employee_ajax_error("只有管理员可以计算团队考核", 403)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="只有管理员可以计算团队考核"),
            status_code=303
        )

    team = session.get(EmployeeTeam, team_id)
    if not team:
        if _is_ajax_request(request):
            return _employee_ajax_error("团队不存在", 404)
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="团队不存在"),
            status_code=303
        )

    if month < 1 or month > 12:
        if _is_ajax_request(request):
            return _employee_ajax_error("月份不正确")
        return RedirectResponse(
            url=_build_employees_url(store, "team_assessment", error="月份不正确"),
            status_code=303
        )

    assessment = _calculate_team_assessment(
        session=session,
        team=team,
        year=year,
        month=month
    )

    if _is_ajax_request(request):
        return _employee_ajax_success(
            message="团队考核已计算",
            action="team_assessment_calculated",
            payload={
                "team_id": team.id,
                "assessment": _team_assessment_payload(assessment)
            }
        )

    return RedirectResponse(
        url=_build_employees_url(store, "team_assessment", success="团队考核已计算"),
        status_code=303
    )

# === 检索顾客 ===
@app.get("/api/customer-search")
async def customer_search(
        keyword: str,
        store_name: Optional[str] = None,
        limit: int = 8,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        raise HTTPException(status_code=401, detail="请先登录")

    keyword = (keyword or "").strip()
    if not keyword:
        return JSONResponse([])

    limit = max(1, min(limit, 20))

    # 昵称模糊匹配
    matched_customers = session.exec(
        select(Customer).where(Customer.nickname.contains(keyword))
    ).all()

    # 若指定门店，则只保留和该门店有关联的顾客
    if store_name:
        filtered_customers = []
        for cust in matched_customers:
            link = session.exec(
                select(CustomerStoreLink).where(
                    CustomerStoreLink.customer_id == cust.id,
                    CustomerStoreLink.store_name == store_name
                )
            ).first()
            if link:
                filtered_customers.append(cust)
        matched_customers = filtered_customers

    # 排序：完全匹配优先，昵称更短优先，id 更新的优先
    matched_customers.sort(
        key=lambda c: (
            0 if (c.nickname or "") == keyword else 1,
            len(c.nickname or ""),
            -c.id
        )
    )

    items = []
    for cust in matched_customers[:limit]:
        items.append({
            "id": cust.id,
            "nickname": cust.nickname or "",
            "wechat_id": cust.wechat_id or "",
            "gender": cust.gender or "",
            "guarantee_deposit": cust.guarantee_deposit or 0
        })

    return JSONResponse(items)

@app.post("/api/validate-unformed-game-players")
async def validate_unformed_game_players(
        player_1: str = Form(""), player_2: str = Form(""),
        player_3: str = Form(""), player_4: str = Form(""),
        player_1_wechat: str = Form(""), player_2_wechat: str = Form(""),
        player_3_wechat: str = Form(""), player_4_wechat: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        raise HTTPException(status_code=401, detail="请先登录")

    slots = _normalize_player_slots(
        player_1, player_2, player_3, player_4,
        player_1_wechat, player_2_wechat, player_3_wechat, player_4_wechat
    )

    ok, msg, indices, error_type = _validate_players_and_customer_binding_detailed(session, slots)

    return JSONResponse({
        "ok": ok,
        "message": msg,
        "indices": indices,
        "error_type": error_type
    })



# === 新增组局接口 ===
@app.post("/add-game")
async def add_game(
        store_name: str = Form(...),
        start_time_full: str = Form(...),

        stakes_select: str = Form(...),
        stakes_custom: Optional[str] = Form(None),
        game_type: str = Form(...),

        player_1: str = Form(""), player_2: str = Form(""),
        player_3: str = Form(""), player_4: str = Form(""),

        player_1_wechat: str = Form(""), player_2_wechat: str = Form(""),
        player_3_wechat: str = Form(""), player_4_wechat: str = Form(""),

        tags: str = Form(""),

        # V2：未组齐阶段允许为空，前端后续再同步放开
        room_name: Optional[str] = Form(""),
        payment_method: Optional[str] = Form(""),
        room_fee: float = Form(0),

        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user),
):
    if not user:
        return RedirectResponse(url="/login?error=请先登录", status_code=303)

    # 1. 门店合法性校验
    store_obj = get_store_by_name(session, store_name)
    if not store_obj:
        return RedirectResponse(url="/?error=所选门店不存在", status_code=303)
    if not store_obj.is_active:
        return RedirectResponse(url=f"/?store={store_name}&error=所选门店已停用", status_code=303)

    # 2. 解析预约时间（V2：record_date + start_time 视为预约时间）
    new_record_date, new_start_time_str = _parse_reservation_datetime_local(start_time_full)

    # 3. 分数逻辑
    final_stakes = _normalize_text(stakes_custom) if stakes_select == "其他" else _normalize_text(stakes_select)

    # 4. 参与人严格校验
    slots = _normalize_player_slots(
        player_1, player_2, player_3, player_4,
        player_1_wechat, player_2_wechat, player_3_wechat, player_4_wechat
    )
    ok, msg, indices, error_type = _validate_players_and_customer_binding_detailed(session, slots)
    if not ok:
        return RedirectResponse(
            url=f"/?store={store_name}&error={msg}",
            status_code=303
        )

    # 4.1 品牌黑名单校验
    ok, msg = _check_brand_blacklist_for_slots(session, slots)
    if not ok:
        return RedirectResponse(
            url=f"/?store={store_name}&error={msg}",
            status_code=303
        )

    # 5. V2：月序号（同门店、同自然月、按预约时间所属月份）
    new_serial = _get_monthly_serial_number(session, store_name, new_record_date)

    # 6. room_name 若传了值，才校验其是否属于该门店；空值允许通过
    room_name = _normalize_text(room_name)
    if room_name:
        room_obj = session.exec(
            select(Room).where(
                Room.store_id == store_obj.id,
                Room.name == room_name,
                Room.is_active == True
            )
        ).first()

        if not room_obj:
            # fallback 兼容旧数据
            room_obj = session.exec(
                select(Room).where(
                    Room.store_name == store_name,
                    Room.name == room_name
                )
            ).first()

        if not room_obj:
            return RedirectResponse(
                url=f"/?store={store_name}&error=所选包间不存在或不属于当前门店",
                status_code=303
            )

    # 7. 创建未组齐记录
    now = datetime.now()
    new_game = GameRecord(
        store_name=store_name,
        serial_number=new_serial,

        # 预约时间
        record_date=new_record_date,
        start_time=new_start_time_str,

        stakes=final_stakes,
        game_type=_normalize_text(game_type),

        player_1=_normalize_text(player_1),
        player_2=_normalize_text(player_2),
        player_3=_normalize_text(player_3),
        player_4=_normalize_text(player_4),

        player_1_wechat=_normalize_text(player_1_wechat),
        player_2_wechat=_normalize_text(player_2_wechat),
        player_3_wechat=_normalize_text(player_3_wechat),
        player_4_wechat=_normalize_text(player_4_wechat),

        # 未组齐区特殊备注来源：tags
        tags=_normalize_text(tags),

        # V2：未组齐阶段允许为空
        room_name=room_name or None,
        payment_method=_normalize_text(payment_method) or None,
        room_fee=room_fee or 0.0,

        status="unformed",

        # V2：确定新增的人就是第一个接待店长，组齐时再覆盖
        who_did=user.display_name,

        created_at=now,
        updated_at=now,
        updated_by=user.display_name,
    )
    session.add(new_game)
    session.commit()

    return RedirectResponse(url=f"/?store={store_name}", status_code=303)


# === 状态更新接口 ===
@app.get("/game/{action}/{game_id}")
async def update_game_status(
        action: str,
        game_id: int,
        store: str,

        pay_status: str = "all",
        date_filter: str = "today",
        start_date: str = "",
        end_date: str = "",
        payment_method_filter: str = "all",

        user: Optional[User] = Depends(get_current_user),
        session: Session = Depends(get_session)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    game = session.get(GameRecord, game_id)
    if not game:
        raise HTTPException(status_code=404, detail="Game not found")

    # ===== 1) 组齐 =====
    if action == "confirm":
        game.status = "formed"

        # V2：谁点击“组齐”，who_did 就覆盖为谁
        game.who_did = user.display_name

        game.updated_at = datetime.now()
        game.updated_by = user.display_name

        session.add(game)
        session.commit()
        return RedirectResponse(
            url=f"/?store={store}",
            status_code=303
        )

    # ===== 2) 退回未组齐 =====
    elif action == "revert":
        # V2：原操作保留；订单开始时间清空
        # 但玩家备注、整桌备注、room_fee 不清空
        game.status = "unformed"
        game.order_start_time = None

        game.updated_at = datetime.now()
        game.updated_by = user.display_name

        session.add(game)
        session.commit()
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter
            ),
            status_code=303
        )

    # ===== 3) 撤销 =====
    elif action == "delete":
        if game.status == "unformed":
            if not _can_delete_unformed_game(user, game):
                return RedirectResponse(
                    url=f"/?store={store}&error=无权撤销该未组齐记录",
                    status_code=303
                )
        else:
            # 保留旧操作，但 formed 状态下仍建议限制为 admin 或接待人
            is_admin = (user.role == "admin")
            is_owner = (game.who_did == user.display_name)
            if not (is_admin or is_owner):
                return RedirectResponse(
                    url=_build_formed_redirect_url(
                        store=store,
                        pay_status=pay_status,
                        date_filter=date_filter,
                        start_date=start_date,
                        end_date=end_date,
                        payment_method_filter=payment_method_filter,
                        error="无权撤销该已组齐记录"
                    ),
                    status_code=303
                )

        session.delete(game)
        session.commit()

        redirect_base = "/formed-games" if game.status == "formed" else "/"
        return RedirectResponse(url=f"{redirect_base}?store={store}", status_code=303)

    raise HTTPException(status_code=400, detail="Unsupported action")

# === 更新组局接口  ===
@app.post("/update-game/{game_id}")
async def update_game(
        game_id: int,
        store_name: str = Form(...),
        start_time_full: str = Form(...),

        stakes_select: str = Form(...),
        stakes_custom: Optional[str] = Form(None),
        game_type: str = Form(...),

        player_1: str = Form(""), player_2: str = Form(""),
        player_3: str = Form(""), player_4: str = Form(""),

        player_1_wechat: str = Form(""), player_2_wechat: str = Form(""),
        player_3_wechat: str = Form(""), player_4_wechat: str = Form(""),

        tags: str = Form(""),

        # V2：未组齐编辑允许为空
        room_name: Optional[str] = Form(""),
        payment_method: Optional[str] = Form(""),
        room_fee: float = Form(0),

        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user),
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    game = session.get(GameRecord, game_id)
    if not game:
        raise HTTPException(status_code=404, detail="Game not found")

    # 1. 门店合法性校验
    store_obj = get_store_by_name(session, store_name)
    if not store_obj:
        return RedirectResponse(url=f"/?store={store_name}&error=所选门店不存在", status_code=303)
    if not store_obj.is_active:
        return RedirectResponse(url=f"/?store={store_name}&error=所选门店已停用", status_code=303)

    # 2. 参与人严格校验
    slots = _normalize_player_slots(
        player_1, player_2, player_3, player_4,
        player_1_wechat, player_2_wechat, player_3_wechat, player_4_wechat
    )
    ok, msg = _validate_players_and_customer_binding(session, slots)
    if not ok:
        redirect_base = "/formed-games" if game.status == "formed" else "/"
        return RedirectResponse(
            url=f"{redirect_base}?store={store_name}&error={msg}",
            status_code=303
        )

    ok, msg = _check_brand_blacklist_for_slots(session, slots)
    if not ok:
        redirect_base = "/formed-games" if game.status == "formed" else "/"
        return RedirectResponse(
            url=f"{redirect_base}?store={store_name}&error={msg}",
            status_code=303
        )

    # 3. 解析预约时间
    new_record_date, new_start_time_str = _parse_reservation_datetime_local(start_time_full)

    # 4. 分数逻辑
    final_stakes = _normalize_text(stakes_custom) if stakes_select == "其他" else _normalize_text(stakes_select)

    # 5. room_name 若传了值，才校验归属；空值允许
    room_name = _normalize_text(room_name)
    if room_name:
        room_obj = session.exec(
            select(Room).where(
                Room.store_id == store_obj.id,
                Room.name == room_name,
                Room.is_active == True
            )
        ).first()

        if not room_obj:
            room_obj = session.exec(
                select(Room).where(
                    Room.store_name == store_name,
                    Room.name == room_name
                )
            ).first()

        if not room_obj:
            redirect_base = "/formed-games" if game.status == "formed" else "/"
            return RedirectResponse(
                url=f"{redirect_base}?store={store_name}&error=所选包间不存在或不属于当前门店",
                status_code=303
            )

    # 6. V2：如果预约时间月份变了，则月序号要按新月份重新计算
    old_month_key = (game.record_date.year, game.record_date.month) if game.record_date else None
    new_month_key = (new_record_date.year, new_record_date.month)
    if game.store_name != store_name or old_month_key != new_month_key:
        game.serial_number = _get_monthly_serial_number(session, store_name, new_record_date)

    # 7. 更新基础字段
    game.store_name = store_name
    game.record_date = new_record_date
    game.start_time = new_start_time_str

    game.stakes = final_stakes
    game.game_type = _normalize_text(game_type)

    game.player_1 = _normalize_text(player_1)
    game.player_2 = _normalize_text(player_2)
    game.player_3 = _normalize_text(player_3)
    game.player_4 = _normalize_text(player_4)

    game.player_1_wechat = _normalize_text(player_1_wechat)
    game.player_2_wechat = _normalize_text(player_2_wechat)
    game.player_3_wechat = _normalize_text(player_3_wechat)
    game.player_4_wechat = _normalize_text(player_4_wechat)

    game.tags = _normalize_text(tags)

    # 未组齐阶段允许为空；已组齐编辑那套“包间必填”后面走专门接口处理
    game.room_name = room_name or None
    game.payment_method = _normalize_text(payment_method) or None
    game.room_fee = room_fee or 0.0

    game.updated_at = datetime.now()
    game.updated_by = user.display_name

    session.add(game)
    session.commit()

    redirect_base = "/formed-games" if game.status == "formed" else "/"
    return RedirectResponse(url=f"{redirect_base}?store={store_name}", status_code=303)


# ===  更新支付信息接口 (升级版：自动同步顾客数据) ===
@app.post("/update-payment/{game_id}")
async def update_payment(
        request: Request,
        game_id: int,
        store_name: str = Form(...),
        is_payAll: str = Form(...),
        wechat_pay: float = Form(0.0),
        Alipay: float = Form(0.0),

        source_filter: str = Form(""),
        pay_status: str = Form("all"),
        date_filter: str = Form("today"),
        start_date: str = Form(""),
        end_date: str = Form(""),
        payment_method_filter: str = Form("all"),

        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    game = session.get(GameRecord, game_id)
    if not game:
        raise HTTPException(status_code=404)

    current_source_filter = _normalize_formed_source_filter(
        source_filter or _normalize_text(game.record_source)
    )

    if game.record_source == FORMED_SOURCE_SELF_ARRIVAL:
        if _normalize_text(game.payment_method) != "代客收款":

            msg = "只有下单方式为代客收款的自主到店登记单才能结算"
            if _is_ajax_request(request):
                return JSONResponse({"ok": False, "message": msg}, status_code=400)

            return RedirectResponse(
                url=_build_formed_redirect_url(
                    store=store_name,
                    source_filter=current_source_filter,
                    pay_status=pay_status,
                    date_filter=date_filter,
                    start_date=start_date,
                    end_date=end_date,
                    payment_method_filter=payment_method_filter,
                    error=msg
                ),
                status_code=303
            )

        if (game.room_fee or 0) <= 0:
            return RedirectResponse(
                url=_build_formed_redirect_url(
                    store=store_name,
                    source_filter=current_source_filter,
                    pay_status=pay_status,
                    date_filter=date_filter,
                    start_date=start_date,
                    end_date=end_date,
                    payment_method_filter=payment_method_filter,
                    error="该自主到店登记单费用异常，无法结算"
                ),
                status_code=303
            )

    was_paid = game.is_payAll

    new_is_payAll = (is_payAll == "true")
    game.is_payAll = new_is_payAll
    game.wechat_pay = wechat_pay
    game.Alipay = Alipay
    game.updated_at = datetime.now()
    game.updated_by = user.display_name
    session.add(game)

    if not was_paid and new_is_payAll:
        print(f"检测到牌局 #{game.serial_number} 完成结算，开始同步顾客数据...")

        raw_players = [
            (game.player_1, game.player_1_wechat),
            (game.player_2, game.player_2_wechat),
            (game.player_3, game.player_3_wechat),
            (game.player_4, game.player_4_wechat)
        ]

        valid_customer_ids = []

        for nickname, wechat in raw_players:
            if not wechat:
                continue

            today = date.today()

            cust = session.exec(select(Customer).where(Customer.wechat_id == wechat)).first()

            if not cust:
                cust = Customer(
                    nickname=nickname or "未知昵称",
                    wechat_id=wechat,
                    gender="未知",
                    guarantee_deposit=0.0,
                    last_visit_date=today,
                    created_at=today
                )
                session.add(cust)
                session.commit()
                session.refresh(cust)
            else:
                cust.last_visit_date = today
                if cust.is_loss:
                    cust.is_loss = False
                session.add(cust)

            valid_customer_ids.append(cust.id)

            link = session.exec(
                select(CustomerStoreLink).where(
                    CustomerStoreLink.customer_id == cust.id,
                    CustomerStoreLink.store_name == store_name
                )
            ).first()

            if not link:
                link = CustomerStoreLink(
                    customer_id=cust.id,
                    store_name=store_name,
                    created_at=today,
                    last_visit_at_store=today
                )
            else:
                link.last_visit_at_store = today

            session.add(link)

        for id1, id2 in itertools.combinations(sorted(valid_customer_ids), 2):
            pf = session.exec(select(PlayFrequency).where(
                PlayFrequency.player_1_id == id1,
                PlayFrequency.player_2_id == id2
            )).first()

            if not pf:
                pf = PlayFrequency(
                    player_1_id=id1,
                    player_2_id=id2,
                    count=1,
                    last_play_date=date.today()
                )
            else:
                pf.count += 1
                pf.last_play_date = date.today()

            session.add(pf)

    session.commit()

    if _is_ajax_request(request):
        return JSONResponse({
            "ok": True,
            "game_id": game.id,
            "message": "结算已保存"
        })

    return RedirectResponse(
        url=_build_formed_redirect_url(
            store=store_name,
            source_filter=current_source_filter,
            pay_status=pay_status,
            date_filter=date_filter,
            start_date=start_date,
            end_date=end_date,
            payment_method_filter=payment_method_filter,
            focus_game_id=game.id,
        ),
        status_code=303
    )


# === 已组齐牌局页面接口 ===
@app.get("/formed-games")
async def formed_games(
        request: Request,
        store: str = "牛王庙店",
        source_filter: str = FORMED_SOURCE_NORMAL,

        pay_status: str = "all",
        date_filter: str = "today",
        start_date: str = "",
        end_date: str = "",
        payment_method_filter: str = "all",

        focus_game_id: Optional[int] = None,
        duplicate_warning_message: str = "",
        reopen_edit_game_id: Optional[int] = None,

        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    source_filter = _normalize_formed_source_filter(source_filter)

    store_objs = get_store_list(session)
    store_list = [s.name for s in store_objs if s.is_active]

    if store not in store_list and store_list:
        store = store_list[0]

    current_store_rooms = get_active_room_list_by_store(session, store)

    statement = select(GameRecord).where(
        GameRecord.store_name == store,
        GameRecord.status == "formed",
        GameRecord.record_source == source_filter
    )

    results = session.exec(statement).all()

    filtered_results = [
        g for g in results
        if _match_formed_game_filters(
            g,
            source_filter=source_filter,
            pay_status=pay_status,
            date_filter=date_filter,
            start_date=start_date,
            end_date=end_date,
            payment_method_filter=payment_method_filter
        )
    ]

    if focus_game_id:
        focus_game = session.get(GameRecord, focus_game_id)
        if (
            focus_game
            and focus_game.status == "formed"
            and focus_game.store_name == store
            and _normalize_text(focus_game.record_source) == source_filter
        ):
            if all(g.id != focus_game.id for g in filtered_results):
                filtered_results.append(focus_game)

    filtered_results.sort(key=_game_effective_order_dt, reverse=True)

    total_collection_amount = 0.0
    collected_amount = 0.0
    uncollected_amount = 0.0
    wechat_collection_amount = 0.0
    alipay_collection_amount = 0.0

    overflow_order_count = 0
    overflow_reserved_total = 0.0
    overflow_received_total = 0.0
    overflow_profit_total = 0.0
    overflow_paid_count = 0
    overflow_unpaid_count = 0

    if source_filter == FORMED_SOURCE_NORMAL:
        collection_games = [
            g for g in filtered_results
            if _normalize_text(g.payment_method) == "代客收款"
        ]
        total_collection_amount = round(sum((g.room_fee or 0) for g in collection_games), 2)
        collected_amount = round(sum((g.wechat_pay or 0) + (g.Alipay or 0) for g in collection_games), 2)
        uncollected_amount = round(total_collection_amount - collected_amount, 2)
        wechat_collection_amount = round(sum((g.wechat_pay or 0) for g in collection_games), 2)
        alipay_collection_amount = round(sum((g.Alipay or 0) for g in collection_games), 2)

    elif source_filter == FORMED_SOURCE_OVERFLOW:
        overflow_order_count = len(filtered_results)
        overflow_reserved_total = round(sum((g.room_fee or 0) for g in filtered_results), 2)
        overflow_received_total = round(sum((g.wechat_pay or 0) + (g.Alipay or 0) for g in filtered_results), 2)
        overflow_profit_total = round(sum(
            ((g.wechat_pay or 0) + (g.Alipay or 0) - (g.room_fee or 0))
            for g in filtered_results
        ), 2)
        overflow_paid_count = len([g for g in filtered_results if g.is_payAll])
        overflow_unpaid_count = len([g for g in filtered_results if not g.is_payAll])

    return templates.TemplateResponse("formed_games.html", {
        "request": request,
        "page_name": "formed",
        "current_store": store,
        "store_list": store_list,
        "room_list": current_store_rooms,
        "game_list": filtered_results,
        "current_user": user,

        "source_filter": source_filter,
        "pay_status": pay_status,
        "date_filter": date_filter,
        "start_date": start_date,
        "end_date": end_date,
        "payment_method_filter": payment_method_filter,
        "today_date": date.today(),
        "focus_game_id": focus_game_id,

        "duplicate_warning_message": duplicate_warning_message,
        "reopen_edit_game_id": reopen_edit_game_id,

        "total_collection_amount": total_collection_amount,
        "collected_amount": collected_amount,
        "uncollected_amount": uncollected_amount,
        "wechat_collection_amount": wechat_collection_amount,
        "alipay_collection_amount": alipay_collection_amount,

        "overflow_order_count": overflow_order_count,
        "overflow_reserved_total": overflow_reserved_total,
        "overflow_received_total": overflow_received_total,
        "overflow_profit_total": overflow_profit_total,
        "overflow_paid_count": overflow_paid_count,
        "overflow_unpaid_count": overflow_unpaid_count,
    })

@app.post("/formed-games/self-arrival/add")
async def add_self_arrival_game(
        store_name: str = Form(...),
        room_name: str = Form(...),
        order_start_time_full: str = Form(...),
        player_1: str = Form(...),
        player_1_wechat: str = Form(...),
        payment_method: str = Form(...),
        room_fee: float = Form(0.0),

        pay_status: str = Form("all"),
        date_filter: str = Form("today"),
        start_date: str = Form(""),
        end_date: str = Form(""),
        payment_method_filter: str = Form("all"),

        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user),
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    store_obj = get_store_by_name(session, store_name)
    if not store_obj:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                error="所选门店不存在"
            ),
            status_code=303
        )
    if not store_obj.is_active:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                error="所选门店已停用"
            ),
            status_code=303
        )

    room_name = _normalize_text(room_name)
    if not room_name:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="预约包间必填"
            ),
            status_code=303
        )

    room_obj = session.exec(
        select(Room).where(
            Room.store_id == store_obj.id,
            Room.name == room_name,
            Room.is_active == True
        )
    ).first()

    if not room_obj:
        room_obj = session.exec(
            select(Room).where(
                Room.store_name == store_name,
                Room.name == room_name
            )
        ).first()

    if not room_obj:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="所选包间不存在或不属于当前门店"
            ),
            status_code=303
        )

    try:
        order_date, order_start_time = _parse_required_self_arrival_order_start_time(order_start_time_full)
    except ValueError as e:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=str(e)
            ),
            status_code=303
        )

    payment_method = _normalize_text(payment_method)
    if payment_method not in SELF_ARRIVAL_PAYMENT_METHODS:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="下单方式不合法"
            ),
            status_code=303
        )

    slots = _normalize_player_slots(
        player_1, "", "", "",
        player_1_wechat, "", "", ""
    )
    ok, msg = _validate_players_and_customer_binding(session, slots)
    if not ok:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=msg
            ),
            status_code=303
        )

    ok, msg = _check_brand_blacklist_for_slots(session, slots)
    if not ok:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=msg
            ),
            status_code=303
        )

    final_room_fee = room_fee or 0.0
    if payment_method == "代客收款":
        if final_room_fee <= 0:
            return RedirectResponse(
                url=_build_formed_redirect_url(
                    store=store_name,
                    source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                    pay_status=pay_status,
                    date_filter=date_filter,
                    start_date=start_date,
                    end_date=end_date,
                    payment_method_filter=payment_method_filter,
                    error="下单方式为代客收款时，费用必须大于0"
                ),
                status_code=303
            )
    else:
        final_room_fee = 0.0

    new_serial = _get_monthly_serial_number(session, store_name, order_date)
    now = datetime.now()

    new_game = GameRecord(
        store_name=store_name,
        serial_number=new_serial,
        record_date=order_date,
        start_time="自主到店",

        stakes="无",
        game_type="无",

        player_1=_normalize_text(player_1),
        player_2=None,
        player_3=None,
        player_4=None,

        player_1_wechat=_normalize_text(player_1_wechat),
        player_2_wechat=None,
        player_3_wechat=None,
        player_4_wechat=None,

        tags=None,

        player_1_note=None,
        player_2_note=None,
        player_3_note=None,
        player_4_note=None,
        table_note="该单为自主到店登记单",

        room_name=room_name,
        payment_method=payment_method,
        room_fee=final_room_fee,

        order_start_time=order_start_time,

        status="formed",
        record_source=FORMED_SOURCE_SELF_ARRIVAL,
        who_did=user.display_name,

        is_payAll=False,
        wechat_pay=0.0,
        Alipay=0.0,

        created_at=now,
        updated_at=now,
        updated_by=user.display_name,
    )

    session.add(new_game)
    session.flush()

    duplicate_warning_message = ""
    duplicate_hit = _find_possible_duplicate_formed_game(
        session=session,
        current_game=new_game,
        tolerance_minutes=10
    )
    if duplicate_hit:
        duplicate_warning_message = (
            f"经过新增后，疑似与{_format_duplicate_game_label(duplicate_hit)}订单为同一订单，请确认"
        )

    session.commit()

    return RedirectResponse(
        url=_build_formed_redirect_url(
            store=store_name,
            source_filter=FORMED_SOURCE_SELF_ARRIVAL,
            pay_status=pay_status,
            date_filter=date_filter,
            start_date=start_date,
            end_date=end_date,
            payment_method_filter=payment_method_filter,
            focus_game_id=new_game.id,
            duplicate_warning_message=duplicate_warning_message,
            reopen_edit_game_id=new_game.id if duplicate_warning_message else None,
        ),
        status_code=303
    )

    session.add(new_game)
    session.flush()

    duplicate_warning_message = ""
    duplicate_hit = _find_possible_duplicate_formed_game(
        session=session,
        current_game=new_game,
        tolerance_minutes=10
    )
    if duplicate_hit:
        duplicate_warning_message = (
            f"经过新增后，疑似与{_format_duplicate_game_label(duplicate_hit)}订单为同一订单，请确认"
        )

    session.commit()

    return RedirectResponse(
        url=_build_formed_redirect_url(
            store=store_name,
            pay_status=pay_status,
            date_filter=date_filter,
            start_date=start_date,
            end_date=end_date,
            payment_method_filter=payment_method_filter,
            focus_game_id=new_game.id,
            duplicate_warning_message=duplicate_warning_message,
            reopen_edit_game_id=new_game.id if duplicate_warning_message else None,
        ),
        status_code=303
    )


@app.post("/formed-games/self-arrival/update/{game_id}")
async def update_self_arrival_game(
        request: Request,
        game_id: int,
        store_name: str = Form(...),
        room_name: str = Form(...),
        order_start_time_full: str = Form(...),
        player_1: str = Form(...),
        player_1_wechat: str = Form(...),
        payment_method: str = Form(...),
        room_fee: float = Form(0.0),

        pay_status: str = Form("all"),
        date_filter: str = Form("today"),
        start_date: str = Form(""),
        end_date: str = Form(""),
        payment_method_filter: str = Form("all"),

        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user),
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    game = session.get(GameRecord, game_id)
    if not game:
        raise HTTPException(status_code=404, detail="订单不存在")

    if game.record_source != FORMED_SOURCE_SELF_ARRIVAL:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="该订单不是自主到店登记单"
            ),
            status_code=303
        )

    store_obj = get_store_by_name(session, store_name)
    if not store_obj:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                error="所选门店不存在"
            ),
            status_code=303
        )
    if not store_obj.is_active:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                error="所选门店已停用"
            ),
            status_code=303
        )

    room_name = _normalize_text(room_name)
    if not room_name:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="预约包间必填"
            ),
            status_code=303
        )

    room_obj = session.exec(
        select(Room).where(
            Room.store_id == store_obj.id,
            Room.name == room_name,
            Room.is_active == True
        )
    ).first()

    if not room_obj:
        room_obj = session.exec(
            select(Room).where(
                Room.store_name == store_name,
                Room.name == room_name
            )
        ).first()

    if not room_obj:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="所选包间不存在或不属于当前门店"
            ),
            status_code=303
        )

    try:
        order_date, order_start_time = _parse_required_self_arrival_order_start_time(order_start_time_full)
    except ValueError as e:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=str(e)
            ),
            status_code=303
        )

    payment_method = _normalize_text(payment_method)
    if payment_method not in SELF_ARRIVAL_PAYMENT_METHODS:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="下单方式不合法"
            ),
            status_code=303
        )

    slots = _normalize_player_slots(
        player_1, "", "", "",
        player_1_wechat, "", "", ""
    )
    ok, msg = _validate_players_and_customer_binding(session, slots)
    if not ok:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=msg
            ),
            status_code=303
        )

    ok, msg = _check_brand_blacklist_for_slots(session, slots)
    if not ok:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=msg
            ),
            status_code=303
        )

    if payment_method != "代客收款" and _has_any_system_receipt(game):
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="该自主到店单已存在微信/支付宝收款记录，不能改成非代客收款"
            ),
            status_code=303
        )

    final_room_fee = room_fee or 0.0
    if payment_method == "代客收款":
        if final_room_fee <= 0:
            return RedirectResponse(
                url=_build_formed_redirect_url(
                    store=store_name,
                    source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                    pay_status=pay_status,
                    date_filter=date_filter,
                    start_date=start_date,
                    end_date=end_date,
                    payment_method_filter=payment_method_filter,
                    error="下单方式为代客收款时，费用必须大于0"
                ),
                status_code=303
            )
    else:
        final_room_fee = 0.0

    old_month_key = (game.record_date.year, game.record_date.month) if game.record_date else None
    new_month_key = (order_date.year, order_date.month)
    if game.store_name != store_name or old_month_key != new_month_key:
        game.serial_number = _get_monthly_serial_number(session, store_name, order_date)

    game.store_name = store_name
    game.record_date = order_date
    game.start_time = "自主到店"
    game.order_start_time = order_start_time

    game.room_name = room_name
    game.payment_method = payment_method
    game.room_fee = final_room_fee

    game.stakes = "无"
    game.game_type = "无"
    game.tags = None

    game.player_1 = _normalize_text(player_1)
    game.player_1_wechat = _normalize_text(player_1_wechat)

    game.player_2 = None
    game.player_3 = None
    game.player_4 = None

    game.player_2_wechat = None
    game.player_3_wechat = None
    game.player_4_wechat = None

    game.player_1_note = None
    game.player_2_note = None
    game.player_3_note = None
    game.player_4_note = None

    game.table_note = "该单为自主到店登记单"
    game.status = "formed"
    game.record_source = FORMED_SOURCE_SELF_ARRIVAL

    game.updated_at = datetime.now()
    game.updated_by = user.display_name

    session.add(game)
    session.flush()

    duplicate_warning_message = ""
    duplicate_hit = _find_possible_duplicate_formed_game(
        session=session,
        current_game=game,
        tolerance_minutes=10
    )
    if duplicate_hit:
        duplicate_warning_message = (
            f"经过编辑后，疑似与{_format_duplicate_game_label(duplicate_hit)}订单为同一订单，请确认"
        )

    session.commit()

    if _is_ajax_request(request):
        return JSONResponse({
            "ok": True,
            "game_id": game.id,
            "message": "自主到店登记单已保存",
            "duplicate_warning_message": duplicate_warning_message or ""
        })

    return RedirectResponse(
        url=_build_formed_redirect_url(
            store=store_name,
            source_filter=FORMED_SOURCE_SELF_ARRIVAL,
            pay_status=pay_status,
            date_filter=date_filter,
            start_date=start_date,
            end_date=end_date,
            payment_method_filter=payment_method_filter,
            focus_game_id=game.id,
            duplicate_warning_message=duplicate_warning_message,
            reopen_edit_game_id=game.id if duplicate_warning_message else None,
        ),
        status_code=303
    )

@app.get("/formed-games/self-arrival/delete/{game_id}")
async def delete_self_arrival_game(
        game_id: int,
        store: str,
        pay_status: str = "all",
        date_filter: str = "today",
        start_date: str = "",
        end_date: str = "",
        payment_method_filter: str = "all",
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    game = session.get(GameRecord, game_id)
    if not game:
        raise HTTPException(status_code=404, detail="订单不存在")

    if game.record_source != FORMED_SOURCE_SELF_ARRIVAL:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="该订单不是自主到店登记单"
            ),
            status_code=303
        )

    is_admin = (user.role == "admin")
    is_owner = (game.who_did == user.display_name)

    if not (is_admin or is_owner):
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="无权删除该自主到店登记单"
            ),
            status_code=303
        )

    session.delete(game)
    session.commit()

    return RedirectResponse(
        url=_build_formed_redirect_url(
            store=store,
            source_filter=FORMED_SOURCE_SELF_ARRIVAL,
            pay_status=pay_status,
            date_filter=date_filter,
            start_date=start_date,
            end_date=end_date,
            payment_method_filter=payment_method_filter
        ),
        status_code=303
    )

@app.post("/formed-games/overflow/add")
async def add_overflow_game(
        store_name: str = Form(...),
        start_time_full: str = Form(""),
        order_start_time_full: str = Form(""),

        external_store_name: str = Form(...),
        room_name: str = Form(""),

        stakes_select: str = Form(""),
        stakes_custom: Optional[str] = Form(None),
        game_type: str = Form(""),

        player_1: str = Form(""), player_2: str = Form(""),
        player_3: str = Form(""), player_4: str = Form(""),

        player_1_wechat: str = Form(""), player_2_wechat: str = Form(""),
        player_3_wechat: str = Form(""), player_4_wechat: str = Form(""),

        player_1_note: str = Form(""), player_2_note: str = Form(""),
        player_3_note: str = Form(""), player_4_note: str = Form(""),

        tags: str = Form(""),
        table_note: str = Form(""),
        room_fee: float = Form(0.0),

        pay_status: str = Form("all"),
        date_filter: str = Form("today"),
        start_date: str = Form(""),
        end_date: str = Form(""),
        payment_method_filter: str = Form("all"),

        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user),
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    store_obj = get_store_by_name(session, store_name)
    if not store_obj:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_OVERFLOW,
                error="所选归属门店不存在"
            ),
            status_code=303
        )
    if not store_obj.is_active:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_OVERFLOW,
                error="所选归属门店已停用"
            ),
            status_code=303
        )

    external_store_name = _normalize_text(external_store_name)
    if not external_store_name:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_OVERFLOW,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="外部安排门店必填"
            ),
            status_code=303
        )

    # 预约时间：新增时允许为空；为空则先挂今天，预约时分留空
    if _normalize_text(start_time_full):
        new_record_date, new_start_time_str = _parse_reservation_datetime_local(start_time_full)
    else:
        new_record_date, new_start_time_str = date.today(), ""

    # 订单开始时间：允许为空
    order_start_time = _parse_optional_order_start_time(order_start_time_full)

    room_name = _normalize_text(room_name)

    final_stakes = _normalize_text(stakes_custom) if _normalize_text(stakes_select) == "其他" else _normalize_text(stakes_select)
    final_game_type = _normalize_text(game_type)

    final_room_fee = room_fee or 0.0
    if final_room_fee < 0:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_OVERFLOW,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="预定金额不能小于0"
            ),
            status_code=303
        )

    # 参与人校验：和常规单一致
    slots = _normalize_player_slots(
        player_1, player_2, player_3, player_4,
        player_1_wechat, player_2_wechat, player_3_wechat, player_4_wechat
    )
    ok, msg = _validate_players_and_customer_binding(session, slots)
    if not ok:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_OVERFLOW,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=msg
            ),
            status_code=303
        )

    ok, msg = _check_brand_blacklist_for_slots(session, slots)
    if not ok:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_OVERFLOW,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=msg
            ),
            status_code=303
        )

    new_serial = _get_monthly_serial_number(session, store_name, new_record_date)
    now = datetime.now()

    new_game = GameRecord(
        store_name=store_name,
        serial_number=new_serial,
        record_date=new_record_date,
        start_time=new_start_time_str,

        order_start_time=order_start_time,
        external_store_name=external_store_name,
        room_name=room_name or None,

        stakes=final_stakes or "",
        game_type=final_game_type or "",

        player_1=_normalize_text(player_1) or None,
        player_2=_normalize_text(player_2) or None,
        player_3=_normalize_text(player_3) or None,
        player_4=_normalize_text(player_4) or None,

        player_1_wechat=_normalize_text(player_1_wechat) or None,
        player_2_wechat=_normalize_text(player_2_wechat) or None,
        player_3_wechat=_normalize_text(player_3_wechat) or None,
        player_4_wechat=_normalize_text(player_4_wechat) or None,

        player_1_note=_normalize_text(player_1_note) or None,
        player_2_note=_normalize_text(player_2_note) or None,
        player_3_note=_normalize_text(player_3_note) or None,
        player_4_note=_normalize_text(player_4_note) or None,

        tags=_normalize_text(tags) or None,
        table_note=_normalize_text(table_note) or None,

        payment_method=OVERFLOW_PAYMENT_METHOD,
        room_fee=final_room_fee,

        status="formed",
        record_source=FORMED_SOURCE_OVERFLOW,
        who_did=user.display_name,

        is_payAll=False,
        wechat_pay=0.0,
        Alipay=0.0,

        created_at=now,
        updated_at=now,
        updated_by=user.display_name,
    )

    session.add(new_game)
    session.flush()

    # 溢出单参与人备注也联动待办
    sync_formed_game_note_to_handover(
        session=session,
        game=new_game,
        operator=user,
        old_noted_players_snapshot=[]
    )

    duplicate_warning_message = ""
    duplicate_hit = _find_possible_duplicate_formed_game(
        session=session,
        current_game=new_game,
        tolerance_minutes=10
    )
    if duplicate_hit:
        duplicate_warning_message = (
            f"经过新增后，疑似与{_format_duplicate_game_label(duplicate_hit)}订单为同一订单，请确认"
        )

    session.commit()

    return RedirectResponse(
        url=_build_formed_redirect_url(
            store=store_name,
            source_filter=FORMED_SOURCE_OVERFLOW,
            pay_status=pay_status,
            date_filter=date_filter,
            start_date=start_date,
            end_date=end_date,
            payment_method_filter=payment_method_filter,
            focus_game_id=new_game.id if duplicate_warning_message else None,
            duplicate_warning_message=duplicate_warning_message,
            reopen_edit_game_id=new_game.id if duplicate_warning_message else None,
        ),
        status_code=303
    )

@app.post("/formed-games/overflow/update/{game_id}")
async def update_overflow_game(
        request: Request,
        game_id: int,
        store_name: str = Form(...),
        start_time_full: str = Form(""),
        order_start_time_full: str = Form(""),

        external_store_name: str = Form(...),
        room_name: str = Form(""),

        stakes_select: str = Form(""),
        stakes_custom: Optional[str] = Form(None),
        game_type: str = Form(""),

        player_1: str = Form(""), player_2: str = Form(""),
        player_3: str = Form(""), player_4: str = Form(""),

        player_1_wechat: str = Form(""), player_2_wechat: str = Form(""),
        player_3_wechat: str = Form(""), player_4_wechat: str = Form(""),

        player_1_note: str = Form(""), player_2_note: str = Form(""),
        player_3_note: str = Form(""), player_4_note: str = Form(""),

        tags: str = Form(""),
        table_note: str = Form(""),
        room_fee: float = Form(0.0),

        pay_status: str = Form("all"),
        date_filter: str = Form("today"),
        start_date: str = Form(""),
        end_date: str = Form(""),
        payment_method_filter: str = Form("all"),

        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user),
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    game = session.get(GameRecord, game_id)
    if not game:
        raise HTTPException(status_code=404, detail="订单不存在")

    if game.status != "formed":
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_OVERFLOW,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="只有已组齐订单才能使用该编辑接口"
            ),
            status_code=303
        )

    if game.record_source != FORMED_SOURCE_OVERFLOW:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_OVERFLOW,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="该订单不是门店溢出单"
            ),
            status_code=303
        )

    store_obj = get_store_by_name(session, store_name)
    if not store_obj:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_OVERFLOW,
                error="所选归属门店不存在"
            ),
            status_code=303
        )
    if not store_obj.is_active:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_OVERFLOW,
                error="所选归属门店已停用"
            ),
            status_code=303
        )

    external_store_name = _normalize_text(external_store_name)
    if not external_store_name:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_OVERFLOW,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="外部安排门店必填"
            ),
            status_code=303
        )

    old_noted_players_snapshot = get_game_noted_players_snapshot_from_raw(
        session,
        [
            {"slot": 1, "nickname": game.player_1, "wechat_id": game.player_1_wechat, "note": game.player_1_note},
            {"slot": 2, "nickname": game.player_2, "wechat_id": game.player_2_wechat, "note": game.player_2_note},
            {"slot": 3, "nickname": game.player_3, "wechat_id": game.player_3_wechat, "note": game.player_3_note},
            {"slot": 4, "nickname": game.player_4, "wechat_id": game.player_4_wechat, "note": game.player_4_note},
        ]
    )

    if _normalize_text(start_time_full):
        new_record_date, new_start_time_str = _parse_reservation_datetime_local(start_time_full)
    else:
        new_record_date = game.record_date or date.today()
        new_start_time_str = _normalize_text(game.start_time)

    order_start_time = _parse_optional_order_start_time(order_start_time_full)
    room_name = _normalize_text(room_name)

    final_stakes = _normalize_text(stakes_custom) if _normalize_text(stakes_select) == "其他" else _normalize_text(stakes_select)
    final_game_type = _normalize_text(game_type)

    final_room_fee = room_fee or 0.0
    if final_room_fee < 0:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_OVERFLOW,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="预定金额不能小于0"
            ),
            status_code=303
        )

    slots = _normalize_player_slots(
        player_1, player_2, player_3, player_4,
        player_1_wechat, player_2_wechat, player_3_wechat, player_4_wechat
    )
    ok, msg = _validate_players_and_customer_binding(session, slots)
    if not ok:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_OVERFLOW,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=msg
            ),
            status_code=303
        )

    ok, msg = _check_brand_blacklist_for_slots(session, slots)
    if not ok:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_OVERFLOW,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=msg
            ),
            status_code=303
        )

    p1_changed = _player_changed(game.player_1, game.player_1_wechat, player_1, player_1_wechat)
    p2_changed = _player_changed(game.player_2, game.player_2_wechat, player_2, player_2_wechat)
    p3_changed = _player_changed(game.player_3, game.player_3_wechat, player_3, player_3_wechat)
    p4_changed = _player_changed(game.player_4, game.player_4_wechat, player_4, player_4_wechat)

    old_month_key = (game.record_date.year, game.record_date.month) if game.record_date else None
    new_month_key = (new_record_date.year, new_record_date.month)
    if game.store_name != store_name or old_month_key != new_month_key:
        game.serial_number = _get_monthly_serial_number(session, store_name, new_record_date)

    game.store_name = store_name
    game.record_date = new_record_date
    game.start_time = new_start_time_str
    game.order_start_time = order_start_time

    game.external_store_name = external_store_name
    game.room_name = room_name or None

    game.payment_method = OVERFLOW_PAYMENT_METHOD
    game.room_fee = final_room_fee

    game.stakes = final_stakes or ""
    game.game_type = final_game_type or ""
    game.tags = _normalize_text(tags) or None

    game.player_1 = _normalize_text(player_1) or None
    game.player_2 = _normalize_text(player_2) or None
    game.player_3 = _normalize_text(player_3) or None
    game.player_4 = _normalize_text(player_4) or None

    game.player_1_wechat = _normalize_text(player_1_wechat) or None
    game.player_2_wechat = _normalize_text(player_2_wechat) or None
    game.player_3_wechat = _normalize_text(player_3_wechat) or None
    game.player_4_wechat = _normalize_text(player_4_wechat) or None

    game.player_1_note = None if p1_changed else (_normalize_text(player_1_note) or None)
    game.player_2_note = None if p2_changed else (_normalize_text(player_2_note) or None)
    game.player_3_note = None if p3_changed else (_normalize_text(player_3_note) or None)
    game.player_4_note = None if p4_changed else (_normalize_text(player_4_note) or None)

    game.table_note = _normalize_text(table_note) or None
    game.status = "formed"
    game.record_source = FORMED_SOURCE_OVERFLOW

    game.updated_at = datetime.now()
    game.updated_by = user.display_name

    session.add(game)
    session.flush()

    sync_formed_game_note_to_handover(
        session=session,
        game=game,
        operator=user,
        old_noted_players_snapshot=old_noted_players_snapshot
    )

    duplicate_warning_message = ""
    duplicate_hit = _find_possible_duplicate_formed_game(
        session=session,
        current_game=game,
        tolerance_minutes=10
    )
    if duplicate_hit:
        duplicate_warning_message = (
            f"经过编辑后，疑似与{_format_duplicate_game_label(duplicate_hit)}订单为同一订单，请确认"
        )

    session.commit()

    if _is_ajax_request(request):
        return JSONResponse({
            "ok": True,
            "game_id": game.id,
            "message": "自主到店登记单已保存",
            "duplicate_warning_message": duplicate_warning_message or ""
        })


    return RedirectResponse(
        url=_build_formed_redirect_url(
            store=store_name,
            source_filter=FORMED_SOURCE_OVERFLOW,
            pay_status=pay_status,
            date_filter=date_filter,
            start_date=start_date,
            end_date=end_date,
            payment_method_filter=payment_method_filter,
            focus_game_id=game.id,
            duplicate_warning_message=duplicate_warning_message,
            reopen_edit_game_id=game.id if duplicate_warning_message else None,
        ),
        status_code=303
    )

@app.get("/formed-games/overflow/delete/{game_id}")
async def delete_overflow_game(
        game_id: int,
        store: str,
        pay_status: str = "all",
        date_filter: str = "today",
        start_date: str = "",
        end_date: str = "",
        payment_method_filter: str = "all",
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    game = session.get(GameRecord, game_id)
    if not game:
        raise HTTPException(status_code=404, detail="订单不存在")

    if game.record_source != FORMED_SOURCE_OVERFLOW:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store,
                source_filter=FORMED_SOURCE_OVERFLOW,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="该订单不是门店溢出单"
            ),
            status_code=303
        )

    is_admin = (user.role == "admin")
    is_owner = (game.who_did == user.display_name)

    if not (is_admin or is_owner):
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store,
                source_filter=FORMED_SOURCE_OVERFLOW,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error="无权删除该门店溢出单"
            ),
            status_code=303
        )

    session.delete(game)
    session.commit()

    return RedirectResponse(
        url=_build_formed_redirect_url(
            store=store,
            source_filter=FORMED_SOURCE_OVERFLOW,
            pay_status=pay_status,
            date_filter=date_filter,
            start_date=start_date,
            end_date=end_date,
            payment_method_filter=payment_method_filter
        ),
        status_code=303
    )


@app.get("/formed-games/export")
async def export_formed_games_excel(
        store: str,
        source_filter: str = FORMED_SOURCE_NORMAL,
        export_date_filter: str = "today",
        export_start_date: str = "",
        export_end_date: str = "",
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    source_filter = _normalize_formed_source_filter(source_filter)

    store_objs = get_store_list(session)
    store_list = [s.name for s in store_objs if s.is_active]

    if store not in store_list:
        return RedirectResponse(
            url=_build_formed_redirect_url(
                store=store,
                source_filter=source_filter,
                error="所选门店不存在或已停用"
            ),
            status_code=303
        )

    try:
        start_d, end_d = _parse_export_date_range(
            export_date_filter=export_date_filter,
            export_start_date=export_start_date,
            export_end_date=export_end_date
        )

        records = session.exec(
            select(GameRecord).where(
                GameRecord.store_name == store,
                GameRecord.status == "formed",
                GameRecord.record_source == source_filter
            )
        ).all()

        filtered_records = [
            g for g in records
            if _match_formed_game_filters(
                g,
                source_filter=source_filter,
                pay_status="all",
                date_filter=export_date_filter,
                start_date=export_start_date,
                end_date=export_end_date,
                payment_method_filter="all"
            )
        ]

        filtered_records.sort(key=_game_effective_order_dt, reverse=True)

        xml_content = _build_formed_games_excel_xml(
            records=filtered_records,
            store_name=store,
            start_d=start_d,
            end_d=end_d
        )

        filename = f"已组齐订单导出_{store}_{start_d}_{end_d}.xls"
        encoded_filename = quote(filename)

        return StreamingResponse(
            content=iter([xml_content.encode("utf-8")]),
            media_type="application/vnd.ms-excel",
            headers={
                "Content-Disposition": f"attachment; filename=export.xls; filename*=UTF-8''{encoded_filename}"
            }
        )
    except HTTPException:
        raise
    except Exception as e:
        print("=== 导出已组齐订单失败 ===")
        print(repr(e))
        raise HTTPException(status_code=500, detail=f"导出失败：{repr(e)}")


# === 自主到店登记页面 ===
@app.get("/self-arrival-register")
async def self_arrival_register_page(
        request: Request,
        store: str = "牛王庙店",
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    store_objs = get_store_list(session)
    store_list = [s.name for s in store_objs if s.is_active]

    if store not in store_list and store_list:
        store = store_list[0]

    room_list = get_active_room_list_by_store(session, store)

    records = session.exec(
        select(SelfArrivalRecord).where(
            SelfArrivalRecord.store_name == store
        ).order_by(SelfArrivalRecord.updated_at.desc(), SelfArrivalRecord.id.desc())
    ).all()

    return templates.TemplateResponse("self_arrival_register.html", {
        "request": request,
        "page_name": "self_arrival_register",
        "current_store": store,
        "store_list": store_list,
        "room_list": room_list,
        "record_list": records,
        "current_user": user
    })


@app.post("/self-arrival-register/add")
async def add_self_arrival_record(
        store_name: str = Form(...),
        room_name: str = Form(...),
        order_start_time_full: str = Form(...),
        customer_name: str = Form(...),
        customer_contact: str = Form(...),
        order_method: str = Form(...),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    # 1. 门店合法性校验
    store_obj = get_store_by_name(session, store_name)
    if not store_obj:
        return RedirectResponse(
            url=f"/self-arrival-register?store={store_name}&error=所选门店不存在",
            status_code=303
        )
    if not store_obj.is_active:
        return RedirectResponse(
            url=f"/self-arrival-register?store={store_name}&error=所选门店已停用",
            status_code=303
        )

    # 2. 包间校验
    room_name = _normalize_text(room_name)
    if not room_name:
        return RedirectResponse(
            url=f"/self-arrival-register?store={store_name}&error=预约包间必填",
            status_code=303
        )

    room_obj = session.exec(
        select(Room).where(
            Room.store_id == store_obj.id,
            Room.name == room_name,
            Room.is_active == True
        )
    ).first()

    if not room_obj:
        room_obj = session.exec(
            select(Room).where(
                Room.store_name == store_name,
                Room.name == room_name
            )
        ).first()

    if not room_obj:
        return RedirectResponse(
            url=f"/self-arrival-register?store={store_name}&error=所选包间不存在或不属于当前门店",
            status_code=303
        )

    # 3. 订单开始时间
    order_date, order_start_time = _parse_self_arrival_order_start_time(order_start_time_full)

    # 4. 月序号
    serial_number = _get_self_arrival_monthly_serial_number(session, store_name, order_date)

    # 5. 下单方式校验
    allowed_methods = [
        "美团团购",
        "抖音团购",
        "美团预定",
        "小程序端口预约",
        "代客收款下单",
        "代客验券下单"
    ]
    if order_method not in allowed_methods:
        return RedirectResponse(
            url=f"/self-arrival-register?store={store_name}&error=下单方式不合法",
            status_code=303
        )

    new_record = SelfArrivalRecord(
        store_name=store_name,
        serial_number=serial_number,
        room_name=room_name,
        order_date=order_date,
        order_start_time=order_start_time,
        customer_name=_normalize_text(customer_name),
        customer_contact=_normalize_text(customer_contact),
        order_method=order_method,
        operator_user_id=user.id,
        operator_name=user.display_name,
        created_at=datetime.now(),
        updated_at=datetime.now()
    )

    session.add(new_record)
    session.commit()

    return RedirectResponse(
        url=f"/self-arrival-register?store={store_name}&success=新增成功",
        status_code=303
    )


@app.post("/self-arrival-register/update/{record_id}")
async def update_self_arrival_record(
        record_id: int,
        store_name: str = Form(...),
        room_name: str = Form(...),
        order_start_time_full: str = Form(...),
        customer_name: str = Form(...),
        customer_contact: str = Form(...),
        order_method: str = Form(...),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    record = session.get(SelfArrivalRecord, record_id)
    if not record:
        raise HTTPException(status_code=404, detail="自主到店记录不存在")

    store_obj = get_store_by_name(session, store_name)
    if not store_obj:
        return RedirectResponse(
            url=f"/self-arrival-register?store={store_name}&error=所选门店不存在",
            status_code=303
        )

    room_name = _normalize_text(room_name)
    if not room_name:
        return RedirectResponse(
            url=f"/self-arrival-register?store={store_name}&error=预约包间必填",
            status_code=303
        )

    room_obj = session.exec(
        select(Room).where(
            Room.store_id == store_obj.id,
            Room.name == room_name,
            Room.is_active == True
        )
    ).first()

    if not room_obj:
        room_obj = session.exec(
            select(Room).where(
                Room.store_name == store_name,
                Room.name == room_name
            )
        ).first()

    if not room_obj:
        return RedirectResponse(
            url=f"/self-arrival-register?store={store_name}&error=所选包间不存在或不属于当前门店",
            status_code=303
        )

    allowed_methods = [
        "美团团购",
        "抖音团购",
        "美团预定",
        "小程序端口预约",
        "代客收款下单",
        "代客验券下单"
    ]
    if order_method not in allowed_methods:
        return RedirectResponse(
            url=f"/self-arrival-register?store={store_name}&error=下单方式不合法",
            status_code=303
        )

    order_date, order_start_time = _parse_self_arrival_order_start_time(order_start_time_full)

    # 如果跨月了，重新生成该月序号；同月则保留原序号
    old_month = (record.order_date.year, record.order_date.month)
    new_month = (order_date.year, order_date.month)
    old_store = record.store_name
    new_store = store_name

    if old_month != new_month or old_store != new_store:
        record.serial_number = _get_self_arrival_monthly_serial_number(session, store_name, order_date)

    record.store_name = store_name
    record.room_name = room_name
    record.order_date = order_date
    record.order_start_time = order_start_time
    record.customer_name = _normalize_text(customer_name)
    record.customer_contact = _normalize_text(customer_contact)
    record.order_method = order_method

    # 按你的规则：谁点确定，操作人就是谁
    record.operator_user_id = user.id
    record.operator_name = user.display_name
    record.updated_at = datetime.now()

    session.add(record)
    session.commit()

    return RedirectResponse(
        url=f"/self-arrival-register?store={store_name}&success=修改成功",
        status_code=303
    )


@app.get("/self-arrival-register/delete/{record_id}")
async def delete_self_arrival_record(
        record_id: int,
        store: Optional[str] = None,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    record = session.get(SelfArrivalRecord, record_id)
    if not record:
        raise HTTPException(status_code=404, detail="自主到店记录不存在")

    target_store = store or record.store_name

    session.delete(record)
    session.commit()

    return RedirectResponse(
        url=f"/self-arrival-register?store={target_store}&success=删除成功",
        status_code=303
    )

@app.post("/update-formed-game/{game_id}")
async def update_formed_game(
        request: Request,

        game_id: int,
        store_name: str = Form(...),
        start_time_full: str = Form(...),
        order_start_time_full: Optional[str] = Form(""),

        stakes_select: str = Form(...),
        stakes_custom: Optional[str] = Form(None),
        game_type: str = Form(...),

        player_1: str = Form(""), player_2: str = Form(""),
        player_3: str = Form(""), player_4: str = Form(""),

        player_1_wechat: str = Form(""), player_2_wechat: str = Form(""),
        player_3_wechat: str = Form(""), player_4_wechat: str = Form(""),

        player_1_note: str = Form(""),
        player_2_note: str = Form(""),
        player_3_note: str = Form(""),
        player_4_note: str = Form(""),
        table_note: str = Form(""),

        room_name: str = Form(...),

        payment_method: Optional[str] = Form(""),
        room_fee: float = Form(0),

        tags: str = Form(""),

        source_filter: str = Form(FORMED_SOURCE_NORMAL),
        pay_status: str = Form("all"),
        date_filter: str = Form("today"),
        start_date: str = Form(""),
        end_date: str = Form(""),
        payment_method_filter: str = Form("all"),

        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user),
):
    if not user:
        if _is_ajax_request(request):
            return JSONResponse(
                {"ok": False, "message": "未登录或登录已过期"},
                status_code=401
            )
        return RedirectResponse(url="/login", status_code=303)

    game = session.get(GameRecord, game_id)
    if not game:
        raise HTTPException(status_code=404, detail="Game not found")

    if game.status != "formed":
        msg = "只有已组齐订单才能使用该编辑接口"
        return _ajax_or_redirect_error(
            request,
            message=msg,
            redirect_url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_NORMAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=msg
            )
        )

    if game.record_source == FORMED_SOURCE_SELF_ARRIVAL:
        msg = "自主到店登记单请使用专用编辑入口"
        return _ajax_or_redirect_error(
            request,
            message=msg,
            redirect_url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_SELF_ARRIVAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=msg
            )
        )

    if game.record_source == FORMED_SOURCE_OVERFLOW:
        msg = "门店溢出单请使用专用编辑入口"
        return _ajax_or_redirect_error(
            request,
            message=msg,
            redirect_url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_OVERFLOW,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=msg
            )
        )

    old_noted_players_snapshot = get_game_noted_players_snapshot_from_raw(
        session,
        [
            {
                "slot": 1,
                "nickname": game.player_1,
                "wechat_id": game.player_1_wechat,
                "note": game.player_1_note
            },
            {
                "slot": 2,
                "nickname": game.player_2,
                "wechat_id": game.player_2_wechat,
                "note": game.player_2_note
            },
            {
                "slot": 3,
                "nickname": game.player_3,
                "wechat_id": game.player_3_wechat,
                "note": game.player_3_note
            },
            {
                "slot": 4,
                "nickname": game.player_4,
                "wechat_id": game.player_4_wechat,
                "note": game.player_4_note
            },
        ]
    )

    store_obj = get_store_by_name(session, store_name)
    if not store_obj:
        msg = "所选门店不存在"
        return _ajax_or_redirect_error(
            request,
            message=msg,
            redirect_url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_NORMAL,
                error=msg
            )
        )

    if not store_obj.is_active:
        msg = "所选门店已停用"
        return _ajax_or_redirect_error(
            request,
            message=msg,
            redirect_url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_NORMAL,
                error=msg
            )
        )

    room_name = _normalize_text(room_name)
    if not room_name:
        msg = "已组齐编辑保存时包间必填"
        return _ajax_or_redirect_error(
            request,
            message=msg,
            redirect_url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_NORMAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=msg
            )
        )

    room_obj = session.exec(
        select(Room).where(
            Room.store_id == store_obj.id,
            Room.name == room_name,
            Room.is_active == True
        )
    ).first()

    if not room_obj:
        room_obj = session.exec(
            select(Room).where(
                Room.store_name == store_name,
                Room.name == room_name
            )
        ).first()

    if not room_obj:
        msg = "所选包间不存在或不属于当前门店"
        return _ajax_or_redirect_error(
            request,
            message=msg,
            redirect_url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_NORMAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=msg
            )
        )

    slots = _normalize_player_slots(
        player_1, player_2, player_3, player_4,
        player_1_wechat, player_2_wechat, player_3_wechat, player_4_wechat
    )

    ok, msg = _validate_players_and_customer_binding(session, slots)
    if not ok:
        return _ajax_or_redirect_error(
            request,
            message=msg,
            redirect_url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_NORMAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=msg
            )
        )

    ok, msg = _check_brand_blacklist_for_slots(session, slots)
    if not ok:
        return _ajax_or_redirect_error(
            request,
            message=msg,
            redirect_url=_build_formed_redirect_url(
                store=store_name,
                source_filter=FORMED_SOURCE_NORMAL,
                pay_status=pay_status,
                date_filter=date_filter,
                start_date=start_date,
                end_date=end_date,
                payment_method_filter=payment_method_filter,
                error=msg
            )
        )

    new_record_date, new_start_time_str = _parse_reservation_datetime_local(start_time_full)
    final_stakes = _normalize_text(stakes_custom) if stakes_select == "其他" else _normalize_text(stakes_select)

    p1_changed = _player_changed(game.player_1, game.player_1_wechat, player_1, player_1_wechat)
    p2_changed = _player_changed(game.player_2, game.player_2_wechat, player_2, player_2_wechat)
    p3_changed = _player_changed(game.player_3, game.player_3_wechat, player_3, player_3_wechat)
    p4_changed = _player_changed(game.player_4, game.player_4_wechat, player_4, player_4_wechat)

    old_month_key = (game.record_date.year, game.record_date.month) if game.record_date else None
    new_month_key = (new_record_date.year, new_record_date.month)
    if game.store_name != store_name or old_month_key != new_month_key:
        game.serial_number = _get_monthly_serial_number(session, store_name, new_record_date)

    game.store_name = store_name
    game.record_date = new_record_date
    game.start_time = new_start_time_str

    game.order_start_time = _parse_optional_order_start_time(order_start_time_full)

    game.room_name = room_name
    game.payment_method = _normalize_text(payment_method) or None
    game.room_fee = room_fee or 0.0

    game.stakes = final_stakes
    game.game_type = _normalize_text(game_type)
    game.tags = _normalize_text(tags)

    game.player_1 = _normalize_text(player_1)
    game.player_2 = _normalize_text(player_2)
    game.player_3 = _normalize_text(player_3)
    game.player_4 = _normalize_text(player_4)

    game.player_1_wechat = _normalize_text(player_1_wechat)
    game.player_2_wechat = _normalize_text(player_2_wechat)
    game.player_3_wechat = _normalize_text(player_3_wechat)
    game.player_4_wechat = _normalize_text(player_4_wechat)

    game.player_1_note = None if p1_changed else (_normalize_text(player_1_note) or None)
    game.player_2_note = None if p2_changed else (_normalize_text(player_2_note) or None)
    game.player_3_note = None if p3_changed else (_normalize_text(player_3_note) or None)
    game.player_4_note = None if p4_changed else (_normalize_text(player_4_note) or None)

    game.table_note = _normalize_text(table_note) or None

    game.updated_at = datetime.now()
    game.updated_by = user.display_name

    session.add(game)
    session.flush()

    sync_formed_game_note_to_handover(
        session=session,
        game=game,
        operator=user,
        old_noted_players_snapshot=old_noted_players_snapshot
    )

    duplicate_warning_message = ""
    duplicate_hit = _find_possible_duplicate_formed_game(
        session=session,
        current_game=game,
        tolerance_minutes=10
    )
    if duplicate_hit:
        duplicate_warning_message = (
            f"经过编辑后，疑似与{_format_duplicate_game_label(duplicate_hit)}订单为同一订单，请确认"
        )

    session.commit()

    if _is_ajax_request(request):
        return JSONResponse({
            "ok": True,
            "game_id": game.id,
            "message": "已组齐订单已保存",
            "duplicate_warning_message": duplicate_warning_message or ""
        })

    return RedirectResponse(
        url=_build_formed_redirect_url(
            store=store_name,
            source_filter=FORMED_SOURCE_NORMAL,
            pay_status=pay_status,
            date_filter=date_filter,
            start_date=start_date,
            end_date=end_date,
            payment_method_filter=payment_method_filter,
            focus_game_id=game.id,
            duplicate_warning_message=duplicate_warning_message,
            reopen_edit_game_id=game.id if duplicate_warning_message else None,
        ),
        status_code=303
    )

@app.get("/game-detail/{game_id}")
async def get_game_detail(
        game_id: int,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        raise HTTPException(status_code=401, detail="请先登录")

    game = session.get(GameRecord, game_id)
    if not game:
        raise HTTPException(status_code=404, detail="牌局不存在")

    def _fmt_dt(dt_val):
        if not dt_val:
            return ""
        if isinstance(dt_val, datetime):
            return dt_val.strftime("%Y-%m-%d %H:%M:%S")
        return str(dt_val)

    def _relative_dt(dt_val):
        if not dt_val or not isinstance(dt_val, datetime):
            return ""
        diff = datetime.now() - dt_val
        secs = int(diff.total_seconds())
        if secs < 60:
            return f"{secs}秒前"
        if secs < 3600:
            return f"{secs // 60}分钟前"
        if secs < 86400:
            return f"{secs // 3600}小时前"
        return f"{secs // 86400}天前"

    players = []
    for idx in range(1, 5):
        name = getattr(game, f"player_{idx}", None)
        wechat = getattr(game, f"player_{idx}_wechat", None)
        note = getattr(game, f"player_{idx}_note", None)
        if _normalize_text(name) or _normalize_text(wechat):
            players.append({
                "index": idx,
                "name": name or "",
                "wechat": wechat or "",
                "note": note or ""
            })

    remaining = (game.room_fee or 0) - (game.wechat_pay or 0) - (game.Alipay or 0)
    actual_received = round((game.wechat_pay or 0) + (game.Alipay or 0), 2)
    profit_amount = round(actual_received - (game.room_fee or 0), 2)

    source_label = (
        "门店溢出单" if game.record_source == FORMED_SOURCE_OVERFLOW
        else "自主到店登记单" if game.record_source == FORMED_SOURCE_SELF_ARRIVAL
        else "常规已组齐订单"
    )

    return JSONResponse({
        "id": game.id,
        "store_name": game.store_name,
        "external_store_name": game.external_store_name or "",
        "serial_number": game.serial_number,
        "status": game.status,

        "reservation_date": str(game.record_date) if game.record_date else "",
        "reservation_time": game.start_time or "",
        "order_start_time": game.order_start_time or "",

        "room_name": game.room_name or "",
        "stakes": game.stakes or "",
        "game_type": game.game_type or "",

        "tags": game.tags or "",
        "table_note": game.table_note or "",

        "payment_method": game.payment_method or "",
        "room_fee": game.room_fee or 0,
        "is_payAll": bool(game.is_payAll),
        "wechat_pay": game.wechat_pay or 0,
        "Alipay": game.Alipay or 0,
        "remaining": remaining,
        "actual_received": actual_received,
        "profit_amount": profit_amount,

        "who_did": game.who_did or "",

        "created_at": _fmt_dt(game.created_at),
        "updated_at": _fmt_dt(game.updated_at),
        "updated_at_relative": _relative_dt(game.updated_at),
        "updated_by": game.updated_by or "",

        "record_source": game.record_source or FORMED_SOURCE_NORMAL,
        "source_label": source_label,

        "players": players
    })


# === 顾客管理页面接口 (GET) ===
@app.get("/customers")
async def read_customers(
        request: Request,
        store: str = "牛王庙店",
        search_query: str = "",
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    # 1. 门店列表
    store_objs = get_store_list(session)
    store_list = [s.name for s in store_objs if s.is_active]

    if store not in store_list and store_list:
        store = store_list[0]

    keyword = (search_query or "").strip()

    # 2. 先按关键词查顾客
    query = select(Customer)
    if keyword:
        query = query.where(or_(
            Customer.nickname.contains(keyword),
            Customer.wechat_id.contains(keyword)
        ))

    customers = session.exec(query).all()

    # 3. 数据组装
    customer_data_list = []

    for cust in customers:
        links = session.exec(
            select(CustomerStoreLink).where(CustomerStoreLink.customer_id == cust.id)
        ).all()
        visited_store_names = [l.store_name for l in links]

        # 关键改动：
        # - 无搜索词时：仍按当前门店隔离展示
        # - 有搜索词时：放开为全域搜索，不再按当前门店过滤
        if not keyword:
            if store not in visited_store_names:
                continue

        # 统计当前门店的到店次数（即使是全域搜索，也仍显示“当前门店次数”）
        game_query = select(GameRecord).where(
            GameRecord.status == "formed",
            GameRecord.store_name == store,
            or_(
                GameRecord.player_1_wechat == cust.wechat_id,
                GameRecord.player_2_wechat == cust.wechat_id,
                GameRecord.player_3_wechat == cust.wechat_id,
                GameRecord.player_4_wechat == cust.wechat_id
            )
        )
        visit_count = len(session.exec(game_query).all())

        customer_data_list.append({
            "id": cust.id,
            "nickname": cust.nickname,
            "wechat_id": cust.wechat_id,
            "gender": cust.gender,
            "visited_stores": ", ".join(visited_store_names),
            "last_visit_date": cust.last_visit_date,
            "guarantee_deposit": cust.guarantee_deposit,
            "current_store_visit_count": visit_count,
            "is_loss": cust.is_loss
        })

    # 搜索时，给更直观的排序
    if keyword:
        customer_data_list.sort(
            key=lambda x: (
                0 if (x["nickname"] or "") == keyword else 1,
                0 if (x["wechat_id"] or "") == keyword else 1,
                -(x["current_store_visit_count"] or 0),
                x["id"]
            )
        )

    return templates.TemplateResponse("customers.html", {
        "request": request,
        "page_name": "customers",
        "current_store": store,
        "store_list": store_list,
        "customer_list": customer_data_list,
        "search_query": search_query,
        "current_user": user
    })


# === 新增顾客接口 (POST) ===
@app.post("/add-customer")
async def add_customer(
        nickname: str = Form(...),
        wechat_id: str = Form(...),
        gender: str = Form(...),
        store_name: str = Form(...),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    today = date.today()

    # 1. 检查微信号是否已存在
    existing_cust = session.exec(
        select(Customer).where(Customer.wechat_id == wechat_id)
    ).first()

    if existing_cust:
        return RedirectResponse(
            url=f"/customers?store={store_name}&error=该微信号已存在",
            status_code=303
        )

    # 2. 创建新顾客
    # 手动录入但未组局：到店次数=0，因此 last_visit_date 应为空
    new_cust = Customer(
        nickname=nickname,
        wechat_id=wechat_id,
        gender=gender,
        guarantee_deposit=0.0,
        is_loss=False,
        last_visit_date=None,
        created_at=today
    )
    session.add(new_cust)
    session.commit()
    session.refresh(new_cust)

    # 3. 创建门店关联
    # 手动录入即进入该门店顾客池，但未组局，所以 last_visit_at_store 为空
    new_link = CustomerStoreLink(
        customer_id=new_cust.id,
        store_name=store_name,
        created_at=today,
        last_visit_at_store=None
    )
    session.add(new_link)
    session.commit()

    return RedirectResponse(url=f"/customers?store={store_name}", status_code=303)



# === 获取顾客详情 ===
@app.get("/customer/{customer_id}")
async def get_customer_details(
        customer_id: int,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return {"error": "请先登录"}

    cust = session.get(Customer, customer_id)
    if not cust:
        return {"error": "顾客不存在"}

    # 1. 当前已绑定门店（以 CustomerStoreLink 为准）
    link_rows = session.exec(
        select(CustomerStoreLink).where(
            CustomerStoreLink.customer_id == cust.id
        )
    ).all()

    stores_data = []
    for link in link_rows:
        visit_count = get_customer_store_visit_count(session, cust, link.store_name)
        stores_data.append({
            "id": link.id,
            "name": link.store_name,
            "count": visit_count,
            "created_at": str(link.created_at) if link.created_at else "",
            "last_visit_at_store": str(link.last_visit_at_store) if link.last_visit_at_store else ""
        })

    # 排序：先按创建时间，再按id
    stores_data.sort(key=lambda x: (x["created_at"], x["id"]))

    # 2. 可供新增绑定的门店选项（= 启用门店 - 已绑定门店）
    active_store_names = get_active_store_name_list(session)
    bound_store_names = {item["name"] for item in stores_data}
    available_store_options = [s for s in active_store_names if s not in bound_store_names]

    # 3. 黑名单
    blacklist_records = session.exec(
        select(Blacklist).where(Blacklist.initiator_id == cust.id)
    ).all()

    blacklist_data = []
    for record in blacklist_records:
        target = session.get(Customer, record.target_id)
        if target:
            blacklist_data.append({
                "id": record.id,
                "target_name": target.nickname,
                "target_wechat": target.wechat_id,
                "reason": record.reason
            })

    # 4. 同场次记录
    play_records = session.exec(
        select(PlayFrequency).where(
            or_(
                PlayFrequency.player_1_id == cust.id,
                PlayFrequency.player_2_id == cust.id
            )
        )
    ).all()

    play_data = []
    for record in play_records:
        partner_id = record.player_2_id if record.player_1_id == cust.id else record.player_1_id
        partner = session.get(Customer, partner_id)
        if partner:
            play_data.append({
                "partner_name": partner.nickname,
                "count": record.count
            })

    # 5. 人情维护记录（未删除）
    maintenance_records = session.exec(
        select(MaintenanceRecord).where(
            MaintenanceRecord.customer_id == cust.id,
            MaintenanceRecord.is_deleted == False
        ).order_by(MaintenanceRecord.record_date.desc(), MaintenanceRecord.id.desc())
    ).all()

    maintenance_data = []
    for rec in maintenance_records:
        maintenance_data.append({
            "id": rec.id,
            "date": str(rec.record_date),
            "gift_name": rec.gift_name,
            "amount": rec.amount,
            "jump_url": f"/maintenance-records?store={rec.store_name}&year={rec.record_date.year}&month={rec.record_date.month}&focus_record_id={rec.id}"
        })

    return {
        "info": {
            "id": cust.id,
            "nickname": cust.nickname,
            "wechat_id": cust.wechat_id,
            "gender": cust.gender,
            "guarantee_deposit": cust.guarantee_deposit,
            "is_loss": cust.is_loss,
            "last_visit_date": str(cust.last_visit_date) if cust.last_visit_date else "",
            "created_at": str(cust.created_at) if cust.created_at else ""
        },
        "stores": stores_data,
        "available_store_options": available_store_options,
        "blacklist": blacklist_data,
        "play_frequency": play_data,
        "maintenance_records": maintenance_data,
        "can_manage_store_links": (user.role == "admin" or "operator")
    }


@app.post("/customer/{customer_id}/store-link/add")
async def add_customer_store_link(
        customer_id: int,
        store_name: str = Form(...),
        current_store: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    # # 建议权限：仅 admin 可操作
    # if user.role != "admin""operator":
    #     return RedirectResponse(
    #         url=f"/customers?store={current_store or '牛王庙店'}&error=无权限，仅超级管理员可新增顾客门店绑定",
    #         status_code=303
    #     )

    cust = session.get(Customer, customer_id)
    if not cust:
        raise HTTPException(status_code=404, detail="顾客不存在")

    store_name = (store_name or "").strip()
    if not store_name:
        return RedirectResponse(
            url=f"/customers?store={current_store or '牛王庙店'}&error=门店不能为空",
            status_code=303
        )

    active_store_names = get_active_store_name_list(session)
    if store_name not in active_store_names:
        return RedirectResponse(
            url=f"/customers?store={current_store or '牛王庙店'}&error=所选门店不存在或未启用",
            status_code=303
        )

    exists = session.exec(
        select(CustomerStoreLink).where(
            CustomerStoreLink.customer_id == customer_id,
            CustomerStoreLink.store_name == store_name
        )
    ).first()

    if exists:
        return RedirectResponse(
            url=f"/customers?store={current_store or store_name}&error=该顾客已绑定此门店",
            status_code=303
        )

    new_link = CustomerStoreLink(
        customer_id=customer_id,
        store_name=store_name,
        created_at=date.today(),
        last_visit_at_store=None
    )
    session.add(new_link)
    session.commit()

    return RedirectResponse(
        url=f"/customers?store={current_store or store_name}&success=顾客门店绑定新增成功",
        status_code=303
    )


@app.post("/customer/store-link/{link_id}/update")
async def update_customer_store_link(
        link_id: int,
        new_store_name: str = Form(...),
        current_store: str = Form(""),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    # if user.role != "admin":
    #     return RedirectResponse(
    #         url=f"/customers?store={current_store or '牛王庙店'}&error=无权限，仅超级管理员可修改顾客门店绑定",
    #         status_code=303
    #     )

    link = session.get(CustomerStoreLink, link_id)
    if not link:
        raise HTTPException(status_code=404, detail="顾客门店绑定记录不存在")

    new_store_name = (new_store_name or "").strip()
    if not new_store_name:
        return RedirectResponse(
            url=f"/customers?store={current_store or '牛王庙店'}&error=新门店不能为空",
            status_code=303
        )

    active_store_names = get_active_store_name_list(session)
    if new_store_name not in active_store_names:
        return RedirectResponse(
            url=f"/customers?store={current_store or '牛王庙店'}&error=目标门店不存在或未启用",
            status_code=303
        )

    # 不允许改成和自己重复
    duplicate = session.exec(
        select(CustomerStoreLink).where(
            CustomerStoreLink.customer_id == link.customer_id,
            CustomerStoreLink.store_name == new_store_name,
            CustomerStoreLink.id != link.id
        )
    ).first()

    if duplicate:
        return RedirectResponse(
            url=f"/customers?store={current_store or new_store_name}&error=该顾客已绑定目标门店，不能重复修改",
            status_code=303
        )

    link.store_name = new_store_name
    session.add(link)
    session.commit()

    return RedirectResponse(
        url=f"/customers?store={current_store or new_store_name}&success=顾客门店绑定修改成功",
        status_code=303
    )


@app.get("/customer/store-link/{link_id}/delete")
async def delete_customer_store_link(
        link_id: int,
        current_store: str = "",
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    # if user.role != "admin":
    #     return RedirectResponse(
    #         url=f"/customers?store={current_store or '牛王庙店'}&error=无权限，仅超级管理员可撤销顾客门店绑定",
    #         status_code=303
    #     )

    link = session.get(CustomerStoreLink, link_id)
    if not link:
        raise HTTPException(status_code=404, detail="顾客门店绑定记录不存在")

    all_links = session.exec(
        select(CustomerStoreLink).where(CustomerStoreLink.customer_id == link.customer_id)
    ).all()

    if len(all_links) <= 1:
        return RedirectResponse(
            url=f"/customers?store={current_store or link.store_name}&error=该顾客至少要保留一个绑定门店，不能撤销最后一个",
            status_code=303
        )

    session.delete(link)
    session.commit()

    return RedirectResponse(
        url=f"/customers?store={current_store or link.store_name}&success=顾客门店绑定已撤销",
        status_code=303
    )

# === 更新顾客基本信息接口 (POST) ===
@app.post("/update-customer/{customer_id}")
async def update_customer(
        customer_id: int,
        nickname: str = Form(...),
        wechat_id: str = Form(...),
        gender: str = Form(...),
        guarantee_deposit: float = Form(0.0),
        store_name: str = Form(...),  # 为了重定向回正确的页面
        session: Session = Depends(get_session)
):
    cust = session.get(Customer, customer_id)
    if not cust: raise HTTPException(status_code=404)

    cust.nickname = nickname
    cust.wechat_id = wechat_id
    cust.gender = gender
    cust.guarantee_deposit = guarantee_deposit

    session.add(cust)
    session.commit()
    return RedirectResponse(url=f"/customers?store={store_name}", status_code=303)


# === 添加黑名单接口 (POST) ===
@app.post("/api/add-blacklist")
async def add_blacklist(
        initiator_id: int = Form(...),
        target_wechat: str = Form(...),  # 通过微信号查找目标
        reason: str = Form(...),
        session: Session = Depends(get_session)
):
    # 1. 找目标
    target = session.exec(select(Customer).where(Customer.wechat_id == target_wechat)).first()

    if not target:
        return {"success": False, "msg": "未找到该微信号对应的顾客"}

    if target.id == initiator_id:
        return {"success": False, "msg": "不能拉黑自己"}

    # 2. 检查是否已存在
    exists = session.exec(select(Blacklist).where(
        Blacklist.initiator_id == initiator_id,
        Blacklist.target_id == target.id
    )).first()

    if exists:
        return {"success": False, "msg": "该顾客已在黑名单中"}

    # 3. 创建记录
    new_bl = Blacklist(initiator_id=initiator_id, target_id=target.id, reason=reason)
    session.add(new_bl)
    session.commit()
    return {"success": True, "msg": "添加成功"}

# ===  删除黑名单接口 (DELETE) ===
@app.delete("/api/delete-blacklist/{record_id}")
async def delete_blacklist(record_id: int, session: Session = Depends(get_session)):
    record = session.get(Blacklist, record_id)
    if record:
        session.delete(record)
        session.commit()
    return {"success": True}


# === 检查黑名单冲突接口 ===
@app.post("/api/check-game-conflicts")
async def check_game_conflicts(
        p1_wx: str = Form(""), p2_wx: str = Form(""),
        p3_wx: str = Form(""), p4_wx: str = Form(""),
        session: Session = Depends(get_session)
):
    # 1. 收集微信号并映射到位置索引 (1, 2, 3, 4)
    # 格式: { "wx_id": index }
    players_map = {}
    if p1_wx: players_map[p1_wx] = 1
    if p2_wx: players_map[p2_wx] = 2
    if p3_wx: players_map[p3_wx] = 3
    if p4_wx: players_map[p4_wx] = 4

    wx_list = list(players_map.keys())
    if len(wx_list) < 2:
        return {"has_conflict": False}  # 少于2人不可能有冲突

    # 2. 查找这些微信号对应的 Customer 实体 (获取 ID)
    customers = session.exec(select(Customer).where(Customer.wechat_id.in_(wx_list))).all()
    # 建立映射: id -> (nickname, wechat_id)
    cust_id_map = {c.id: c for c in customers}
    # 建立映射: wechat_id -> id
    wx_to_id = {c.wechat_id: c.id for c in customers}

    conflicts = []
    conflict_indices = []

    # 3. 两两检查黑名单
    # 遍历所有找到的顾客ID
    found_ids = list(cust_id_map.keys())

    # 查询黑名单表：发起人 和 目标 都在这群人里
    blacklist_records = session.exec(select(Blacklist).where(
        Blacklist.initiator_id.in_(found_ids),
        Blacklist.target_id.in_(found_ids)
    )).all()

    for rec in blacklist_records:
        initiator = cust_id_map[rec.initiator_id]
        target = cust_id_map[rec.target_id]

        # 记录冲突描述
        msg = f"【{initiator.nickname}】不想跟【{target.nickname}】打，理由：{rec.reason}"
        conflicts.append(msg)

        # 记录冲突的位置序号 (1-4)
        conflict_indices.append(players_map[initiator.wechat_id])
        conflict_indices.append(players_map[target.wechat_id])

    # 去重位置索引
    conflict_indices = list(set(conflict_indices))

    return {
        "has_conflict": len(conflicts) > 0,
        "messages": conflicts,
        "indices": conflict_indices  # 返回 [1, 3] 代表玩家1和玩家3冲突
    }


class BlacklistCheckPlayer(BaseModel):
    index: int
    nickname: Optional[str] = ""
    wechat_id: Optional[str] = ""


class BlacklistCheckPayload(BaseModel):
    players: List[BlacklistCheckPlayer]
    store_name: Optional[str] = ""


@app.post("/api/check-blacklist-conflict")
async def check_blacklist_conflict(
        payload: BlacklistCheckPayload,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    适配未组齐 V2 前端：
    接收 JSON:
    {
      "players": [
        {"index": 1, "nickname": "...", "wechat_id": "..."},
        ...
      ],
      "store_name": "牛王庙店"
    }

    返回：
    {
      "conflicts": [
        {
          "index": 1,
          "nickname": "...",
          "wechat_id": "...",
          "reason": "..."
        }
      ]
    }
    """
    if not user:
        raise HTTPException(status_code=401, detail="请先登录")

    players = payload.players or []
    wx_to_player = {}
    wx_list = []

    for p in players:
        wx = (p.wechat_id or "").strip()
        if not wx:
            continue
        wx_to_player[wx] = {
            "index": p.index,
            "nickname": (p.nickname or "").strip(),
            "wechat_id": wx
        }
        wx_list.append(wx)

    # 少于2个有效微信号，不可能有黑名单冲突
    if len(wx_list) < 2:
        return JSONResponse({"conflicts": []})

    # 查 Customer
    customers = session.exec(
        select(Customer).where(Customer.wechat_id.in_(wx_list))
    ).all()

    if len(customers) < 2:
        return JSONResponse({"conflicts": []})

    cust_id_map = {c.id: c for c in customers}
    wx_to_customer = {c.wechat_id: c for c in customers}
    found_ids = list(cust_id_map.keys())

    blacklist_records = session.exec(
        select(Blacklist).where(
            Blacklist.initiator_id.in_(found_ids),
            Blacklist.target_id.in_(found_ids)
        )
    ).all()

    conflict_map = {}

    for rec in blacklist_records:
        initiator = cust_id_map.get(rec.initiator_id)
        target = cust_id_map.get(rec.target_id)
        if not initiator or not target:
            continue

        init_wx = initiator.wechat_id
        target_wx = target.wechat_id

        if init_wx in wx_to_player:
            conflict_map[init_wx] = {
                "index": wx_to_player[init_wx]["index"],
                "nickname": wx_to_player[init_wx]["nickname"] or initiator.nickname or "",
                "wechat_id": init_wx,
                "reason": f"【{initiator.nickname}】不想跟【{target.nickname}】打，理由：{rec.reason or '未填写'}"
            }

        if target_wx in wx_to_player:
            conflict_map[target_wx] = {
                "index": wx_to_player[target_wx]["index"],
                "nickname": wx_to_player[target_wx]["nickname"] or target.nickname or "",
                "wechat_id": target_wx,
                "reason": f"【{initiator.nickname}】不想跟【{target.nickname}】打，理由：{rec.reason or '未填写'}"
            }

    conflicts = sorted(conflict_map.values(), key=lambda x: x["index"])
    return JSONResponse({"conflicts": conflicts})

# =========== 检查品牌黑名单 ==========
@app.post("/api/check-brand-blacklist")
async def check_brand_blacklist(
        payload: BlacklistCheckPayload,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    检查当前参与人中是否有人命中品牌黑名单。
    返回：
    {
      "conflicts": [
        {
          "index": 1,
          "nickname": "张三",
          "wechat_id": "wx123",
          "reason": "欠款未结清"
        }
      ]
    }
    """
    if not user:
        raise HTTPException(status_code=401, detail="请先登录")

    conflicts = []

    for p in (payload.players or []):
        nickname = (p.nickname or "").strip()
        wechat_id = (p.wechat_id or "").strip()

        entry = _get_active_brand_blacklist_entry_by_identity(
            session=session,
            nickname=nickname,
            wechat_id=wechat_id
        )
        if not entry:
            continue

        conflicts.append({
            "index": p.index,
            "nickname": nickname or entry.nickname or "",
            "wechat_id": wechat_id or entry.wechat_id or "",
            "reason": entry.reason or "未填写原因"
        })

    conflicts.sort(key=lambda x: x["index"])
    return JSONResponse({"conflicts": conflicts})


# ======== 品牌黑名单页面接口 ======
@app.get("/brand-blacklist")
async def brand_blacklist_page(
        request: Request,
        keyword: str = "",
        status_filter: str = "active",   # active / revoked / all
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    stmt = select(BrandBlacklistEntry)

    kw = (keyword or "").strip()
    if kw:
        stmt = stmt.where(or_(
            BrandBlacklistEntry.nickname.contains(kw),
            BrandBlacklistEntry.wechat_id.contains(kw),
            BrandBlacklistEntry.reason.contains(kw)
        ))

    if status_filter == "active":
        stmt = stmt.where(BrandBlacklistEntry.is_active == True)
    elif status_filter == "revoked":
        stmt = stmt.where(BrandBlacklistEntry.is_active == False)

    records = session.exec(
        stmt.order_by(
            BrandBlacklistEntry.is_active.desc(),
            BrandBlacklistEntry.updated_at.desc(),
            BrandBlacklistEntry.id.desc()
        )
    ).all()

    return templates.TemplateResponse("brand_blacklist.html", {
        "request": request,
        "page_name": "brand_blacklist",
        "current_user": user,
        "record_list": records,
        "keyword": keyword,
        "status_filter": status_filter
    })


@app.post("/brand-blacklist/add")
async def add_brand_blacklist(
        nickname: str = Form(...),
        wechat_id: str = Form(...),
        reason: str = Form(...),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)
    if user.role != "admin":
        return RedirectResponse(url="/brand-blacklist?error=无权限，仅超级管理员可新增", status_code=303)

    nickname = _normalize_text(nickname)
    wechat_id = _normalize_text(wechat_id)
    reason = _normalize_text(reason)

    if not nickname:
        return RedirectResponse(url="/brand-blacklist?error=昵称不能为空", status_code=303)
    if not wechat_id:
        return RedirectResponse(url="/brand-blacklist?error=微信号不能为空", status_code=303)
    if not reason:
        return RedirectResponse(url="/brand-blacklist?error=理由不能为空", status_code=303)

    exists = session.exec(
        select(BrandBlacklistEntry).where(BrandBlacklistEntry.wechat_id == wechat_id)
    ).first()

    if exists and exists.is_active:
        return RedirectResponse(url="/brand-blacklist?error=该微信号已在品牌黑名单中", status_code=303)

    now = datetime.now()

    if exists and not exists.is_active:
        # 撤销后重新启用，按“恢复”处理
        exists.nickname = nickname
        exists.reason = reason
        exists.is_active = True
        exists.updated_by_user_id = user.id
        exists.updated_by_name = user.display_name
        exists.updated_at = now
        exists.revoked_at = None
        session.add(exists)
        session.commit()
        return RedirectResponse(url="/brand-blacklist?success=已重新启用该品牌黑名单记录", status_code=303)

    new_entry = BrandBlacklistEntry(
        nickname=nickname,
        wechat_id=wechat_id,
        reason=reason,
        is_active=True,
        created_by_user_id=user.id,
        created_by_name=user.display_name,
        updated_by_user_id=user.id,
        updated_by_name=user.display_name,
        created_at=now,
        updated_at=now,
        revoked_at=None
    )
    session.add(new_entry)
    session.commit()

    return RedirectResponse(url="/brand-blacklist?success=新增成功", status_code=303)


@app.post("/brand-blacklist/update/{record_id}")
async def update_brand_blacklist(
        record_id: int,
        nickname: str = Form(...),
        wechat_id: str = Form(...),
        reason: str = Form(...),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)
    if user.role != "admin":
        return RedirectResponse(url="/brand-blacklist?error=无权限，仅超级管理员可编辑", status_code=303)

    record = session.get(BrandBlacklistEntry, record_id)
    if not record:
        raise HTTPException(status_code=404, detail="品牌黑名单记录不存在")

    nickname = _normalize_text(nickname)
    wechat_id = _normalize_text(wechat_id)
    reason = _normalize_text(reason)

    if not nickname:
        return RedirectResponse(url="/brand-blacklist?error=昵称不能为空", status_code=303)
    if not wechat_id:
        return RedirectResponse(url="/brand-blacklist?error=微信号不能为空", status_code=303)
    if not reason:
        return RedirectResponse(url="/brand-blacklist?error=理由不能为空", status_code=303)

    duplicate = session.exec(
        select(BrandBlacklistEntry).where(
            BrandBlacklistEntry.wechat_id == wechat_id,
            BrandBlacklistEntry.id != record_id
        )
    ).first()
    if duplicate and duplicate.is_active:
        return RedirectResponse(url="/brand-blacklist?error=该微信号已存在于其他生效中的品牌黑名单记录", status_code=303)

    record.nickname = nickname
    record.wechat_id = wechat_id
    record.reason = reason
    record.updated_by_user_id = user.id
    record.updated_by_name = user.display_name
    record.updated_at = datetime.now()

    session.add(record)
    session.commit()

    return RedirectResponse(url="/brand-blacklist?success=修改成功", status_code=303)


@app.get("/brand-blacklist/revoke/{record_id}")
async def revoke_brand_blacklist(
        record_id: int,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)
    if user.role != "admin":
        return RedirectResponse(url="/brand-blacklist?error=无权限，仅超级管理员可撤销", status_code=303)

    record = session.get(BrandBlacklistEntry, record_id)
    if not record:
        raise HTTPException(status_code=404, detail="品牌黑名单记录不存在")

    record.is_active = False
    record.updated_by_user_id = user.id
    record.updated_by_name = user.display_name
    record.updated_at = datetime.now()
    record.revoked_at = datetime.now()

    session.add(record)
    session.commit()

    return RedirectResponse(url="/brand-blacklist?success=已撤销", status_code=303)


# ===获取门店/品牌数据接口===
@app.get("/brand-store-data")
async def brand_store_data_page(
        request: Request,
        dimension: str = "brand",   # brand / store
        store: str = "牛王庙店",
        start_date: Optional[str] = None,
        end_date: Optional[str] = None,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    store_list = _get_all_store_list(session)

    today = date.today()
    month_start = date(today.year, today.month, 1)

    # 默认本月：当月1号到今天
    try:
        real_start_date = datetime.strptime(start_date, "%Y-%m-%d").date() if start_date else month_start
    except:
        real_start_date = month_start

    try:
        real_end_date = datetime.strptime(end_date, "%Y-%m-%d").date() if end_date else today
    except:
        real_end_date = today

    if real_start_date > real_end_date:
        real_start_date, real_end_date = real_end_date, real_start_date

    if dimension not in ["brand", "store"]:
        dimension = "brand"

    # 如果选门店但门店不在列表里，就回退到第一个门店
    if dimension == "store":
        if store_list:
            if store not in store_list:
                store = store_list[0]
        else:
            store = ""

    stats = get_brand_store_dashboard_stats(
        session=session,
        dimension=dimension,
        store_name=store if dimension == "store" else None,
        start_date=real_start_date,
        end_date=real_end_date
    )

    return templates.TemplateResponse("brand_store_data.html", {
        "request": request,
        "page_name": "brand_store_data",
        "current_user": user,

        "dimension": dimension,
        "current_store": store,
        "store_list": store_list,

        "start_date": real_start_date.strftime("%Y-%m-%d"),
        "end_date": real_end_date.strftime("%Y-%m-%d"),

        "stats": stats,

        # 传给 JS
        "trend_labels_json": json.dumps(stats["charts"]["trend_labels"], ensure_ascii=False),
        "revenue_trend_json": json.dumps(stats["charts"]["revenue_trend"], ensure_ascii=False),
        "order_trend_json": json.dumps(stats["charts"]["order_trend"], ensure_ascii=False),
        "revenue_composition_json": json.dumps(stats["charts"]["revenue_composition"], ensure_ascii=False),
        "customer_funnel_json": json.dumps(stats["charts"]["customer_funnel"], ensure_ascii=False),
    })


# === 获取店长业绩接口 ===
@app.get("/manager-performance")
async def manager_performance(
        request: Request,
        store: str = "牛王庙店",
        year: Optional[int] = None,
        month: Optional[int] = None,
        display_mode: str = "monthly_summary",   # 新增：当前展示
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    # 1. 门店下拉框数据
    store_objs = get_store_list(session)
    store_list = [s.name for s in store_objs if s.is_active]

    if store not in store_list and store_list:
        store = store_list[0]

    # 2. 年月默认值
    today = date.today()
    y = year if year is not None else today.year
    m = month if month is not None else today.month
    if m < 1 or m > 12:
        raise HTTPException(status_code=400, detail="month 必须在 1-12 之间")

    # 3. 当前展示模式
    display_options = [
        ("monthly_summary", "月度总结"),
        ("shift_performance", "各班次业绩")
    ]
    if display_mode not in ["monthly_summary", "shift_performance"]:
        display_mode = "monthly_summary"

    # 4. 年份下拉
    year_options = list(range(today.year - 4, today.year + 1))

    # 5. 月度总结数据（原有三张图）
    monthly_stats = None
    if display_mode == "monthly_summary":
        monthly_stats = get_manager_performance_stats(
            session=session,
            store_name=store,
            year=y,
            month=m
        )

    # 6. 各班次业绩数据（新增）
    shift_stats = None
    if display_mode == "shift_performance":
        shift_stats = get_shift_performance_stats(
            session=session,
            year=y,
            month=m
        )

    shift_label = {
        "off": "休息",
        "early": "早班",
        "mid": "中班",
        "bigmid": "大中班",
        "night": "晚班"
    }

    return templates.TemplateResponse("manager_performance.html", {
        "request": request,
        "page_name": "manager_performance",
        "current_store": store,
        "store_list": store_list,
        "current_user": user,

        "year": y,
        "month": m,
        "year_options": year_options,

        # 当前展示
        "display_mode": display_mode,
        "display_options": display_options,

        # 月度总结
        "monthly_stats": monthly_stats,

        # 各班次业绩
        "shift_stats": shift_stats,
        "shift_label": shift_label
    })

# === 排班表页面（GET：查看，admin 可看到编辑控件） ===
# === 排班表页面（GET：查看，admin 可看到编辑控件） ===
@app.get("/schedule")
async def schedule_page(
        request: Request,
        year: Optional[int] = None,
        month: Optional[int] = None,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    today = date.today()
    y = year if year is not None else today.year
    m = month if month is not None else today.month

    if m < 1 or m > 12:
        raise HTTPException(status_code=400, detail="month 必须在 1-12 之间")

    # 月信息：该月天数
    _, days_in_month = calendar.monthrange(y, m)

    # 构造日期列表：1..days_in_month
    day_list = [date(y, m, d) for d in range(1, days_in_month + 1)]

    # 星期映射（中文）
    weekday_map = ["周一", "周二", "周三", "周四", "周五", "周六", "周日"]

    # V3 员工管理联动：
    # 在职员工始终展示；已停用员工只展示到停用月份为止，下个月自动不展示
    operator_names = _get_visible_employee_names_for_month(session, y, m)

    # 读取该月排班：map[(name, date)] = shift_type
    shifts_map = get_month_shifts_map(session, y, m)

    # 给前端的 shift label
    shift_options = [
        ("off", "休息"),
        ("early", "早班"),
        ("mid", "中班"),
        ("bigmid", "大中班"),
        ("night", "晚班"),
    ]
    shift_label = {k: v for k, v in shift_options}

    # 年份下拉（最近 5 年）
    year_options = list(range(today.year - 4, today.year + 1))

    return templates.TemplateResponse("schedule.html", {
        "request": request,
        "page_name": "schedule",
        "current_user": user,

        "year": y,
        "month": m,
        "year_options": year_options,
        "days_in_month": days_in_month,
        "day_list": day_list,
        "weekday_map": weekday_map,

        "operator_names": operator_names,
        "shifts_map": shifts_map,
        "shift_options": shift_options,
        "shift_label": shift_label,

        # 固定班次说明
        "shift_desc": {
            "early": "9:00-18:00",
            "mid": "11:00-20:00",
            "bigmid": "11:00-22:00",
            "night": "16:00-次日1:00",
            "off": "-"
        }
    })


# === 排班表保存（POST：仅 admin 可操作） ===
@app.post("/schedule/save")
async def schedule_save(
        request: Request,
        year: int = Form(...),
        month: int = Form(...),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    # 权限：仅超级管理员可保存
    if user.role != "admin":
        return RedirectResponse(
            url="/schedule?error=无权限，只有超级管理员可以编辑",
            status_code=303
        )

    if month < 1 or month > 12:
        raise HTTPException(status_code=400, detail="month 必须在 1-12 之间")

    # V3 员工管理联动：
    # 只有当前月份可展示的员工，才允许保存排班
    visible_operator_names = set(
        _get_visible_employee_names_for_month(session, year, month)
    )

    form = await request.form()

    allowed = {"off", "early", "mid", "bigmid", "night"}

    updated = 0
    skipped = 0

    for key, value in form.items():
        if not key.startswith("shift__"):
            continue

        if value not in allowed:
            continue

        # key: shift__张三__2026-03-01
        try:
            _, operator_name, date_str = key.split("__", 2)
            work_date = datetime.strptime(date_str, "%Y-%m-%d").date()
        except Exception:
            continue

        # 仅保存所选月份的数据
        if work_date.year != year or work_date.month != month:
            continue

        # 已停用且本月不该展示的员工，不再保存排班
        if operator_name not in visible_operator_names:
            skipped += 1
            continue

        upsert_shift(session, operator_name, work_date, value)
        updated += 1

    session.commit()

    msg = f"保存成功({updated}项)"
    if skipped:
        msg += f"，已忽略停用员工排班({skipped}项)"

    return RedirectResponse(
        url=f"/schedule?year={year}&month={month}&success={msg}",
        status_code=303
    )


# =========================
# 人情维护支出 页面与接口
# =========================

@app.get("/maintenance-records")
async def maintenance_records_page(
        request: Request,
        store: str = "牛王庙店",
        year: int = date.today().year,
        month: int = date.today().month,
        focus_record_id: Optional[int] = None,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    if month < 1 or month > 12:
        raise HTTPException(status_code=400, detail="month 必须在 1-12 之间")

    # 门店列表
    store_list = get_all_store_list(session)

    # 当前门店下的包间
    current_store_rooms = session.exec(
        select(Room).where(Room.store_name == store).order_by(Room.name)
    ).all()

    # 所有门店 -> 包间映射（前端联动）
    all_rooms = session.exec(select(Room)).all()
    room_map = {}
    for r in all_rooms:
        room_map.setdefault(r.store_name, []).append({
            "id": r.id,
            "name": r.name
        })

    # 所有门店 -> 顾客映射（只取去过该店的顾客）
    customer_links = session.exec(select(CustomerStoreLink)).all()
    store_customer_ids_map = {}
    for link in customer_links:
        store_customer_ids_map.setdefault(link.store_name, set()).add(link.customer_id)

    all_customers = session.exec(select(Customer)).all()
    customer_map = {}
    customer_dict = {c.id: c for c in all_customers}
    for s_name, cust_ids in store_customer_ids_map.items():
        customer_map[s_name] = []
        for cid in sorted(list(cust_ids)):
            cust = customer_dict.get(cid)
            if cust:
                customer_map[s_name].append({
                    "id": cust.id,
                    "nickname": cust.nickname,
                    "wechat_id": cust.wechat_id
                })

    # 月份范围
    month_start, month_end = get_month_date_range(year, month)

    # 查询当前门店、当前月份、未删除记录
    record_stmt = (
        select(MaintenanceRecord)
        .where(MaintenanceRecord.store_name == store)
        .where(MaintenanceRecord.is_deleted == False)
        .where(MaintenanceRecord.record_date >= month_start)
        .where(MaintenanceRecord.record_date < month_end)
        .order_by(MaintenanceRecord.record_date.desc(), MaintenanceRecord.id.desc())
    )
    records = session.exec(record_stmt).all()

    # 组装列表展示数据
    record_list = []
    for rec in records:
        cust = session.get(Customer, rec.customer_id)
        record_list.append({
            "id": rec.id,
            "record_date": rec.record_date,
            "room_name": rec.room_name,
            "customer_name": cust.nickname if cust else "未知顾客",
            "gift_name": rec.gift_name,
            "amount": rec.amount
        })

    # 统计区
    total_count = len(records)
    total_amount = round(sum([r.amount for r in records]), 2)

    return templates.TemplateResponse("maintenance_records.html", {
        "request": request,
        "page_name": "maintenance",
        "current_store": store,
        "store_list": store_list,
        "room_list": current_store_rooms,
        "customer_map": customer_map,
        "room_map": room_map,
        "record_list": record_list,
        "selected_year": year,
        "selected_month": month,
        "total_count": total_count,
        "total_amount": total_amount,
        "focus_record_id": focus_record_id,
        "current_user": user
    })


@app.post("/maintenance-records/add")
async def add_maintenance_record(
        store_name: str = Form(...),
        room_name: str = Form(...),
        customer_id: int = Form(...),
        gift_name: str = Form(...),
        amount: float = Form(...),
        payment_account: str = Form(...),
        reason: str = Form(...),
        record_date: date = Form(...),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login?error=请先登录", status_code=303)

    # 校验金额
    if amount <= 0:
        return RedirectResponse(
            url=f"/maintenance-records?store={store_name}&year={record_date.year}&month={record_date.month}&error=金额必须大于0",
            status_code=303
        )

    # 校验包间属于所选门店
    if not check_room_belongs_to_store(session, store_name, room_name):
        return RedirectResponse(
            url=f"/maintenance-records?store={store_name}&year={record_date.year}&month={record_date.month}&error=所选包间不属于当前门店",
            status_code=303
        )

    # 校验顾客属于所选门店
    if not check_customer_belongs_to_store(session, customer_id, store_name):
        return RedirectResponse(
            url=f"/maintenance-records?store={store_name}&year={record_date.year}&month={record_date.month}&error=所选顾客不属于当前门店",
            status_code=303
        )

    new_record = MaintenanceRecord(
        store_name=store_name,
        room_name=room_name,
        record_date=record_date,
        customer_id=customer_id,
        operator_name=user.display_name,
        gift_name=gift_name.strip(),
        amount=amount,
        payment_account=payment_account.strip(),
        reason=reason.strip(),
        is_deleted=False,
        created_at=datetime.now(),
        updated_at=datetime.now()
    )
    session.add(new_record)
    session.commit()

    return RedirectResponse(
        url=f"/maintenance-records?store={store_name}&year={record_date.year}&month={record_date.month}",
        status_code=303
    )


@app.get("/maintenance-record/{record_id}")
async def get_maintenance_record_detail(
        record_id: int,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return {"error": "未登录"}

    rec = session.get(MaintenanceRecord, record_id)
    if not rec or rec.is_deleted:
        return {"error": "记录不存在"}

    cust = session.get(Customer, rec.customer_id)
    if not cust:
        return {"error": "顾客不存在"}

    # 当前门店的包间列表（详情编辑时可切换包间）
    rooms = session.exec(
        select(Room).where(Room.store_name == rec.store_name).order_by(Room.name)
    ).all()

    return {
        "id": rec.id,
        "store_name": rec.store_name,
        "room_name": rec.room_name,
        "record_date": str(rec.record_date),
        "customer_id": rec.customer_id,
        "customer_name": cust.nickname,
        "customer_wechat": cust.wechat_id,
        "gift_name": rec.gift_name,
        "amount": rec.amount,
        "payment_account": rec.payment_account,
        "reason": rec.reason,
        "operator_name": rec.operator_name,
        "room_options": [{"id": r.id, "name": r.name} for r in rooms]
    }


@app.post("/maintenance-record/{record_id}/update")
async def update_maintenance_record(
        record_id: int,
        room_name: str = Form(...),
        record_date: date = Form(...),
        gift_name: str = Form(...),
        amount: float = Form(...),
        payment_account: str = Form(...),
        reason: str = Form(...),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login?error=请先登录", status_code=303)

    rec = session.get(MaintenanceRecord, record_id)
    if not rec or rec.is_deleted:
        raise HTTPException(status_code=404, detail="维护记录不存在")

    # 金额必须 > 0
    if amount <= 0:
        return RedirectResponse(
            url=f"/maintenance-records?store={rec.store_name}&year={rec.record_date.year}&month={rec.record_date.month}&error=金额必须大于0",
            status_code=303
        )

    # 包间必须属于原门店
    if not check_room_belongs_to_store(session, rec.store_name, room_name):
        return RedirectResponse(
            url=f"/maintenance-records?store={rec.store_name}&year={rec.record_date.year}&month={rec.record_date.month}&error=所选包间不属于当前门店",
            status_code=303
        )

    # 规则：不可修改门店、不可修改维护用户
    rec.room_name = room_name
    rec.record_date = record_date
    rec.gift_name = gift_name.strip()
    rec.amount = amount
    rec.payment_account = payment_account.strip()
    rec.reason = reason.strip()
    rec.updated_at = datetime.now()

    session.add(rec)
    session.commit()

    return RedirectResponse(
        url=f"/maintenance-records?store={rec.store_name}&year={record_date.year}&month={record_date.month}&focus_record_id={record_id}",
        status_code=303
    )


@app.get("/maintenance-record/{record_id}/delete")
async def delete_maintenance_record(
        record_id: int,
        store: str,
        year: int,
        month: int,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    rec = session.get(MaintenanceRecord, record_id)
    if rec and not rec.is_deleted:
        rec.is_deleted = True
        rec.deleted_at = datetime.now()
        rec.updated_at = datetime.now()
        session.add(rec)
        session.commit()

    return RedirectResponse(
        url=f"/maintenance-records?store={store}&year={year}&month={month}",
        status_code=303
    )

# ===================== 待办及信息同步 页面 =====================

@app.get("/handover-sync")
async def handover_sync_page(
        request: Request,
        store: Optional[str] = None,
        start_date: Optional[date] = None,
        end_date: Optional[date] = None,
        status_filter: str = "all",
        tag_filter: str = "all",
        room_filter: str = "",
        keyword: str = "",
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    # 先解析当前应使用的门店
    store = resolve_store_from_request(request, session, store)

    today = date.today()
    if start_date is None:
        start_date = today.replace(day=1)
    if end_date is None:
        end_date = today

    start_dt = datetime.combine(start_date, time.min)
    end_dt = datetime.combine(end_date + timedelta(days=1), time.min)

    # 把 room_filter 从字符串安全转换成整数
    room_filter_int = None
    if str(room_filter).strip():
        try:
            room_filter_int = int(room_filter)
        except ValueError:
            room_filter_int = None

    # 门店、包间、顾客下拉
    store_list = get_store_list_for_page(session)
    room_list = get_room_list_by_store(session, store)
    customer_options = get_customer_options_by_store(session, store)

    # 构建查询
    stmt = select(HandoverTodo).where(
        HandoverTodo.store_name == store,
        HandoverTodo.created_at >= start_dt,
        HandoverTodo.created_at < end_dt
    )

    if status_filter in ["unresolved", "resolved"]:
        stmt = stmt.where(HandoverTodo.status == status_filter)

    if tag_filter == "pinned":
        stmt = stmt.where(HandoverTodo.is_pinned == True)
    elif tag_filter == "remarked":
        stmt = stmt.where(HandoverTodo.remark != None).where(HandoverTodo.remark != "")

    if room_filter_int:
        stmt = stmt.where(HandoverTodo.room_id == room_filter_int)

    kw = keyword.strip()
    if kw:
        stmt = stmt.where(or_(
            HandoverTodo.summary.contains(kw),
            HandoverTodo.detail.contains(kw),
            HandoverTodo.remark.contains(kw),
            HandoverTodo.process_note.contains(kw)
        ))

    todos = session.exec(stmt).all()
    todos.sort(key=handover_sort_key)

    stats = build_handover_stats(session, store, start_date, end_date)
    todo_cards = build_handover_cards(session, todos)

    return templates.TemplateResponse("handover_todos.html", {
        "request": request,
        "page_name": "handover_sync",
        "current_store": store,
        "store_list": store_list,
        "room_list": room_list,
        "customer_options": customer_options,
        "todo_cards": todo_cards,
        "stats": stats,
        "start_date": start_date,
        "end_date": end_date,
        "status_filter": status_filter,
        "tag_filter": tag_filter,
        "room_filter": room_filter_int,
        "keyword": keyword,
        "current_user": user
    })


@app.post("/handover-sync/add")
async def add_handover_todo(
        store_name: str = Form(...),
        room_id: str = Form(""),
        summary: str = Form(...),
        detail: Optional[str] = Form(None),
        remark: Optional[str] = Form(None),
        is_pinned: Optional[str] = Form(None),
        customer_ids: Optional[List[int]] = Form(None),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    room_obj = None
    if room_id and str(room_id).strip():
        try:
            room_obj = session.get(Room, int(room_id))
            if room_obj and room_obj.store_name != store_name:
                room_obj = None
        except Exception:
            room_obj = None

    final_customer_ids = normalize_customer_ids_for_store(session, store_name, customer_ids)

    now = datetime.now()
    new_todo = HandoverTodo(
        store_name=store_name,
        room_id=room_obj.id if room_obj else None,
        room_name=room_obj.name if room_obj else None,
        summary=summary.strip(),
        detail=(detail or "").strip() or None,
        remark=(remark or "").strip() or None,
        is_pinned=(is_pinned == "1"),
        status="unresolved",
        process_note=None,
        created_by_user_id=user.id,
        created_by_name=user.display_name,
        handled_by_user_id=None,
        handled_by_name=None,
        created_at=now,
        updated_at=now,
        resolved_at=None
    )

    session.add(new_todo)
    session.commit()
    session.refresh(new_todo)

    for cid in final_customer_ids:
        session.add(HandoverTodoCustomerLink(todo_id=new_todo.id, customer_id=cid))

    session.commit()

    return RedirectResponse(
        url=f"/handover-sync?store={store_name}&success=新增成功",
        status_code=303
    )


@app.post("/handover-sync/update/{todo_id}")
async def update_handover_todo(
        todo_id: int,
        store_name: str = Form(...),
        room_id: str = Form(""),
        summary: str = Form(...),
        detail: Optional[str] = Form(None),
        remark: Optional[str] = Form(None),
        is_pinned: Optional[str] = Form(None),
        customer_ids: Optional[List[int]] = Form(None),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    todo = session.get(HandoverTodo, todo_id)
    if not todo:
        raise HTTPException(status_code=404, detail="待办不存在")

    room_obj = None
    if room_id and str(room_id).strip():
        try:
            room_obj = session.get(Room, int(room_id))
            if room_obj and room_obj.store_name != store_name:
                room_obj = None
        except Exception:
            room_obj = None

    todo.store_name = store_name
    todo.room_id = room_obj.id if room_obj else None
    todo.room_name = room_obj.name if room_obj else None
    todo.summary = summary.strip()
    todo.detail = (detail or "").strip() or None
    todo.remark = (remark or "").strip() or None
    todo.is_pinned = (is_pinned == "1")
    todo.updated_at = datetime.now()

    session.add(todo)

    # 1. 先规范化并去重
    final_customer_ids = normalize_customer_ids_for_store(session, store_name, customer_ids)
    final_customer_ids = list(dict.fromkeys(final_customer_ids))

    # 2. 先删旧关联，再 flush，确保不会残留旧数据
    session.exec(
        delete(HandoverTodoCustomerLink).where(HandoverTodoCustomerLink.todo_id == todo_id)
    )
    session.flush()

    # 3. 再写新关联
    for cid in final_customer_ids:
        session.add(HandoverTodoCustomerLink(todo_id=todo_id, customer_id=cid))

    session.commit()

    return RedirectResponse(
        url=f"/handover-sync?store={store_name}&success=修改成功",
        status_code=303
    )


@app.post("/handover-sync/process/{todo_id}")
async def save_handover_process(
        todo_id: int,
        process_note: str = Form(...),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    todo = session.get(HandoverTodo, todo_id)
    if not todo:
        raise HTTPException(status_code=404, detail="待办不存在")

    final_note = (process_note or "").strip()
    if not final_note:
        return RedirectResponse(
            url=f"/handover-sync?store={todo.store_name}&error=解决过程为空时，不允许保存处理过程",
            status_code=303
        )

    now = datetime.now()
    todo.process_note = final_note
    todo.handled_by_user_id = user.id
    todo.handled_by_name = user.display_name
    todo.updated_at = now

    # 如果当前已经是已解决状态，则你要求“后续修改解决过程，要更新时间”
    if todo.status == "resolved":
        todo.resolved_at = now

    session.add(todo)
    session.commit()

    return RedirectResponse(
        url=f"/handover-sync?store={todo.store_name}&success=处理过程已保存",
        status_code=303
    )


@app.post("/handover-sync/resolve/{todo_id}")
async def resolve_handover_todo(
        todo_id: int,
        process_note: str = Form(...),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    todo = session.get(HandoverTodo, todo_id)
    if not todo:
        raise HTTPException(status_code=404, detail="待办不存在")

    final_note = (process_note or "").strip()
    if not final_note:
        return RedirectResponse(
            url=f"/handover-sync?store={todo.store_name}&error=标记已解决时，必须填写至少一句解决说明",
            status_code=303
        )

    now = datetime.now()
    todo.status = "resolved"
    todo.process_note = final_note
    todo.handled_by_user_id = user.id
    todo.handled_by_name = user.display_name
    todo.updated_at = now
    todo.resolved_at = now

    session.add(todo)
    session.commit()

    return RedirectResponse(
        url=f"/handover-sync?store={todo.store_name}&success=该待办已标记为已解决",
        status_code=303
    )


@app.get("/handover-sync/reopen/{todo_id}")
async def reopen_handover_todo(
        todo_id: int,
        store: Optional[str] = None,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    todo = session.get(HandoverTodo, todo_id)
    if not todo:
        raise HTTPException(status_code=404, detail="待办不存在")

    # 按你确认的规则：
    # 1. 允许改回未解决
    # 2. process_note 不清空
    # 3. 处理人更新为当前操作人
    # 4. 处理时间（resolved_at）清空
    now = datetime.now()
    todo.status = "unresolved"
    todo.handled_by_user_id = user.id
    todo.handled_by_name = user.display_name
    todo.updated_at = now
    todo.resolved_at = None

    session.add(todo)
    session.commit()

    target_store = store or todo.store_name
    return RedirectResponse(
        url=f"/handover-sync?store={target_store}&success=已改回未解决",
        status_code=303
    )

# ======= 待办置顶 ========
@app.get("/handover-sync/pin/{todo_id}")
async def toggle_handover_pin(
        todo_id: int,
        store: Optional[str] = None,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    todo = session.get(HandoverTodo, todo_id)
    if not todo:
        raise HTTPException(status_code=404, detail="待办不存在")

    # 按你确认的规则：置顶只对未解决项生效
    if todo.status != "unresolved":
        return RedirectResponse(
            url=f"/handover-sync?store={todo.store_name}&error=置顶只对未解决待办生效",
            status_code=303
        )

    todo.is_pinned = not todo.is_pinned
    todo.updated_at = datetime.now()

    session.add(todo)
    session.commit()

    target_store = store or todo.store_name
    action_text = "已置顶" if todo.is_pinned else "已取消置顶"
    return RedirectResponse(
        url=f"/handover-sync?store={target_store}&success={action_text}",
        status_code=303
    )

# ================= 待办项删除 ===============
@app.get("/handover-sync/delete/{todo_id}")
async def delete_handover_todo(
        todo_id: int,
        store: Optional[str] = None,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    待办硬删除：
    1. 删除待办主记录
    2. 删除待办-顾客关联
    3. 删除已组齐牌局-待办关联
    规则：所有人都可删，不区分已解决/未解决
    """
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    todo = session.get(HandoverTodo, todo_id)
    if not todo:
        raise HTTPException(status_code=404, detail="待办不存在")

    target_store = store or todo.store_name

    # 1) 删除待办-顾客关联
    session.exec(
        delete(HandoverTodoCustomerLink).where(HandoverTodoCustomerLink.todo_id == todo_id)
    )

    # 2) 删除牌局-待办关联
    session.exec(
        delete(FormedGameHandoverLink).where(FormedGameHandoverLink.todo_id == todo_id)
    )

    # 3) 删除待办主记录
    session.delete(todo)
    session.commit()

    return RedirectResponse(
        url=f"/handover-sync?store={target_store}&success=待办已删除",
        status_code=303
    )



@app.get("/handover-sync/locate/{todo_id}")
async def locate_handover_todo(
        todo_id: int,
        store: Optional[str] = None,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    待办定位：
    1. 若该待办有关联牌局，则跳转到已组齐区并定位到该牌局
    2. 若无关联牌局，则提示“手动创建待办项，无关联牌局”
    3. 若有关联但牌局不存在，则提示“原有关联牌局已不存在”
    """
    if not user:
        return RedirectResponse(url="/login", status_code=303)

    todo = session.get(HandoverTodo, todo_id)
    if not todo:
        raise HTTPException(status_code=404, detail="待办不存在")

    target_store = store or todo.store_name

    link = session.exec(
        select(FormedGameHandoverLink).where(FormedGameHandoverLink.todo_id == todo_id)
    ).first()

    if not link:
        return RedirectResponse(
            url=f"/handover-sync?store={target_store}&error=该项为手动创建待办项，无关联牌局",
            status_code=303
        )

    game = session.get(GameRecord, link.game_id)

    if not game:
        return RedirectResponse(
            url=f"/handover-sync?store={target_store}&error=该待办原有关联牌局已不存在",
            status_code=303
        )

    if game.status != "formed":
        return RedirectResponse(
            url=f"/handover-sync?store={target_store}&error=该待办关联牌局当前不在已组齐区，无法定位",
            status_code=303
        )

    game_source = _normalize_text(game.record_source) or FORMED_SOURCE_NORMAL
    if game_source not in {
        FORMED_SOURCE_NORMAL,
        FORMED_SOURCE_SELF_ARRIVAL,
        FORMED_SOURCE_OVERFLOW
    }:
        game_source = FORMED_SOURCE_NORMAL

    return RedirectResponse(
        url=_build_formed_redirect_url(
            store=game.store_name or target_store,
            source_filter=game_source,
            pay_status="all",
            date_filter="this_month",
            start_date="",
            end_date="",
            payment_method_filter="all",
            focus_game_id=game.id
        ),
        status_code=303
    )


# ===================== 待办及信息同步：联动接口 =====================

@app.get("/api/handover/rooms")
async def api_handover_rooms(
        store: str,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        raise HTTPException(status_code=401, detail="请先登录")

    room_list = get_room_list_by_store(session, store)
    return [
        {"id": r.id, "name": r.name}
        for r in room_list
    ]


@app.get("/api/handover/customers")
async def api_handover_customers(
        store: str,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        raise HTTPException(status_code=401, detail="请先登录")

    return get_customer_options_by_store(session, store)

# ===== 新增待办快速筛选顾客 ====
@app.get("/api/handover/customer-search")
async def api_handover_customer_search(
        store: str,
        keyword: str = "",
        limit: int = 12,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    """
    待办及信息同步页：按门店 + 关键词快速筛选顾客
    支持按 昵称 / 微信号 模糊搜索
    """
    if not user:
        raise HTTPException(status_code=401, detail="请先登录")

    keyword = (keyword or "").strip()
    limit = max(1, min(limit, 30))

    # 先取当前门店顾客池里的 customer_id
    customer_ids = session.exec(
        select(CustomerStoreLink.customer_id).where(CustomerStoreLink.store_name == store)
    ).all()
    customer_ids = sorted(list(set(customer_ids)))

    if not customer_ids:
        return JSONResponse([])

    stmt = select(Customer).where(Customer.id.in_(customer_ids))

    if keyword:
        stmt = stmt.where(
            or_(
                Customer.nickname.contains(keyword),
                Customer.wechat_id.contains(keyword)
            )
        )

    customers = session.exec(stmt).all()

    # 排序：完全匹配优先，昵称短优先，最新优先
    customers.sort(
        key=lambda c: (
            0 if (c.nickname or "") == keyword else 1,
            len(c.nickname or ""),
            -c.id
        )
    )

    return JSONResponse([
        {
            "id": c.id,
            "nickname": c.nickname or "",
            "wechat_id": c.wechat_id or "",
            "gender": c.gender or "",
            "guarantee_deposit": c.guarantee_deposit or 0
        }
        for c in customers[:limit]
    ])


# ===== 设置门店/包间路由 =====
@app.get("/settings/stores-rooms")
async def stores_rooms_settings_page(
        request: Request,
        tab: str = "stores",
        keyword: str = "",
        store_filter: str = "",
        success: str = "",
        error: str = "",
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)
    if user.role != "admin":
        return RedirectResponse(url="/?error=无权限访问设置页", status_code=303)

    # -------- 门店列表 --------
    store_stmt = select(Store)

    if keyword.strip():
        kw = f"%{keyword.strip()}%"
        store_stmt = store_stmt.where(
            or_(
                Store.name.like(kw),
                Store.short_name.like(kw)
            )
        )

    stores = session.exec(
        store_stmt.order_by(Store.sort_order, Store.id)
    ).all()

    # -------- 包间列表 --------
    room_stmt = select(Room)

    if keyword.strip():
        kw = f"%{keyword.strip()}%"
        room_stmt = room_stmt.where(Room.name.like(kw))

    if store_filter.strip():
        store_obj = session.exec(
            select(Store).where(Store.name == store_filter.strip())
        ).first()
        if store_obj:
            room_stmt = room_stmt.where(Room.store_id == store_obj.id)
        else:
            room_stmt = room_stmt.where(Room.store_name == store_filter.strip())

    rooms = session.exec(
        room_stmt.order_by(Room.sort_order, Room.id)
    ).all()

    # 给包间补一个展示用门店名
    room_store_name_map = {}
    store_id_map = {s.id: s.name for s in session.exec(select(Store)).all()}
    for r in rooms:
        room_store_name_map[r.id] = store_id_map.get(r.store_id) or r.store_name or "-"

    return templates.TemplateResponse("settings_stores_rooms.html", {
        "request": request,
        "page_name": "settings_stores_rooms",
        "current_user": user,

        "tab": tab,
        "keyword": keyword,
        "store_filter": store_filter,
        "success": success,
        "error": error,

        "store_list": session.exec(
            select(Store).order_by(Store.sort_order, Store.id)
        ).all(),
        "stores": stores,
        "rooms": rooms,
        "room_store_name_map": room_store_name_map

    })

# ==== 新增门店 ====
@app.post("/settings/store/add")
async def add_store(
        name: str = Form(...),
        short_name: str = Form(""),
        address: str = Form(""),
        contact_phone: str = Form(""),
        sort_order: int = Form(0),
        remark: str = Form(""),
        is_active: Optional[str] = Form(None),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)
    if user.role != "admin":
        return RedirectResponse(url="/?error=无权限操作", status_code=303)

    name = name.strip()
    if not name:
        return RedirectResponse(url="/settings/stores-rooms?tab=stores&error=门店名称不能为空", status_code=303)

    exists = session.exec(
        select(Store).where(Store.name == name)
    ).first()
    if exists:
        return RedirectResponse(url="/settings/stores-rooms?tab=stores&error=门店名称已存在", status_code=303)

    now = datetime.now()
    new_store = Store(
        name=name,
        short_name=short_name.strip() or None,
        address=address.strip() or None,
        contact_phone=contact_phone.strip() or None,
        sort_order=sort_order,
        remark=remark.strip() or None,
        is_active=(is_active == "true"),
        created_at=now,
        updated_at=now
    )
    session.add(new_store)
    session.commit()

    return RedirectResponse(url="/settings/stores-rooms?tab=stores&success=门店新增成功", status_code=303)

# ==== 编辑门店 ====
@app.post("/settings/store/update/{store_id}")
async def update_store(
        store_id: int,
        short_name: str = Form(""),
        address: str = Form(""),
        contact_phone: str = Form(""),
        sort_order: int = Form(0),
        remark: str = Form(""),
        is_active: Optional[str] = Form(None),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)
    if user.role != "admin":
        return RedirectResponse(url="/?error=无权限操作", status_code=303)

    store = session.get(Store, store_id)
    if not store:
        return RedirectResponse(url="/settings/stores-rooms?tab=stores&error=门店不存在", status_code=303)

    # 本版先不允许改 name，只允许改附属信息
    store.short_name = short_name.strip() or None
    store.address = address.strip() or None
    store.contact_phone = contact_phone.strip() or None
    store.sort_order = sort_order
    store.remark = remark.strip() or None
    store.is_active = (is_active == "true")
    store.updated_at = datetime.now()

    session.add(store)
    session.commit()

    return RedirectResponse(url="/settings/stores-rooms?tab=stores&success=门店更新成功", status_code=303)

# ==== 门店启用/停用 ====
@app.get("/settings/store/toggle/{store_id}")
async def toggle_store(
        store_id: int,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)
    if user.role != "admin":
        return RedirectResponse(url="/?error=无权限操作", status_code=303)

    store = session.get(Store, store_id)
    if not store:
        return RedirectResponse(url="/settings/stores-rooms?tab=stores&error=门店不存在", status_code=303)

    store.is_active = not store.is_active
    store.updated_at = datetime.now()
    session.add(store)
    session.commit()

    return RedirectResponse(url="/settings/stores-rooms?tab=stores&success=门店状态已更新", status_code=303)

# ==== 新增包间 ====
@app.post("/settings/room/add")
async def add_room(
        store_id: int = Form(...),
        name: str = Form(...),
        description: str = Form(""),
        sort_order: int = Form(0),
        is_active: Optional[str] = Form(None),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)
    if user.role != "admin":
        return RedirectResponse(url="/?error=无权限操作", status_code=303)

    store = session.get(Store, store_id)
    if not store:
        return RedirectResponse(url="/settings/stores-rooms?tab=rooms&error=所属门店不存在", status_code=303)

    name = name.strip()
    if not name:
        return RedirectResponse(url="/settings/stores-rooms?tab=rooms&error=包间名称不能为空", status_code=303)

    exists = session.exec(
        select(Room).where(
            Room.store_id == store_id,
            Room.name == name
        )
    ).first()
    if exists:
        return RedirectResponse(url="/settings/stores-rooms?tab=rooms&error=同门店下包间名称已存在", status_code=303)

    now = datetime.now()
    new_room = Room(
        store_id=store.id,
        store_name=store.name,
        name=name,
        description=description.strip() or None,
        sort_order=sort_order,
        is_active=(is_active == "true"),
        created_at=now,
        updated_at=now
    )
    session.add(new_room)
    session.commit()

    return RedirectResponse(url="/settings/stores-rooms?tab=rooms&success=包间新增成功", status_code=303)

# ==== 编辑包间 ====
@app.post("/settings/room/update/{room_id}")
async def update_room(
        room_id: int,
        store_id: int = Form(...),
        name: str = Form(...),
        description: str = Form(""),
        sort_order: int = Form(0),
        is_active: Optional[str] = Form(None),
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)
    if user.role != "admin":
        return RedirectResponse(url="/?error=无权限操作", status_code=303)

    room = session.get(Room, room_id)
    if not room:
        return RedirectResponse(url="/settings/stores-rooms?tab=rooms&error=包间不存在", status_code=303)

    store = session.get(Store, store_id)
    if not store:
        return RedirectResponse(url="/settings/stores-rooms?tab=rooms&error=所属门店不存在", status_code=303)

    name = name.strip()
    if not name:
        return RedirectResponse(url="/settings/stores-rooms?tab=rooms&error=包间名称不能为空", status_code=303)

    duplicate = session.exec(
        select(Room).where(
            Room.store_id == store_id,
            Room.name == name,
            Room.id != room_id
        )
    ).first()
    if duplicate:
        return RedirectResponse(url="/settings/stores-rooms?tab=rooms&error=同门店下包间名称已存在", status_code=303)

    room.store_id = store.id
    room.store_name = store.name
    room.name = name
    room.description = description.strip() or None
    room.sort_order = sort_order
    room.is_active = (is_active == "true")
    room.updated_at = datetime.now()

    session.add(room)
    session.commit()

    return RedirectResponse(url="/settings/stores-rooms?tab=rooms&success=包间更新成功", status_code=303)

# ==== 包间启用/停用 ====
@app.get("/settings/room/toggle/{room_id}")
async def toggle_room(
        room_id: int,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        return RedirectResponse(url="/login", status_code=303)
    if user.role != "admin":
        return RedirectResponse(url="/?error=无权限操作", status_code=303)

    room = session.get(Room, room_id)
    if not room:
        return RedirectResponse(url="/settings/stores-rooms?tab=rooms&error=包间不存在", status_code=303)

    room.is_active = not room.is_active
    room.updated_at = datetime.now()
    session.add(room)
    session.commit()

    return RedirectResponse(url="/settings/stores-rooms?tab=rooms&success=包间状态已更新", status_code=303)

# === 动态按门店刷新包间 ===
@app.get("/api/rooms/by-store")
async def api_rooms_by_store(
        store_name: str,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        raise HTTPException(status_code=401, detail="请先登录")

    rooms = get_active_room_list_by_store(session, store_name)

    return [
        {
            "id": r.id,
            "name": r.name,
            "description": r.description or "",
            "store_name": r.store_name or store_name
        }
        for r in rooms
    ]

# === 按门店获取所有包间（包含停用)仅管理员可用
@app.get("/api/admin/rooms/by-store")
async def api_admin_rooms_by_store(
        store_name: str,
        session: Session = Depends(get_session),
        user: Optional[User] = Depends(get_current_user)
):
    if not user:
        raise HTTPException(status_code=401, detail="请先登录")
    if user.role != "admin":
        raise HTTPException(status_code=403, detail="无权限")

    store_obj = get_store_by_name(session, store_name)

    if store_obj:
        rooms = session.exec(
            select(Room).where(Room.store_id == store_obj.id).order_by(Room.sort_order, Room.id)
        ).all()
    else:
        rooms = session.exec(
            select(Room).where(Room.store_name == store_name).order_by(Room.sort_order, Room.id)
        ).all()

    return [
        {
            "id": r.id,
            "name": r.name,
            "is_active": r.is_active,
            "sort_order": r.sort_order,
            "description": r.description or ""
        }
        for r in rooms
    ]

if __name__ == "__main__":
    import uvicorn

    uvicorn.run(app, host="0.0.0.0", port=8000, reload=True)

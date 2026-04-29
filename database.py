from sqlmodel import func,SQLModel, Field, create_engine, Session, select
from datetime import datetime, date, time
from typing import Optional,Dict, List, Tuple, Any
import calendar
from sqlalchemy import UniqueConstraint,text


# === 数据库模型定义 ===
class GameRecord(SQLModel, table=True):
    id: Optional[int] = Field(default=None, primary_key=True)

    # =========================
    # 一、基础信息
    # =========================
    store_name: str  # 门店名称

    # V2：序号口径调整为“同一门店、同一自然月内递增”
    serial_number: int  # 月序号（按预约时间所属月份生成）

    # V2：沿用旧字段，统一解释为“预约时间”
    record_date: date  # 预约日期
    start_time: str  # 预约时间（存字符串 "14:30" 方便）

    # =========================
    # 二、牌局参数
    # =========================
    stakes: str  # 分数大小（如 "10分"、"20分"）
    game_type: str  # 玩法（如 "血战"、"换三张"）

    # =========================
    # 三、参与人（4个坑位）
    # =========================
    player_1: Optional[str] = None
    player_2: Optional[str] = None
    player_3: Optional[str] = None
    player_4: Optional[str] = None

    # 参与人微信号（用于关联顾客表）
    player_1_wechat: Optional[str] = None
    player_2_wechat: Optional[str] = None
    player_3_wechat: Optional[str] = None
    player_4_wechat: Optional[str] = None

    # =========================
    # 四、备注信息
    # =========================
    # V1.1 原有字段：未组齐区“特殊备注”沿用它
    tags: Optional[str] = None  # 特殊备注（前端列表显示摘要，悬浮显示全文）

    # V2：已组齐区每个参与人一条备注
    player_1_note: Optional[str] = None
    player_2_note: Optional[str] = None
    player_3_note: Optional[str] = None
    player_4_note: Optional[str] = None

    # V2：整桌备注
    table_note: Optional[str] = None

    # =========================
    # 五、正式订单信息
    # =========================
    # V3：溢出单专用，记录外部安排门店
    external_store_name: Optional[str] = Field(default=None, index=True)
    # V2：未组齐阶段默认允许为空；已组齐编辑保存时前端要求必填
    room_name: Optional[str] = None  # 包间名

    # 继续沿用你当前字段名
    payment_method: Optional[str] = None  # 下单/支付方式

    # V2：这里的 room_fee 统一解释为“本单金额（手工录入）”，不等于实收
    room_fee: float = 0.0

    # V2：实际订单开始时间（兼容旧数据，允许为空）
    order_start_time: Optional[str] = None  # 例如 "19:30"

    # =========================
    # 六、状态控制
    # =========================
    status: str = Field(default="unformed")  # unformed(未组齐), formed(已组齐)

    # V3：记录来源
    # normal = 常规牌局（未组齐 -> 已组齐）
    # self_arrival = 自主到店登记单（直接进入已组齐）
    record_source: str = Field(default="normal", index=True)

    # 接待店长：
    # 1. 未组齐新增时：谁点“确定新增”，who_did 先记谁
    # 2. 点击“组齐”时：再覆盖为谁点“组齐”
    # 3. 已组齐后：who_did 不再变更
    who_did: Optional[str] = None

    # =========================
    # 七、财务结算字段
    # =========================
    is_payAll: bool = Field(default=False)  # 是否已收齐
    wechat_pay: float = Field(default=0.0)  # 微信收款
    Alipay: float = Field(default=0.0)  # 支付宝收款

    # =========================
    # 八、审计字段
    # =========================
    # V2：用于未组齐“6小时后任意店长可撤销”的权限判断
    created_at: datetime = Field(default_factory=datetime.now, index=True)

    # V2：记录最后一次编辑时间
    updated_at: datetime = Field(default_factory=datetime.now, index=True)

    # V2：记录最后一次编辑人（显示名）
    updated_by: Optional[str] = None

# === 门店配置表（新增） ===
class Store(SQLModel, table=True):
    """
    门店主表：
    以后系统中的门店应优先从这个表读取，而不是再从 Room.store_name 去重得到。
    """
    __table_args__ = (
        UniqueConstraint("name", name="uq_store_name"),
    )

    id: Optional[int] = Field(default=None, primary_key=True)

    # 核心信息
    name: str = Field(index=True)  # 门店全称（唯一）
    short_name: Optional[str] = None  # 门店简称（可选）

    # 联系信息
    address: Optional[str] = None  # 地址
    contact_phone: Optional[str] = None  # 联系电话

    # 状态与排序
    is_active: bool = Field(default=True, index=True)  # 是否启用
    sort_order: int = Field(default=0, index=True)  # 排序值，越小越靠前

    # 备注
    remark: Optional[str] = None

    # 时间字段
    created_at: datetime = Field(default_factory=datetime.now)
    updated_at: datetime = Field(default_factory=datetime.now)

# === 包间与门店配置表（增强） ===
class Room(SQLModel, table=True):
    """
    兼容过渡设计：
    1. 保留旧字段 store_name，避免你现有业务代码立刻报错；
    2. 新增 store_id，后续逐步切换到真正的门店外键；
    3. 增加启用状态、排序、时间字段，为“设置页”做准备。
    """
    __table_args__ = (
        # 同一门店下，包间名唯一
        UniqueConstraint("store_id", "name", name="uq_room_storeid_name"),
    )

    id: Optional[int] = Field(default=None, primary_key=True)

    # 核心字段
    name: str = Field(index=True)  # 包间名称

    # 新版推荐字段：门店外键
    store_id: Optional[int] = Field(default=None, foreign_key="store.id", index=True)

    # 兼容旧逻辑：暂时保留
    store_name: Optional[str] = Field(default=None, index=True)

    # 附加信息
    description: Optional[str] = None  # 描述（如“自动麻将机”“靠窗”）
    is_active: bool = Field(default=True, index=True)  # 是否启用
    sort_order: int = Field(default=0, index=True)  # 排序值

    # 时间字段
    created_at: datetime = Field(default_factory=datetime.now)
    updated_at: datetime = Field(default_factory=datetime.now)

# === 操作员账号、权限表 ===
class User(SQLModel, table=True):
    id: Optional[int] = Field(default=None, primary_key=True)
    username: str = Field(unique=True, index=True)  # 登录账号
    hashed_password: str
    display_name: str  # 显示名称
    role: str = "operator"  # admin / operator

    # V3：员工软删除 / 停用
    is_active: bool = Field(default=True, index=True)
    deleted_at: Optional[datetime] = Field(default=None, index=True)

    # V3：展示过滤字段
    # True = 账号仍可正常登录，但不展示在排班表、店长业绩-各班次业绩-耍牌绩效考核表中
    hide_from_schedule_performance: bool = Field(default=False, index=True)

# === 顾客主表 ===
class Customer(SQLModel, table=True):
    id: Optional[int] = Field(default=None, primary_key=True)

    # 核心身份
    nickname: str = Field(index=True)  # 昵称
    wechat_id: str = Field(unique=True, index=True)  # 微信号 (唯一标识)
    gender: str = Field(default="未知")  # 性别 (男/女/未知)

    # 押金
    guarantee_deposit: float = Field(default=0.0)  # 保证金 (可增删改)

    # 流失状态控制
    # 存储 last_visit_date，由程序实时计算是否流失。
    is_loss: bool = Field(default=False)
    last_visit_date: Optional[date] = None  # 最后一次到店日期 (用于计算流失)

    # 创建时间
    created_at: date = Field(default_factory=date.today)

# === 顾客-门店关联表 ===
class CustomerStoreLink(SQLModel, table=True):
    id: Optional[int] = Field(default=None, primary_key=True)
    customer_id: int = Field(foreign_key="customer.id")  # 关联顾客
    store_name: str  # 关联门店

    # 顾客首次进入该门店顾客池的时间
    created_at: date = Field(default_factory=date.today)

    # 可以在这里也加一个 last_visit，精确记录在这个店的最后一次时间
    last_visit_at_store: date = Field(default_factory=date.today)




# === 黑名单表 ===
class Blacklist(SQLModel, table=True):
    id: Optional[int] = Field(default=None, primary_key=True)

    initiator_id: int = Field(foreign_key="customer.id")  # 谁提出来的 (比如张三)
    target_id: int = Field(foreign_key="customer.id")  # 他不想跟谁玩 (比如李四)

    reason: Optional[str] = None  # 理由 (比如：牌品差、欠钱、吵过架)
    created_at: date = Field(default_factory=date.today)


# === 品牌黑名单表（新增） ===
class BrandBlacklistEntry(SQLModel, table=True):
    """
    品牌黑名单表：
    用于记录“全品牌范围内禁止参与组局的人”。

    业务口径：
    1. 不按门店隔离，所有门店共用
    2. 一条记录对应一个被品牌封禁的人
    3. 以 wechat_id 作为强标识；nickname 作为展示冗余
    4. 仅 admin 可新增 / 编辑 / 撤销，operator 只读
    """
    __tablename__ = "brandblacklistentry"
    __table_args__ = (
        UniqueConstraint("wechat_id", name="uq_brand_blacklist_wechat_id"),
    )

    id: Optional[int] = Field(default=None, primary_key=True)

    nickname: str = Field(index=True)
    # 含义：被拉黑人的昵称（展示用）

    wechat_id: str = Field(index=True)
    # 含义：被拉黑人的微信号（品牌黑名单唯一标识）

    reason: str
    # 含义：拉黑原因

    is_active: bool = Field(default=True, index=True)
    # 含义：是否仍生效
    # True = 生效中；False = 已撤销

    created_by_user_id: int = Field(foreign_key="user.id", index=True)
    created_by_name: str
    # 含义：创建人

    updated_by_user_id: Optional[int] = Field(default=None, foreign_key="user.id", index=True)
    updated_by_name: Optional[str] = None
    # 含义：最后编辑/撤销人

    created_at: datetime = Field(default_factory=datetime.now, index=True)
    updated_at: datetime = Field(default_factory=datetime.now, index=True)
    revoked_at: Optional[datetime] = Field(default=None, index=True)
    # 含义：撤销时间，未撤销则为空

# === 同场次记录表 ===
class PlayFrequency(SQLModel, table=True):
    id: Optional[int] = Field(default=None, primary_key=True)

    # 为了防止重复存储 (A+B 和 B+A)，逻辑上我们可以规定 player_1_id 必须小于 player_2_id
    player_1_id: int = Field(foreign_key="customer.id")
    player_2_id: int = Field(foreign_key="customer.id")

    count: int = Field(default=0)  # 同场次数
    last_play_date: date = Field(default_factory=date.today)  # 最后一次同场时间

# === 人情维护表 ===
class MaintenanceRecord(SQLModel, table=True):
    id: Optional[int] = Field(default=None, primary_key=True)

    # 归属信息
    store_name: str = Field(index=True)  # 门店
    room_name: str = Field(index=True)   # 包间（必须属于 store_name）
    record_date: date = Field(default_factory=date.today, index=True)  # 维护日期

    # 维护对象
    customer_id: int = Field(foreign_key="customer.id", index=True)  # 被维护顾客（创建后不可改）

    # 操作信息
    operator_name: str = Field(index=True)  # 操作员（who_did）

    # 维护内容
    gift_name: str  # 赠送物品
    amount: float = Field(default=0.0)  # 金额（业务上要求 > 0，建议在接口层校验）
    payment_account: str  # 付款账号（如：公司备用金、店长垫付）
    reason: str  # 赠送理由（如：生日、安抚输家）

    # 状态控制
    is_deleted: bool = Field(default=False, index=True)  # 软删除标记
    deleted_at: Optional[datetime] = Field(default=None)  # 删除时间

    # 时间戳
    created_at: datetime = Field(default_factory=datetime.now, index=True)  # 创建时间
    updated_at: datetime = Field(default_factory=datetime.now)  # 最后更新时间

# === 排班表 ===
class ShiftSchedule(SQLModel, table=True):
    """
    排班记录：一个“店长/操作员 + 某天”对应一个班次。
    不按门店隔离，属于全局排班。
    """
    id: Optional[int] = Field(default=None, primary_key=True)

    # 排班日期（按天）
    work_date: date = Field(index=True)

    # 店长/操作员显示名（与 User.display_name 对齐）
    operator_name: str = Field(index=True)

    # 班次：early / mid / bigmid / night / off
    shift_type: str = Field(default="off", index=True)

# ===================== 新增：待办及信息同步业务表 =====================
class HandoverTodo(SQLModel, table=True):
    """
    待办及信息同步主表。
    一条记录代表“某门店在交班/跟班过程中需要同步的一件事项”。

    设计目标：
    1. 支持一个待办项关联多个顾客（通过关联表实现）
    2. 支持包间可空
    3. 支持“概述 / 详细说明 / 备注 / 处理过程”分层表达
    4. 支持置顶、解决、改回未解决、持续补充处理过程
    """
    __tablename__ = "handovertodo"

    id: Optional[int] = Field(default=None, primary_key=True)

    # ===== 归属信息 =====
    store_name: str = Field(index=True)
    # 含义：该待办属于哪个门店。
    # 用途：列表筛选、统计筛选、门店隔离展示。

    room_id: Optional[int] = Field(default=None, foreign_key="room.id")
    # 含义：关联的包间ID，可为空。
    # 用途：支持“某件事对应具体包间”的场景；如果事项不绑定包间，则为空。

    room_name: Optional[str] = Field(default=None)
    # 含义：冗余保存包间名称。
    # 用途：减少展示时联表压力；即使后续包间名被修改，历史记录也能保留当时显示名称。

    # ===== 事项内容 =====
    summary: str = Field(index=True)
    # 含义：事件概述 / 待办标题。
    # 用途：列表卡片主标题，要求简短明确。

    detail: Optional[str] = Field(default=None)
    # 含义：事件详细说明。
    # 用途：详情页、编辑页完整展示事件背景与说明。

    remark: Optional[str] = Field(default=None)
    # 含义：备注。
    # 用途：补充记录额外说明；前端若该字段有值，则自动显示“已备注”标签。

    # ===== 状态与标签 =====
    is_pinned: bool = Field(default=False, index=True)
    # 含义：是否置顶。
    # 用途：仅对“未解决”事项生效，控制列表置顶排序。

    status: str = Field(default="unresolved", index=True)
    # 含义：当前待办状态。
    # 约定值：unresolved(未解决) / resolved(已解决)
    # 用途：控制展示分组、操作按钮、统计数量。

    # ===== 处理过程 =====
    process_note: Optional[str] = Field(default=None)
    # 含义：处理过程 / 解决过程。
    # 用途：记录当前事项是如何被跟进、处理、解决的。
    # 规则：保存处理过程时不能为空；标记已解决时也必须至少填写一句说明。

    # ===== 创建人（登记人） =====
    created_by_user_id: int = Field(foreign_key="user.id")
    # 含义：登记人用户ID。
    # 用途：审计、关联用户、避免仅存名字带来的歧义。

    created_by_name: str
    # 含义：登记人显示名。
    # 用途：前端直接展示，不必每次联 User 表。

    # ===== 处理人 =====
    handled_by_user_id: Optional[int] = Field(default=None, foreign_key="user.id")
    # 含义：最后一次保存处理过程 / 标记已解决 / 改回未解决 的操作人ID。
    # 用途：责任留痕。

    handled_by_name: Optional[str] = Field(default=None)
    # 含义：最后处理人的显示名。
    # 用途：前端直接展示。

    # ===== 时间字段 =====
    created_at: datetime = Field(default_factory=datetime.now, index=True)
    # 含义：登记时间。
    # 用途：默认筛选依据、列表排序、详情展示。

    updated_at: datetime = Field(default_factory=datetime.now, index=True)
    # 含义：最后更新时间。
    # 用途：只要记录被编辑、置顶、保存处理过程、状态变更，就更新该字段。

    resolved_at: Optional[datetime] = Field(default=None, index=True)
    # 含义：最近一次进入“已解决”状态的时间。
    # 用途：展示解决时间；如果已解决后再次修改处理过程，也会同步更新该时间。
    # 规则：改回未解决时清空该字段。

class HandoverTodoCustomerLink(SQLModel, table=True):
    """
    待办-顾客 关联表。
    一条记录表示：某个待办项关联了某一个顾客。
    这样可以支持“一个待办包含多个顾客”。
    """
    __tablename__ = "handovertodocustomerlink"
    __table_args__ = (
        UniqueConstraint("todo_id", "customer_id", name="uq_handover_todo_customer"),
    )

    id: Optional[int] = Field(default=None, primary_key=True)

    todo_id: int = Field(foreign_key="handovertodo.id")
    # 含义：所属待办项ID。
    # 用途：定位该顾客关联到哪一条待办。

    customer_id: int = Field(foreign_key="customer.id")
    # 含义：被关联的顾客ID。
    # 用途：支持一个待办项挂多个顾客。

class FormedGameHandoverLink(SQLModel, table=True):
    """
    已组齐牌局 - 待办 关联表

    设计目标：
    1. 不修改 HandoverTodo 主表结构
    2. 一条已组齐牌局最多对应 1 条“备注同步类待办”
    3. 一条待办也只允许对应 1 条已组齐牌局来源
    4. 便于后续硬删除待办时同步清理关联关系
    """
    __tablename__ = "formedgamehandoverlink"
    __table_args__ = (
        # 一个牌局最多挂一条联动待办
        UniqueConstraint("game_id", name="uq_formedgamehandoverlink_game_id"),
        # 一条待办只允许对应一个牌局联动来源
        UniqueConstraint("todo_id", name="uq_formedgamehandoverlink_todo_id"),
    )

    id: Optional[int] = Field(default=None, primary_key=True)

    game_id: int = Field(foreign_key="gamerecord.id", index=True)
    # 含义：来源牌局ID（必须是已组齐牌局）
    # 用途：已组齐区保存时，先根据 game_id 查是否已有对应待办

    todo_id: int = Field(foreign_key="handovertodo.id", index=True)
    # 含义：关联的待办ID
    # 用途：定位“这局牌当前对应的是哪一条待办”

    created_at: datetime = Field(default_factory=datetime.now, index=True)
    # 含义：建立关联的时间
    # 用途：审计留痕；删除待办时也方便排查历史



# ===================== 新增：自主到店登记表 =====================
class SelfArrivalRecord(SQLModel, table=True):
    """
    自主到店登记表：
    记录“非牌局流程”产生的自主到店订单登记信息。
    该表按门店隔离展示，并纳入业绩统计中的“销售订单”口径。
    """
    __tablename__ = "selfarrivalrecord"

    id: Optional[int] = Field(default=None, primary_key=True)

    # ===== 归属信息 =====
    store_name: str = Field(index=True)
    # 含义：该登记记录属于哪个门店

    serial_number: int = Field(index=True)
    # 含义：月序号（同一门店、同一自然月内递增）

    room_name: str = Field(index=True)
    # 含义：预约包间

    order_date: date = Field(index=True)
    # 含义：订单开始时间对应的日期（用于按月统计、按日统计）

    order_start_time: str
    # 含义：订单开始时间，建议存 "YYYY-%m-%d %H:%M"

    # ===== 下单用户信息 =====
    customer_name: str
    # 含义：下单用户小程序名称 / 微信昵称

    customer_contact: str
    # 含义：下单用户手机号 / 微信号

    order_method: str = Field(index=True)
    # 含义：下单方式
    # 约定值：
    # 美团团购、抖音团购、美团预定、小程序端口预约、代客收款下单、代客验券下单

    # ===== 操作人信息 =====
    operator_user_id: int = Field(foreign_key="user.id", index=True)
    # 含义：谁点击“确定保存”

    operator_name: str = Field(index=True)
    # 含义：操作人显示名，前端直接展示

    # ===== 审计时间 =====
    created_at: datetime = Field(default_factory=datetime.now, index=True)
    updated_at: datetime = Field(default_factory=datetime.now, index=True)

# ===================== V3 员工管理模块：员工档案表 =====================
class EmployeeProfile(SQLModel, table=True):
    """
    员工扩展档案表。

    说明：
    1. User 表只负责登录账号、角色、是否停用；
    2. EmployeeProfile 负责员工业务档案和工资基础参数；
    3. 后续若某个员工基础工资、日薪、岗位不同，不需要改 User 表。
    """
    __tablename__ = "employeeprofile"
    __table_args__ = (
        UniqueConstraint("user_id", name="uq_employeeprofile_user_id"),
    )

    id: Optional[int] = Field(default=None, primary_key=True)

    # 关联系统登录账号
    user_id: int = Field(foreign_key="user.id", index=True)

    # 冗余快照：防止员工改名后，历史工资档案展示混乱
    display_name_snapshot: str = Field(index=True)

    # 岗位：operator / supervisor / manager / admin 等，后续可扩展
    position: str = Field(default="operator", index=True)

    # 工资基础参数
    base_salary: float = Field(default=2800.0)              # 月基础工资
    normal_daily_salary: float = Field(default=105.74)      # 普通班次日薪
    hourly_salary: float = Field(default=11.74)             # 时薪
    bigmid_extra_salary: float = Field(default=23.48)       # 大中班额外补贴
    bigmid_daily_salary: float = Field(default=129.22)      # 大中班日薪 = 105.74 + 23.48

    # 入离职信息
    join_date: date = Field(default_factory=date.today, index=True)
    leave_date: Optional[date] = Field(default=None, index=True)

    remark: Optional[str] = None

    created_at: datetime = Field(default_factory=datetime.now, index=True)
    updated_at: datetime = Field(default_factory=datetime.now, index=True)


# ===================== V3 员工管理模块：团队表 =====================
class EmployeeTeam(SQLModel, table=True):
    """
    团队表。

    说明：
    1. 团队成员不能简单按 role != admin 判断；
    2. 管理员也可能属于某个团队；
    3. 团队奖金池、团队负责门店、团队考核都基于该表。
    """
    __tablename__ = "employeeteam"

    id: Optional[int] = Field(default=None, primary_key=True)

    name: str = Field(index=True)
    description: Optional[str] = None

    is_active: bool = Field(default=True, index=True)

    created_at: datetime = Field(default_factory=datetime.now, index=True)
    updated_at: datetime = Field(default_factory=datetime.now, index=True)


class EmployeeTeamMember(SQLModel, table=True):
    """
    团队成员表。

    说明：
    1. 一名员工可以在不同时间加入/退出团队；
    2. 是否参与当月团队奖金，后续按 joined_at / left_at / is_active 判断；
    3. 不按 User.role 判断，所以管理员也可以被加入团队。
    """
    __tablename__ = "employeeteammember"
    __table_args__ = (
        UniqueConstraint("team_id", "user_id", name="uq_employeeteammember_team_user"),
    )

    id: Optional[int] = Field(default=None, primary_key=True)

    team_id: int = Field(foreign_key="employeeteam.id", index=True)
    user_id: int = Field(foreign_key="user.id", index=True)

    joined_at: date = Field(default_factory=date.today, index=True)
    left_at: Optional[date] = Field(default=None, index=True)

    is_active: bool = Field(default=True, index=True)
    remark: Optional[str] = None

    created_at: datetime = Field(default_factory=datetime.now, index=True)
    updated_at: datetime = Field(default_factory=datetime.now, index=True)


class TeamStoreAssignment(SQLModel, table=True):
    """
    团队负责门店表。

    说明：
    1. 第一版可以默认一个团队负责所有门店；
    2. 后续如果多个团队负责不同门店，不需要重构工资逻辑；
    3. store_name_snapshot 用于保留当时门店名称，避免门店改名影响历史展示。
    """
    __tablename__ = "teamstoreassignment"
    __table_args__ = (
        UniqueConstraint("team_id", "store_id", name="uq_teamstoreassignment_team_store"),
    )

    id: Optional[int] = Field(default=None, primary_key=True)

    team_id: int = Field(foreign_key="employeeteam.id", index=True)
    store_id: int = Field(foreign_key="store.id", index=True)

    store_name_snapshot: str = Field(index=True)

    is_active: bool = Field(default=True, index=True)

    created_at: datetime = Field(default_factory=datetime.now, index=True)
    updated_at: datetime = Field(default_factory=datetime.now, index=True)


# ===================== V3 员工管理模块：请假申请表 =====================
class EmployeeLeaveRequest(SQLModel, table=True):
    """
    请假申请表。

    说明：
    1. 员工提交请假申请；
    2. 管理员审批；
    3. 审批通过后再生成考勤记录和工资流水；
    4. 请假通过不影响全勤奖，但会按当天班次扣基础日薪；
    5. 休息日请假不扣款。
    """
    __tablename__ = "employeeleaverequest"

    id: Optional[int] = Field(default=None, primary_key=True)

    user_id: int = Field(foreign_key="user.id", index=True)
    employee_name_snapshot: str = Field(index=True)

    leave_date: date = Field(index=True)                  # 请假日期
    apply_date: date = Field(default_factory=date.today)  # 申请日期

    # 系统根据 ShiftSchedule 自动读取并保存快照
    shift_type: str = Field(default="off", index=True)    # mid / bigmid / night / off

    reason: str
    remark: Optional[str] = None

    # pending / approved / rejected / cancelled
    status: str = Field(default="pending", index=True)

    # 是否满足至少提前一天申请
    is_before_one_day: bool = Field(default=False, index=True)

    # 预计扣款与最终扣款分开，避免审批时管理员修正金额
    estimated_deduct_amount: float = Field(default=0.0)
    final_deduct_amount: float = Field(default=0.0)

    approved_by_user_id: Optional[int] = Field(default=None, foreign_key="user.id", index=True)
    approved_by_name: Optional[str] = None
    approved_at: Optional[datetime] = Field(default=None, index=True)
    approval_note: Optional[str] = None

    # 审批通过后关联生成的考勤记录和工资流水
    attendance_record_id: Optional[int] = Field(default=None, index=True)
    salary_flow_id: Optional[int] = Field(default=None, index=True)

    created_at: datetime = Field(default_factory=datetime.now, index=True)
    updated_at: datetime = Field(default_factory=datetime.now, index=True)


# ===================== V3 员工管理模块：考勤事件表 =====================
class EmployeeAttendanceRecord(SQLModel, table=True):
    """
    员工考勤事件表。

    说明：
    1. 记录请假、迟到、旷工、工作失误等事实；
    2. 请假一般由 EmployeeLeaveRequest 审批通过后自动生成；
    3. 迟到、旷工、工作失误由管理员手动登记；
    4. 若产生扣款，需要同步生成 SalaryFlowRecord。
    """
    __tablename__ = "employeeattendancerecord"

    id: Optional[int] = Field(default=None, primary_key=True)

    user_id: int = Field(foreign_key="user.id", index=True)
    employee_name_snapshot: str = Field(index=True)

    event_date: date = Field(index=True)

    # leave / late / absent / mistake / other
    event_type: str = Field(index=True)

    # 当天班次快照：mid / bigmid / night / off
    shift_type: str = Field(default="off", index=True)

    reason: str
    remark: Optional[str] = None

    # pending / approved / rejected / recorded
    # 请假类可用 approved，迟到旷工类一般用 recorded
    status: str = Field(default="recorded", index=True)

    # 是否影响全勤奖：
    # 审批通过请假 = False；迟到/旷工通常 = True
    affect_full_attendance: bool = Field(default=False, index=True)

    # 本事件产生的扣款金额，正数存储，生成工资流水时转成负数
    deduct_amount: float = Field(default=0.0)

    # 是否已经生成工资流水，防止重复生成
    is_salary_generated: bool = Field(default=False, index=True)

    salary_flow_id: Optional[int] = Field(default=None, index=True)
    # 含义：关联生成的工资流水 ID。
    # 用途：审批通过请假、迟到扣款、旷工扣款等生成 SalaryFlowRecord 后，用这个字段记录对应流水。

    # 来源请假申请，可为空
    leave_request_id: Optional[int] = Field(default=None, foreign_key="employeeleaverequest.id", index=True)

    created_by_user_id: int = Field(foreign_key="user.id", index=True)
    created_by_name: str

    approved_by_user_id: Optional[int] = Field(default=None, foreign_key="user.id", index=True)
    approved_by_name: Optional[str] = None
    approved_at: Optional[datetime] = Field(default=None, index=True)
    approval_note: Optional[str] = None

    created_at: datetime = Field(default_factory=datetime.now, index=True)
    updated_at: datetime = Field(default_factory=datetime.now, index=True)


# ===================== V3 员工管理模块：工资流水表 =====================
class SalaryFlowRecord(SQLModel, table=True):
    """
    工资流动记录表。

    说明：
    1. 这是“我的工资”页面的核心数据源；
    2. 所有加钱、扣钱、奖金、提成、补贴、修正都必须进入这张表；
    3. MonthlySalarySettlement 只做汇总，不替代工资流水；
    4. amount 正数表示加钱，负数表示扣钱。
    """
    __tablename__ = "salaryflowrecord"

    id: Optional[int] = Field(default=None, primary_key=True)

    user_id: int = Field(foreign_key="user.id", index=True)
    employee_name_snapshot: str = Field(index=True)

    salary_year: int = Field(index=True)
    salary_month: int = Field(index=True)

    # 这笔工资变动实际发生或归属的日期
    flow_date: date = Field(default_factory=date.today, index=True)

    # 大类：base_salary / personal_commission / team_commission / bonus /
    # deduction / attendance / manual_adjustment / replacement_work / settlement
    flow_category: str = Field(index=True)

    # 小类：monthly_base_salary / leave_deduct / late_deduct / personal_order_commission 等
    flow_type: str = Field(index=True)

    # 正数=加钱，负数=扣钱
    amount: float = Field(default=0.0)

    # 给员工看的简短标题
    title: str

    # 详细说明，例如“4月12日迟到20分钟，管理员登记扣款20元”
    description: Optional[str] = None

    # 来源类型：leave_request / attendance_record / salary_settlement / manual / team_assessment 等
    source_type: Optional[str] = Field(default=None, index=True)

    # 来源记录ID，可为空
    source_id: Optional[int] = Field(default=None, index=True)

    # 自动生成还是管理员手工录入
    is_auto: bool = Field(default=False, index=True)

    # 工资锁定后，对应流水不允许直接修改
    is_locked: bool = Field(default=False, index=True)

    # 是否在员工“我的工资”里展示
    is_visible_to_employee: bool = Field(default=True, index=True)

    created_by_user_id: Optional[int] = Field(default=None, foreign_key="user.id", index=True)
    created_by_name: Optional[str] = None

    created_at: datetime = Field(default_factory=datetime.now, index=True)
    updated_at: datetime = Field(default_factory=datetime.now, index=True)


# ===================== V3 员工管理模块：月度工资结算表 =====================
class MonthlySalarySettlement(SQLModel, table=True):
    """
    月度工资结算表。

    说明：
    1. 一名员工一个月份一条工资汇总；
    2. 汇总结果来自 SalaryFlowRecord；
    3. 真正的明细仍然看 SalaryFlowRecord；
    4. 锁定后不能直接改旧流水，只能新增工资修正流水。
    """
    __tablename__ = "monthlysalarysettlement"
    __table_args__ = (
        UniqueConstraint("user_id", "salary_year", "salary_month", name="uq_monthlysalary_user_month"),
    )

    id: Optional[int] = Field(default=None, primary_key=True)

    user_id: int = Field(foreign_key="user.id", index=True)
    employee_name_snapshot: str = Field(index=True)

    salary_year: int = Field(index=True)
    salary_month: int = Field(index=True)

    base_salary_total: float = Field(default=0.0)
    personal_commission_total: float = Field(default=0.0)
    team_commission_total: float = Field(default=0.0)
    bonus_total: float = Field(default=0.0)
    deduction_total: float = Field(default=0.0)
    manual_adjustment_total: float = Field(default=0.0)

    final_salary: float = Field(default=0.0)
    employee_social_security_amount: float = Field(default=0.0)
    social_security_amount: float = Field(default=0.0)

    # 本月个人订单量，按 GameRecord.who_did 统计
    personal_order_count: int = Field(default=0)

    team_id: Optional[int] = Field(default=None, foreign_key="employeeteam.id", index=True)
    team_name_snapshot: Optional[str] = None

    # draft / confirmed / paid / locked
    status: str = Field(default="draft", index=True)

    calculated_at: Optional[datetime] = Field(default=None, index=True)

    confirmed_by_user_id: Optional[int] = Field(default=None, foreign_key="user.id", index=True)
    confirmed_by_name: Optional[str] = None
    confirmed_at: Optional[datetime] = Field(default=None, index=True)

    paid_at: Optional[datetime] = Field(default=None, index=True)

    created_at: datetime = Field(default_factory=datetime.now, index=True)
    updated_at: datetime = Field(default_factory=datetime.now, index=True)


# ===================== V3 员工管理模块：团队月度考核表 =====================
class TeamMonthlyAssessment(SQLModel, table=True):
    """
    团队月度考核表。

    说明：
    1. 团队奖金池 = 1000 × 团队成员数；
    2. 目标业绩池 = 团队奖金池 × 60%；
    3. 非结果性考核池 = 团队奖金池 × 40%；
    4. 团队零失误奖 1000 元是团队总额；
    5. 团队总奖金最终由团队成员平均分。
    """
    __tablename__ = "teammonthlyassessment"
    __table_args__ = (
        UniqueConstraint("team_id", "year", "month", name="uq_teammonthlyassessment_team_month"),
    )

    id: Optional[int] = Field(default=None, primary_key=True)

    team_id: int = Field(foreign_key="employeeteam.id", index=True)
    team_name_snapshot: str = Field(index=True)

    year: int = Field(index=True)
    month: int = Field(index=True)

    team_member_count: int = Field(default=0)

    base_pool_amount: float = Field(default=0.0)          # 1000 × 团队人数
    target_pool_amount: float = Field(default=0.0)        # base_pool × 60%
    non_result_pool_amount: float = Field(default=0.0)    # base_pool × 40%

    responsible_store_count: int = Field(default=0)
    target_reached_store_count: int = Field(default=0)
    target_bonus_released_amount: float = Field(default=0.0)

    non_result_score: float = Field(default=100.0)
    non_result_release_rate: float = Field(default=1.0)
    non_result_bonus_amount: float = Field(default=0.0)

    zero_mistake_bonus_amount: float = Field(default=0.0)

    total_team_bonus_amount: float = Field(default=0.0)
    per_member_bonus_amount: float = Field(default=0.0)

    # draft / confirmed / locked
    status: str = Field(default="draft", index=True)

    created_at: datetime = Field(default_factory=datetime.now, index=True)
    updated_at: datetime = Field(default_factory=datetime.now, index=True)


class TeamAssessmentDeductionItem(SQLModel, table=True):
    """
    团队非结果性考核扣分明细表。

    说明：
    管理员逐条填写扣分项，TeamMonthlyAssessment.non_result_score 根据明细汇总得到。
    """
    __tablename__ = "teamassessmentdeductionitem"

    id: Optional[int] = Field(default=None, primary_key=True)

    assessment_id: int = Field(foreign_key="teammonthlyassessment.id", index=True)
    team_id: int = Field(foreign_key="employeeteam.id", index=True)

    deduct_date: date = Field(default_factory=date.today, index=True)

    deduct_points: float = Field(default=0.0)
    reason: str
    remark: Optional[str] = None

    created_by_user_id: int = Field(foreign_key="user.id", index=True)
    created_by_name: str

    created_at: datetime = Field(default_factory=datetime.now, index=True)
    updated_at: datetime = Field(default_factory=datetime.now, index=True)


# ===================== V3 员工管理模块：门店月目标快照表 =====================
class StoreMonthlyTargetSnapshot(SQLModel, table=True):
    """
    门店月目标快照表。

    说明：
    1. 门店目标订单量 = 启用包间数 × 当月天数 × 2；
    2. 用快照保存历史月份目标，避免后续包间数量变化后影响历史统计；
    3. 激励白板和团队目标业绩考核都可以读取该表。
    """
    __tablename__ = "storemonthlytargetsnapshot"
    __table_args__ = (
        UniqueConstraint("store_id", "year", "month", name="uq_storemonthlytarget_store_month"),
    )

    id: Optional[int] = Field(default=None, primary_key=True)

    store_id: int = Field(foreign_key="store.id", index=True)
    store_name_snapshot: str = Field(index=True)

    year: int = Field(index=True)
    month: int = Field(index=True)

    active_room_count: int = Field(default=0)
    days_in_month: int = Field(default=0)

    # 目标订单量 = active_room_count × days_in_month × 2
    target_order_count: int = Field(default=0)

    # 实际订单量，按 GameRecord.status='formed' 统计后写入快照
    actual_order_count: int = Field(default=0)

    is_reached: bool = Field(default=False, index=True)

    created_at: datetime = Field(default_factory=datetime.now, index=True)
    updated_at: datetime = Field(default_factory=datetime.now, index=True)


# ===================== V3 员工管理模块：员工通知表 =====================
class EmployeeNotification(SQLModel, table=True):
    """
    员工通知表。

    说明：
    1. 第一版采用“每个接收人一条通知”的方式，便于独立标记已读；
    2. 管理员新增迟到/旷工扣款时，给其他员工生成通知；
    3. 前端后续通过轮询 unread 通知实现弹窗。
    """
    __tablename__ = "employeenotification"

    id: Optional[int] = Field(default=None, primary_key=True)

    # 接收通知的员工
    target_user_id: int = Field(foreign_key="user.id", index=True)
    target_user_name_snapshot: str = Field(index=True)

    title: str
    content: str

    # attendance_late / attendance_absent / salary_deduct / leave / other
    notification_type: str = Field(index=True)

    # 触发通知的员工，可为空
    related_user_id: Optional[int] = Field(default=None, foreign_key="user.id", index=True)
    related_user_name_snapshot: Optional[str] = None

    # 来源：attendance_record / salary_flow / leave_request / manual
    source_type: Optional[str] = Field(default=None, index=True)
    source_id: Optional[int] = Field(default=None, index=True)

    is_read: bool = Field(default=False, index=True)
    read_at: Optional[datetime] = Field(default=None, index=True)

    created_at: datetime = Field(default_factory=datetime.now, index=True)

# =========== 函数定义 =============

def create_db_and_tables():
    SQLModel.metadata.create_all(engine)

    migrate_customer_store_link_table()
    migrate_game_record_table()
    migrate_formed_game_handover_link_table()
    migrate_brand_blacklist_entry_table()
    migrate_user_table()

    # V3 员工管理模块初始化：
    # 1. 为已有账号补员工档案；
    # 2. 初始化默认团队；
    # 3. 不强行把所有员工加入团队，避免管理员被默认计入奖金池。
    migrate_employee_module_tables()
    # V3 员工管理模块：
    # 补充员工考勤表后续新增字段，避免旧库已有表时 create_all 不自动加列。
    migrate_employee_attendance_record_table()
    migrate_monthly_salary_settlement_table()

def migrate_brand_blacklist_entry_table():
    """
    新增品牌黑名单表：
    用于全品牌范围的统一封禁名单，不按门店隔离。
    """
    with engine.begin() as conn:
        table_exists = conn.execute(
            text("""
                SELECT name
                FROM sqlite_master
                WHERE type='table' AND name='brandblacklistentry'
            """)
        ).fetchone()

        if table_exists:
            return

        conn.execute(text("""
            CREATE TABLE brandblacklistentry (
                id INTEGER PRIMARY KEY,
                nickname TEXT NOT NULL,
                wechat_id TEXT NOT NULL,
                reason TEXT NOT NULL,
                is_active INTEGER NOT NULL DEFAULT 1,

                created_by_user_id INTEGER NOT NULL,
                created_by_name TEXT NOT NULL,

                updated_by_user_id INTEGER,
                updated_by_name TEXT,

                created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                updated_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                revoked_at DATETIME,

                CONSTRAINT uq_brand_blacklist_wechat_id UNIQUE (wechat_id),
                FOREIGN KEY (created_by_user_id) REFERENCES user (id),
                FOREIGN KEY (updated_by_user_id) REFERENCES user (id)
            )
        """))

        conn.execute(text("""
            CREATE INDEX IF NOT EXISTS ix_brandblacklistentry_nickname
            ON brandblacklistentry (nickname)
        """))
        conn.execute(text("""
            CREATE INDEX IF NOT EXISTS ix_brandblacklistentry_wechat_id
            ON brandblacklistentry (wechat_id)
        """))
        conn.execute(text("""
            CREATE INDEX IF NOT EXISTS ix_brandblacklistentry_is_active
            ON brandblacklistentry (is_active)
        """))
        conn.execute(text("""
            CREATE INDEX IF NOT EXISTS ix_brandblacklistentry_created_at
            ON brandblacklistentry (created_at)
        """))
        conn.execute(text("""
            CREATE INDEX IF NOT EXISTS ix_brandblacklistentry_revoked_at
            ON brandblacklistentry (revoked_at)
        """))

        print("已创建 brandblacklistentry 表（品牌黑名单表）")

def migrate_customer_store_link_table():
    """
    兼容老数据库：
    1. 如果 customerstorelink 表没有 created_at，则自动补上
    2. 如果 created_at 为空，则回填今天
    """
    with engine.begin() as conn:
        # 检查表字段
        columns = conn.execute(text("PRAGMA table_info(customerstorelink)")).fetchall()
        col_names = [col[1] for col in columns]

        # 1. 补 created_at 字段
        if "created_at" not in col_names:
            conn.execute(text("ALTER TABLE customerstorelink ADD COLUMN created_at DATE"))
            conn.execute(text("UPDATE customerstorelink SET created_at = DATE('now') WHERE created_at IS NULL"))
            print("已为 customerstorelink 表补充 created_at 字段")

def migrate_game_record_table():
    """
    兼容旧版本 -> 当前版本 的 GameRecord 表结构升级。

    当前目标结构包含：
    1. player_1_note ~ player_4_note
    2. table_note
    3. order_start_time
    4. created_at
    5. updated_at
    6. updated_by
    7. record_source
    8. external_store_name   <-- 溢出单专用字段

    迁移原则：
    - 有旧值就保留
    - 旧表没有该字段时，才补默认值
    - room_name / payment_method 保持可空
    - record_source 若旧表没有，则补 'normal'
    - external_store_name 若旧表没有，则补 NULL
    """

    with engine.begin() as conn:
        table_exists = conn.execute(
            text("""
                SELECT name
                FROM sqlite_master
                WHERE type='table' AND name='gamerecord'
            """)
        ).fetchone()

        if not table_exists:
            return

        columns = conn.execute(text("PRAGMA table_info(gamerecord)")).fetchall()
        col_map = {
            col[1]: {
                "type": col[2],
                "notnull": col[3],
                "default": col[4],
                "pk": col[5],
            }
            for col in columns
        }

        required_new_cols = [
            "player_1_note",
            "player_2_note",
            "player_3_note",
            "player_4_note",
            "table_note",
            "order_start_time",
            "created_at",
            "updated_at",
            "updated_by",
            "record_source",
            "external_store_name",
        ]

        need_rebuild = False

        for c in required_new_cols:
            if c not in col_map:
                need_rebuild = True
                break

        # 若旧版本里 room_name / payment_method 是 NOT NULL，也需要重建为可空
        if (
            "room_name" in col_map and col_map["room_name"]["notnull"] == 1
        ) or (
            "payment_method" in col_map and col_map["payment_method"]["notnull"] == 1
        ):
            need_rebuild = True

        # ===== 不需要重建：只做补列 / 回填 =====
        if not need_rebuild:
            if "created_at" in col_map:
                conn.execute(text("""
                    UPDATE gamerecord
                    SET created_at = CURRENT_TIMESTAMP
                    WHERE created_at IS NULL
                """))

            if "updated_at" in col_map:
                conn.execute(text("""
                    UPDATE gamerecord
                    SET updated_at = CURRENT_TIMESTAMP
                    WHERE updated_at IS NULL
                """))

            if "record_source" in col_map:
                conn.execute(text("""
                    UPDATE gamerecord
                    SET record_source = 'normal'
                    WHERE record_source IS NULL OR TRIM(record_source) = ''
                """))

            # external_store_name 若列已存在，无需额外回填；保持 NULL 即可
            print("GameRecord 表结构已是目标结构，无需重建，仅完成空值回填。")
            return

        print("检测到 GameRecord 表需要迁移，开始重建...")

        # ===== 记录旧表中哪些列存在：有则保留，没有才补默认 =====
        has_old_player_1_note = "player_1_note" in col_map
        has_old_player_2_note = "player_2_note" in col_map
        has_old_player_3_note = "player_3_note" in col_map
        has_old_player_4_note = "player_4_note" in col_map
        has_old_table_note = "table_note" in col_map

        has_old_order_start_time = "order_start_time" in col_map
        has_old_created_at = "created_at" in col_map
        has_old_updated_at = "updated_at" in col_map
        has_old_updated_by = "updated_by" in col_map
        has_old_record_source = "record_source" in col_map
        has_old_external_store_name = "external_store_name" in col_map

        # 重命名旧表
        conn.execute(text("ALTER TABLE gamerecord RENAME TO gamerecord_old"))

        # 创建新表
        conn.execute(text("""
            CREATE TABLE gamerecord (
                id INTEGER PRIMARY KEY,

                store_name TEXT NOT NULL,
                serial_number INTEGER NOT NULL,
                record_date DATE NOT NULL,
                start_time TEXT NOT NULL,

                stakes TEXT NOT NULL,
                game_type TEXT NOT NULL,

                player_1 TEXT,
                player_2 TEXT,
                player_3 TEXT,
                player_4 TEXT,

                player_1_wechat TEXT,
                player_2_wechat TEXT,
                player_3_wechat TEXT,
                player_4_wechat TEXT,

                tags TEXT,

                player_1_note TEXT,
                player_2_note TEXT,
                player_3_note TEXT,
                player_4_note TEXT,
                table_note TEXT,

                external_store_name TEXT,

                room_name TEXT,
                payment_method TEXT,
                room_fee REAL NOT NULL DEFAULT 0,

                order_start_time TEXT,

                status TEXT NOT NULL DEFAULT 'unformed',
                record_source TEXT NOT NULL DEFAULT 'normal',
                who_did TEXT,

                is_payAll INTEGER NOT NULL DEFAULT 0,
                wechat_pay REAL NOT NULL DEFAULT 0,
                Alipay REAL NOT NULL DEFAULT 0,

                created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                updated_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                updated_by TEXT
            )
        """))

        select_sql = f"""
            SELECT
                id,
                store_name,
                serial_number,
                record_date,
                start_time,
                stakes,
                game_type,
                player_1,
                player_2,
                player_3,
                player_4,
                player_1_wechat,
                player_2_wechat,
                player_3_wechat,
                player_4_wechat,
                tags,

                {"player_1_note" if has_old_player_1_note else "NULL"} AS player_1_note,
                {"player_2_note" if has_old_player_2_note else "NULL"} AS player_2_note,
                {"player_3_note" if has_old_player_3_note else "NULL"} AS player_3_note,
                {"player_4_note" if has_old_player_4_note else "NULL"} AS player_4_note,
                {"table_note" if has_old_table_note else "NULL"} AS table_note,

                {"external_store_name" if has_old_external_store_name else "NULL"} AS external_store_name,

                room_name,
                payment_method,
                COALESCE(room_fee, 0) AS room_fee,

                {"order_start_time" if has_old_order_start_time else "NULL"} AS order_start_time,

                COALESCE(status, 'unformed') AS status,
                {"COALESCE(record_source, 'normal')" if has_old_record_source else "'normal'"} AS record_source,
                who_did,

                COALESCE(is_payAll, 0) AS is_payAll,
                COALESCE(wechat_pay, 0) AS wechat_pay,
                COALESCE(Alipay, 0) AS Alipay,

                {"COALESCE(created_at, CURRENT_TIMESTAMP)" if has_old_created_at else "CURRENT_TIMESTAMP"} AS created_at,
                {"COALESCE(updated_at, CURRENT_TIMESTAMP)" if has_old_updated_at else "CURRENT_TIMESTAMP"} AS updated_at,
                {"updated_by" if has_old_updated_by else "NULL"} AS updated_by

            FROM gamerecord_old
        """

        conn.execute(text(f"""
            INSERT INTO gamerecord (
                id,
                store_name,
                serial_number,
                record_date,
                start_time,
                stakes,
                game_type,
                player_1,
                player_2,
                player_3,
                player_4,
                player_1_wechat,
                player_2_wechat,
                player_3_wechat,
                player_4_wechat,
                tags,
                player_1_note,
                player_2_note,
                player_3_note,
                player_4_note,
                table_note,
                external_store_name,
                room_name,
                payment_method,
                room_fee,
                order_start_time,
                status,
                record_source,
                who_did,
                is_payAll,
                wechat_pay,
                Alipay,
                created_at,
                updated_at,
                updated_by
            )
            {select_sql}
        """))

        conn.execute(text("DROP TABLE gamerecord_old"))

        # ===== 索引重建 =====
        conn.execute(text("""
            CREATE INDEX IF NOT EXISTS ix_gamerecord_record_source
            ON gamerecord (record_source)
        """))

        conn.execute(text("""
            CREATE INDEX IF NOT EXISTS ix_gamerecord_created_at
            ON gamerecord (created_at)
        """))

        conn.execute(text("""
            CREATE INDEX IF NOT EXISTS ix_gamerecord_updated_at
            ON gamerecord (updated_at)
        """))

        conn.execute(text("""
            CREATE INDEX IF NOT EXISTS ix_gamerecord_external_store_name
            ON gamerecord (external_store_name)
        """))

        print("GameRecord 表已成功迁移到当前结构，旧值已按“有则保留”原则完成迁移。")

def migrate_formed_game_handover_link_table():
    """
    兼容新增：
    为“已组齐牌局 - 待办”联动增加独立关联表。

    设计口径：
    1. 不修改 HandoverTodo 主表
    2. 用独立关联表记录 game_id <-> todo_id
    3. 一个 game_id 最多只允许对应一条待办
    4. 一个 todo_id 也只允许对应一个牌局来源
    """
    with engine.begin() as conn:
        table_exists = conn.execute(
            text("""
                SELECT name
                FROM sqlite_master
                WHERE type='table' AND name='formedgamehandoverlink'
            """)
        ).fetchone()

        if table_exists:
            return

        conn.execute(text("""
            CREATE TABLE formedgamehandoverlink (
                id INTEGER PRIMARY KEY,
                game_id INTEGER NOT NULL,
                todo_id INTEGER NOT NULL,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP,

                CONSTRAINT uq_formedgamehandoverlink_game_id UNIQUE (game_id),
                CONSTRAINT uq_formedgamehandoverlink_todo_id UNIQUE (todo_id),

                FOREIGN KEY (game_id) REFERENCES gamerecord (id),
                FOREIGN KEY (todo_id) REFERENCES handovertodo (id)
            )
        """))

        conn.execute(text("""
            CREATE INDEX IF NOT EXISTS ix_formedgamehandoverlink_game_id
            ON formedgamehandoverlink (game_id)
        """))

        conn.execute(text("""
            CREATE INDEX IF NOT EXISTS ix_formedgamehandoverlink_todo_id
            ON formedgamehandoverlink (todo_id)
        """))

        conn.execute(text("""
            CREATE INDEX IF NOT EXISTS ix_formedgamehandoverlink_created_at
            ON formedgamehandoverlink (created_at)
        """))

        print("已创建 formedgamehandoverlink 表（已组齐牌局-待办关联表）")

def migrate_user_table():
    """
    V3 员工管理：为 user 表增加软删除字段和展示过滤字段。
    """
    with engine.connect() as conn:
        columns = conn.execute(text("PRAGMA table_info(user)")).fetchall()
        existing_columns = {col[1] for col in columns}

        if "is_active" not in existing_columns:
            conn.execute(text("ALTER TABLE user ADD COLUMN is_active BOOLEAN DEFAULT 1"))

        if "deleted_at" not in existing_columns:
            conn.execute(text("ALTER TABLE user ADD COLUMN deleted_at DATETIME"))

        if "hide_from_schedule_performance" not in existing_columns:
            conn.execute(text("""
                ALTER TABLE user 
                ADD COLUMN hide_from_schedule_performance BOOLEAN DEFAULT 0
            """))

        conn.commit()

def migrate_employee_attendance_record_table():
    """
    V3 员工考勤表迁移：
    为 employeeattendancerecord 表补充 salary_flow_id 字段。

    原因：
    审批通过请假后，会同时生成 EmployeeAttendanceRecord 和 SalaryFlowRecord；
    salary_flow_id 用于让考勤记录能反查对应的工资流水。
    """
    with engine.begin() as conn:
        table_exists = conn.execute(text("""
            SELECT name
            FROM sqlite_master
            WHERE type='table' AND name='employeeattendancerecord'
        """)).fetchone()

        if not table_exists:
            return

        columns = conn.execute(text("PRAGMA table_info(employeeattendancerecord)")).fetchall()
        col_names = {col[1] for col in columns}

        if "salary_flow_id" not in col_names:
            conn.execute(text("""
                ALTER TABLE employeeattendancerecord
                ADD COLUMN salary_flow_id INTEGER
            """))

            conn.execute(text("""
                CREATE INDEX IF NOT EXISTS ix_employeeattendancerecord_salary_flow_id
                ON employeeattendancerecord (salary_flow_id)
            """))

            print("已为 employeeattendancerecord 表补充 salary_flow_id 字段")


def migrate_monthly_salary_settlement_table():
    """
    V3 工资结算表迁移：
    为 monthlysalarysettlement 表补充社保字段。

    employee_social_security_amount：员工社保，公司缴纳部分，计入应发工资；
    social_security_amount：代缴社保，公司代个人缴纳部分，从实发工资中扣除。
    """
    with engine.begin() as conn:
        table_exists = conn.execute(text("""
            SELECT name
            FROM sqlite_master
            WHERE type='table' AND name='monthlysalarysettlement'
        """)).fetchone()

        if not table_exists:
            return

        columns = conn.execute(text("PRAGMA table_info(monthlysalarysettlement)")).fetchall()
        col_names = {col[1] for col in columns}

        if "employee_social_security_amount" not in col_names:
            conn.execute(text("""
                ALTER TABLE monthlysalarysettlement
                ADD COLUMN employee_social_security_amount REAL NOT NULL DEFAULT 0
            """))
            print("已为 monthlysalarysettlement 表补充 employee_social_security_amount 字段")

        if "social_security_amount" not in col_names:
            conn.execute(text("""
                ALTER TABLE monthlysalarysettlement
                ADD COLUMN social_security_amount REAL NOT NULL DEFAULT 0
            """))
            print("已为 monthlysalarysettlement 表补充 social_security_amount 字段")


def migrate_employee_module_tables():
    """
    V3 员工管理模块初始化。

    注意：
    1. 新表由 SQLModel.metadata.create_all(engine) 自动创建；
    2. 这里不重复手写 CREATE TABLE，避免和 SQLModel 模型定义不一致；
    3. 这里主要做默认数据初始化：
       - 给已有 User 补 EmployeeProfile；
       - 初始化一个“默认团队”；
       - 不默认把所有人加入团队，后续由管理员在团队管理页选择。
    """
    with Session(engine) as session:
        # ===== 1. 为已有 User 补员工档案 =====
        users = session.exec(select(User).order_by(User.id)).all()

        for u in users:
            existing_profile = session.exec(
                select(EmployeeProfile).where(EmployeeProfile.user_id == u.id)
            ).first()

            if existing_profile:
                continue

            # position 仅作为员工业务岗位，不直接等同于登录权限 role
            position = "admin" if u.role == "admin" else "operator"

            session.add(EmployeeProfile(
                user_id=u.id,
                display_name_snapshot=u.display_name,
                position=position,
                base_salary=2800.0,
                normal_daily_salary=105.74,
                hourly_salary=11.74,
                bigmid_extra_salary=23.48,
                bigmid_daily_salary=129.22,
                join_date=date.today(),
                remark="系统初始化自动创建员工档案"
            ))

        # ===== 2. 初始化默认团队 =====
        default_team = session.exec(
            select(EmployeeTeam).where(EmployeeTeam.name == "默认团队")
        ).first()

        if not default_team:
            session.add(EmployeeTeam(
                name="默认团队",
                description="V3员工管理模块初始化团队。团队成员后续由管理员手动维护，可包含管理员。",
                is_active=True
            ))

        session.commit()

        print("员工管理模块表结构已检查，员工档案和默认团队已初始化。")

def get_session():
    with Session(engine) as session:
        yield session

def get_visible_employee_names_for_month(
    session: Session,
    year: int,
    month: int
) -> List[str]:
    """
    V3 员工管理联动规则：
    1. 在职员工：始终展示；
    2. 已停用员工：展示到停用月份为止；
       例如 2026-04-24 停用，则 2026年4月仍展示，2026年5月开始不展示。
    """
    month_start = date(year, month, 1)

    users = session.exec(
        select(User).order_by(User.id)
    ).all()

    visible_names = []

    for u in users:
        # 被设置为隐藏展示的账号：仍可登录，但不进入排班表和各班次业绩展示
        if getattr(u, "hide_from_schedule_performance", False):
            continue

        is_active = getattr(u, "is_active", True)

        if is_active:
            visible_names.append(u.display_name)
            continue

        deleted_at = getattr(u, "deleted_at", None)
        if not deleted_at:
            continue

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

        if month_start <= deleted_month_start:
            visible_names.append(u.display_name)

    return list(dict.fromkeys(visible_names))

def get_month_date_range(year: int, month: int) -> Tuple[date, date]:
    """
    返回某年某月的 [month_start, next_month_start) 日期范围（左闭右开）。
    用 date 类型过滤最稳，不受时间边界影响。
    """
    month_start = date(year, month, 1)
    if month == 12:
        month_end = date(year + 1, 1, 1)
    else:
        month_end = date(year, month + 1, 1)
    return month_start, month_end


def get_manager_performance_stats(
    session: Session,
    store_name: str,
    year: int,
    month: int,
) -> Dict[str, Any]:
    """
    店长业绩三项统计（按操作员聚合），返回给前端画图。

    返回：
    {
      "operators": [...],
      "tables": [...],
      "pay_amounts": [...],
      "verify_amounts": [...],
      "totals": {"tables": int, "pay_amounts": float, "verify_amounts": float}
    }
    """
    month_start, month_end = get_month_date_range(year, month)

    # who_did 为空时归为“未标注”
    operator_col = func.coalesce(GameRecord.who_did, "未标注").label("operator")

    # 金额口径：你当前表结构里金额来源是 wechat_pay + Alipay
    amount_expr = (GameRecord.wechat_pay + GameRecord.Alipay)

    # 1) 销售订单数 = 已组齐牌局数 + 自主到店登记数

    # 1.1 已组齐牌局
    formed_stmt = (
        select(
            operator_col,
            func.count(GameRecord.id).label("cnt"),
        )
        .where(GameRecord.store_name == store_name)
        .where(GameRecord.status == "formed")
        .where(GameRecord.record_date >= month_start)
        .where(GameRecord.record_date < month_end)
        .group_by(operator_col)
    )
    formed_rows = session.exec(formed_stmt).all()
    formed_map = {r.operator: int(r.cnt) for r in formed_rows}

    # 1.2 自主到店登记
    self_arrival_stmt = (
        select(
            func.coalesce(SelfArrivalRecord.operator_name, "未标注").label("operator"),
            func.count(SelfArrivalRecord.id).label("cnt"),
        )
        .where(SelfArrivalRecord.store_name == store_name)
        .where(SelfArrivalRecord.order_date >= month_start)
        .where(SelfArrivalRecord.order_date < month_end)
        .group_by(func.coalesce(SelfArrivalRecord.operator_name, "未标注"))
    )
    self_arrival_rows = session.exec(self_arrival_stmt).all()
    self_arrival_map = {r.operator: int(r.cnt) for r in self_arrival_rows}

    # 1.3 合并为销售订单总数
    sales_order_map = {}
    all_sales_ops = set(formed_map.keys()) | set(self_arrival_map.keys())
    for op in all_sales_ops:
        sales_order_map[op] = formed_map.get(op, 0) + self_arrival_map.get(op, 0)

    # 2) 代客收款金额
    pay_stmt = (
        select(
            operator_col,
            func.coalesce(func.sum(amount_expr), 0).label("amt"),
        )
        .where(GameRecord.store_name == store_name)
        .where(GameRecord.payment_method == "代客收款")
        .where(GameRecord.record_date >= month_start)
        .where(GameRecord.record_date < month_end)
        .group_by(operator_col)
    )
    pay_rows = session.exec(pay_stmt).all()
    pay_map = {r.operator: float(r.amt or 0) for r in pay_rows}

    # 3) 代客验券金额
    verify_stmt = (
        select(
            operator_col,
            func.coalesce(func.sum(amount_expr), 0).label("amt"),
        )
        .where(GameRecord.store_name == store_name)
        .where(GameRecord.payment_method == "代客验券")
        .where(GameRecord.record_date >= month_start)
        .where(GameRecord.record_date < month_end)
        .group_by(operator_col)
    )
    verify_rows = session.exec(verify_stmt).all()
    verify_map = {r.operator: float(r.amt or 0) for r in verify_rows}

    # V3 员工管理联动：
    # 在职员工始终展示；已停用员工只展示到停用月份为止，下个月开始不展示
    visible_operator_names = set(
        get_visible_employee_names_for_month(session, year, month)
    )

    # 合并操作员全集，确保三张图 labels 一致
    raw_operators = sorted(
        set(sales_order_map.keys()) |
        set(pay_map.keys()) |
        set(verify_map.keys())
    )

    operators = [
        op for op in raw_operators
        if op in visible_operator_names
    ]

    tables = [sales_order_map.get(op, 0) for op in operators]
    pay_amounts = [round(pay_map.get(op, 0.0), 2) for op in operators]
    verify_amounts = [round(verify_map.get(op, 0.0), 2) for op in operators]

    totals = {
        "tables": int(sum(tables)),
        "pay_amounts": round(sum(pay_amounts), 2),
        "verify_amounts": round(sum(verify_amounts), 2),
    }

    return {
        "operators": operators,
        "tables": tables,
        "pay_amounts": pay_amounts,
        "verify_amounts": verify_amounts,
        "totals": totals,
        "month_start": month_start,  # 便于前端展示（可选）
        "month_end": month_end,      # 便于前端展示（可选）
    }


def get_shift_performance_stats(
    session: Session,
    year: int,
    month: int,
) -> Dict[str, Any]:
    """
    获取“各班次业绩”页面所需数据（不按门店隔离）。

    统计规则：
    1. 只要 who_did 是该店长，就算该店长业绩，不区分门店；
    2. 统计项：
       - 销售订单：status='formed' 的桌数
       - 代客收款金额：在这些 formed 中，payment_method='代客收款' 的金额总和
    3. 若某天是“休息(off)”，则该天产生的业绩统一并入“前一天的晚班”：
       - 上半部分“耍牌绩效考核表”也这样处理
       - 下半部分“各班次业绩汇总表”也这样处理
    """
    month_start, month_end = get_month_date_range(year, month)
    _, days_in_month = calendar.monthrange(year, month)
    day_list = [date(year, month, d) for d in range(1, days_in_month + 1)]

    # 为了处理“1号休息 -> 归到上个月最后一天晚班”的情况，这里把前一天也纳入排班查询范围
    prev_day = month_start.replace(day=1)
    from datetime import timedelta
    prev_day = prev_day - timedelta(days=1)

    # 1) 参与统计的员工
    # V3 员工管理联动：
    # 在职员工始终展示；已停用员工只展示到停用月份为止，下个月开始不展示
    operator_names = get_visible_employee_names_for_month(session, year, month)

    # 2) 读取排班（多查前一天，便于处理月初休息日归前一天）
    shift_rows = session.exec(
        select(ShiftSchedule).where(
            ShiftSchedule.work_date >= prev_day,
            ShiftSchedule.work_date < month_end
        )
    ).all()
    shift_map = {(r.operator_name, r.work_date): r.shift_type for r in shift_rows}

    # 3) 查询本月所有已组齐牌局（不按门店过滤）
    games = session.exec(
        select(GameRecord).where(
            GameRecord.status == "formed",
            GameRecord.record_date >= month_start,
            GameRecord.record_date < month_end
        )
    ).all()
    # 4) 查询本月所有自然登记牌局（不按门店过滤）
    self_arrival_records = session.exec(
        select(SelfArrivalRecord).where(
            SelfArrivalRecord.order_date >= month_start,
            SelfArrivalRecord.order_date < month_end
        )
    ).all()

    game_names = set([g.who_did for g in games if g.who_did])
    self_arrival_names = set([r.operator_name for r in self_arrival_records if r.operator_name])

    hidden_names = set()
    all_users = session.exec(select(User).order_by(User.id)).all()
    for u in all_users:
        if getattr(u, "hide_from_schedule_performance", False):
            hidden_names.add(u.display_name)

    extra_names = sorted(list((game_names | self_arrival_names) - set(operator_names) - hidden_names))
    operator_names.extend(extra_names)

    # 4) 初始化“最终归属日期”的逐日统计
    # 注意：这里存的是“业绩最终应该落在哪一天那一列”
    operator_daily_orders = {}
    operator_daily_pay = {}

    for name in operator_names:
        for d in day_list:
            operator_daily_orders[(name, d)] = 0
            operator_daily_pay[(name, d)] = 0.0

    # 5) 核心归属逻辑：
    #    如果当天排班是 off，则业绩归到前一天；并且前一天在表头班次显示为晚班
    for g in games:
        if not g.who_did:
            continue

        operator_name = g.who_did
        raw_date = g.record_date

        assigned_shift = shift_map.get((operator_name, raw_date), "off")

        # 默认归属当天
        target_date = raw_date

        # 如果当天是休息，则业绩归到前一天晚班
        if assigned_shift == "off":
            target_date = raw_date - timedelta(days=1)

        # 只统计最终归属仍落在当前月份表格内的数据
        if target_date < month_start or target_date >= month_end:
            continue

        key = (operator_name, target_date)

        if key not in operator_daily_orders:
            operator_daily_orders[key] = 0
            operator_daily_pay[key] = 0.0

        operator_daily_orders[key] += 1

        if g.payment_method == "代客收款":
            operator_daily_pay[key] += float((g.wechat_pay or 0) + (g.Alipay or 0))

    # 5.2 自主到店登记：也计入销售订单
    for r in self_arrival_records:
        if not r.operator_name:
            continue

        operator_name = r.operator_name
        raw_date = r.order_date

        assigned_shift = shift_map.get((operator_name, raw_date), "off")

        target_date = raw_date
        if assigned_shift == "off":
            target_date = raw_date - timedelta(days=1)

        if target_date < month_start or target_date >= month_end:
            continue

        key = (operator_name, target_date)

        if key not in operator_daily_orders:
            operator_daily_orders[key] = 0
            operator_daily_pay[key] = 0.0

        # 自主到店登记只给“销售订单 +1”，不增加代客收款金额
        operator_daily_orders[key] += 1

    # 6) 上半部分：耍牌绩效考核表
    #    班次显示逻辑：
    #    - 若“次日是休息”，则当日班次显示为晚班（因为次日休息业绩会并回到今天晚班）
    #    - 否则显示当天原始排班
    operator_rows = []
    for name in operator_names:
        daily = []
        for d in day_list:
            today_shift = shift_map.get((name, d), "off")
            next_shift = shift_map.get((name, d + timedelta(days=1)), None)

            display_shift = today_shift

            # 如果次日休息，则今天这一列承担“前一天晚班+次日休息日业绩回并”的角色，显示为晚班
            if next_shift == "off":
                display_shift = "night"

            daily.append({
                "date": d,
                "shift_type": display_shift,
                "orders": operator_daily_orders.get((name, d), 0),
                "pay_amount": round(operator_daily_pay.get((name, d), 0.0), 2)
            })
        operator_rows.append({
            "name": name,
            "daily": daily
        })

    # 7) 下半部分：各班次业绩汇总
    #    汇总按“上半部分最终显示的班次归属”来汇总
    summary_keys = ["early","mid", "bigmid", "night"]
    summary_map = {}
    for sk in summary_keys:
        for d in day_list:
            summary_map[(sk, d, "orders")] = 0
            summary_map[(sk, d, "pay_amount")] = 0.0

    for row in operator_rows:
        for item in row["daily"]:
            sk = item["shift_type"]
            d = item["date"]

            if sk not in summary_keys:
                # 休息不单独汇总
                continue

            summary_map[(sk, d, "orders")] += item["orders"]
            summary_map[(sk, d, "pay_amount")] += item["pay_amount"]

    summary_rows = []
    for sk in summary_keys:
        daily = []
        for d in day_list:
            daily.append({
                "date": d,
                "orders": summary_map[(sk, d, "orders")],
                "pay_amount": round(summary_map[(sk, d, "pay_amount")], 2)
            })
        summary_rows.append({
            "shift_type": sk,
            "daily": daily
        })

    return {
        "day_list": day_list,
        "operator_rows": operator_rows,
        "summary_rows": summary_rows
    }

def upsert_shift(
    session: Session,
    operator_name: str,
    work_date: date,
    shift_type: str
):
    """
    新增或更新某人某天班次（UPSERT）。
    """
    record = session.exec(
        select(ShiftSchedule).where(
            ShiftSchedule.operator_name == operator_name,
            ShiftSchedule.work_date == work_date
        )
    ).first()

    if record:
        record.shift_type = shift_type
        session.add(record)
    else:
        session.add(ShiftSchedule(
            operator_name=operator_name,
            work_date=work_date,
            shift_type=shift_type
        ))


def get_month_shifts_map(
    session: Session,
    year: int,
    month: int
):
    """
    获取某年某月所有排班记录，返回：
    {(operator_name, work_date): shift_type}
    """
    month_start, month_end = get_month_date_range(year, month)

    rows = session.exec(
        select(ShiftSchedule).where(
            ShiftSchedule.work_date >= month_start,
            ShiftSchedule.work_date < month_end
        )
    ).all()

    return {(r.operator_name, r.work_date): r.shift_type for r in rows}

# === 数据库连接设置 ===
sqlite_file_name = "mahjong.db"
sqlite_url = f"sqlite:///{sqlite_file_name}"

engine = create_engine(sqlite_url)


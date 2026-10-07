from __future__ import annotations

import argparse
import sqlite3
from pathlib import Path


TARGET_STORES = (
    "万象城店—两对半",
    "光华公园—两对半",
    "戛纳湾—两对半",
)
TARGET_START = "2026-09-01"
TARGET_END = "2026-09-30"
EXPECTED_TOTAL = 840
EXPECTED_STORE_COUNTS = {
    "万象城店—两对半": 383,
    "光华公园—两对半": 219,
    "戛纳湾—两对半": 238,
}
EXPECTED_SOURCE_COUNTS = {
    "normal": 9,
    "self_arrival": 831,
}
EXPECTED_EMPLOYEE_INVALID_COUNTS = {
    "何雨橦": 58,
    "周思怡": 133,
    "孙丛鑫": 62,
    "曹茜": 93,
    "胡艳婷": 90,
    "贾廷锋": 286,
    "陈家敏": 60,
    "高冰慧": 58,
}


def _dict_counts(rows: list[sqlite3.Row], key: str) -> dict[str, int]:
    return {str(row[key]): int(row["cnt"]) for row in rows}


def _assert_equal(label: str, actual: object, expected: object) -> None:
    if actual != expected:
        raise RuntimeError(f"{label}不符合预期：实际={actual!r}，预期={expected!r}")


def _target_where() -> str:
    placeholders = ", ".join("?" for _ in TARGET_STORES)
    return (
        "record_date BETWEEN ? AND ? "
        f"AND store_name IN ({placeholders})"
    )


def _target_params() -> tuple[str, ...]:
    return (TARGET_START, TARGET_END, *TARGET_STORES)


def run(db_path: Path, apply: bool) -> None:
    db_path = db_path.resolve()
    if not db_path.is_file():
        raise FileNotFoundError(f"数据库不存在：{db_path}")

    connection = sqlite3.connect(str(db_path), timeout=30)
    connection.row_factory = sqlite3.Row
    connection.isolation_level = None

    try:
        connection.execute("BEGIN IMMEDIATE" if apply else "BEGIN")
        where_sql = _target_where()
        params = _target_params()

        total = int(connection.execute(
            f"SELECT COUNT(*) FROM gamerecord WHERE status = 'formed' AND {where_sql}",
            params,
        ).fetchone()[0])
        _assert_equal("待作废订单总数", total, EXPECTED_TOTAL)

        store_rows = connection.execute(
            f"""
            SELECT store_name, COUNT(*) AS cnt
            FROM gamerecord
            WHERE status = 'formed' AND {where_sql}
            GROUP BY store_name
            """,
            params,
        ).fetchall()
        _assert_equal(
            "各门店待作废订单数",
            _dict_counts(store_rows, "store_name"),
            EXPECTED_STORE_COUNTS,
        )

        source_rows = connection.execute(
            f"""
            SELECT record_source, COUNT(*) AS cnt
            FROM gamerecord
            WHERE status = 'formed' AND {where_sql}
            GROUP BY record_source
            """,
            params,
        ).fetchall()
        _assert_equal(
            "各类型待作废订单数",
            _dict_counts(source_rows, "record_source"),
            EXPECTED_SOURCE_COUNTS,
        )

        employee_rows = connection.execute(
            f"""
            SELECT who_did, COUNT(*) AS cnt
            FROM gamerecord
            WHERE status = 'formed' AND {where_sql}
            GROUP BY who_did
            """,
            params,
        ).fetchall()
        _assert_equal(
            "各员工待作废订单数",
            _dict_counts(employee_rows, "who_did"),
            EXPECTED_EMPLOYEE_INVALID_COUNTS,
        )

        salary_rows = connection.execute(
            """
            SELECT employee_name_snapshot, status
            FROM monthlysalarysettlement
            WHERE salary_year = 2026 AND salary_month = 9
              AND employee_name_snapshot IN ({})
            ORDER BY employee_name_snapshot
            """.format(", ".join("?" for _ in EXPECTED_EMPLOYEE_INVALID_COUNTS)),
            tuple(EXPECTED_EMPLOYEE_INVALID_COUNTS),
        ).fetchall()
        _assert_equal("相关工资草稿数量", len(salary_rows), 8)
        non_draft = [
            f"{row['employee_name_snapshot']}:{row['status']}"
            for row in salary_rows
            if row["status"] != "draft"
        ]
        _assert_equal("非草稿工资记录", non_draft, [])

        print(f"数据库：{db_path}")
        print(f"预检通过：精确命中 {total} 笔 formed 订单。")
        for store_name in TARGET_STORES:
            print(f"  {store_name}：{EXPECTED_STORE_COUNTS[store_name]} 笔")
        print("  normal：9 笔；self_arrival：831 笔")
        print("  相关员工9月工资：8份，状态全部为 draft")

        if not apply:
            connection.rollback()
            print("当前为预检模式，未修改数据库。使用 --apply 才会执行作废。")
            return

        cursor = connection.execute(
            f"UPDATE gamerecord SET status = 'invalid' WHERE status = 'formed' AND {where_sql}",
            params,
        )
        _assert_equal("实际更新订单数", cursor.rowcount, EXPECTED_TOTAL)

        remaining_formed = int(connection.execute(
            f"SELECT COUNT(*) FROM gamerecord WHERE status = 'formed' AND {where_sql}",
            params,
        ).fetchone()[0])
        _assert_equal("作废后仍为formed的订单数", remaining_formed, 0)

        invalid_total = int(connection.execute(
            f"SELECT COUNT(*) FROM gamerecord WHERE status = 'invalid' AND {where_sql}",
            params,
        ).fetchone()[0])
        _assert_equal("作废后invalid订单数", invalid_total, EXPECTED_TOTAL)

        connection.commit()
        print(f"作废完成：已将 {EXPECTED_TOTAL} 笔订单从 formed 修改为 invalid。")
        print("工资数据尚未重算；请在系统中选择2026年9月并点击重新计算工资。")
    except Exception:
        if connection.in_transaction:
            connection.rollback()
        raise
    finally:
        connection.close()


def main() -> None:
    parser = argparse.ArgumentParser(
        description="将三个两对半门店2026年9月的840笔已成局订单逻辑作废。"
    )
    parser.add_argument(
        "--db",
        type=Path,
        default=Path(__file__).with_name("mahjong.db"),
        help="SQLite数据库路径，默认使用脚本同目录下的mahjong.db。",
    )
    parser.add_argument(
        "--apply",
        action="store_true",
        help="通过全部断言后提交修改；不传时只做预检。",
    )
    args = parser.parse_args()
    run(args.db, args.apply)


if __name__ == "__main__":
    main()

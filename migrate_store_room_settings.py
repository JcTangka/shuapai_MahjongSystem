import os
import shutil
import sqlite3
from datetime import datetime

DB_PATH = "mahjong.db"


def table_exists(cursor, table_name: str) -> bool:
    cursor.execute(
        "SELECT name FROM sqlite_master WHERE type='table' AND name=?",
        (table_name,)
    )
    return cursor.fetchone() is not None


def column_exists(cursor, table_name: str, column_name: str) -> bool:
    cursor.execute(f"PRAGMA table_info({table_name})")
    columns = [row[1] for row in cursor.fetchall()]
    return column_name in columns


def index_exists(cursor, index_name: str) -> bool:
    cursor.execute(
        "SELECT name FROM sqlite_master WHERE type='index' AND name=?",
        (index_name,)
    )
    return cursor.fetchone() is not None


def create_backup(db_path: str) -> str:
    if not os.path.exists(db_path):
        raise FileNotFoundError(f"数据库文件不存在：{db_path}")

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    backup_path = f"{db_path}.backup_{timestamp}"
    shutil.copy2(db_path, backup_path)
    print(f"[OK] 已备份数据库 -> {backup_path}")
    return backup_path


def add_column_if_not_exists(cursor, table_name: str, column_sql: str, column_name: str):
    if not column_exists(cursor, table_name, column_name):
        cursor.execute(f"ALTER TABLE {table_name} ADD COLUMN {column_sql}")
        print(f"[OK] 已新增字段：{table_name}.{column_name}")
    else:
        print(f"[SKIP] 字段已存在：{table_name}.{column_name}")


def main():
    print("==== 开始迁移：门店/包间设置功能 ====")

    # 0) 先备份
    create_backup(DB_PATH)

    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()

    try:
        cursor.execute("BEGIN")

        # =========================================================
        # 1. 创建 store 表
        # =========================================================
        if not table_exists(cursor, "store"):
            cursor.execute("""
                CREATE TABLE store (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    name TEXT NOT NULL,
                    short_name TEXT,
                    address TEXT,
                    contact_phone TEXT,
                    is_active INTEGER NOT NULL DEFAULT 1,
                    sort_order INTEGER NOT NULL DEFAULT 0,
                    remark TEXT,
                    created_at TEXT NOT NULL,
                    updated_at TEXT NOT NULL
                )
            """)
            print("[OK] 已创建表：store")
        else:
            print("[SKIP] 表已存在：store")

        # store.name 唯一索引
        if not index_exists(cursor, "uq_store_name"):
            cursor.execute("""
                CREATE UNIQUE INDEX uq_store_name
                ON store(name)
            """)
            print("[OK] 已创建唯一索引：uq_store_name")
        else:
            print("[SKIP] 索引已存在：uq_store_name")

        if not index_exists(cursor, "idx_store_is_active"):
            cursor.execute("CREATE INDEX idx_store_is_active ON store(is_active)")
            print("[OK] 已创建索引：idx_store_is_active")

        if not index_exists(cursor, "idx_store_sort_order"):
            cursor.execute("CREATE INDEX idx_store_sort_order ON store(sort_order)")
            print("[OK] 已创建索引：idx_store_sort_order")

        # =========================================================
        # 2. 给 room 表补字段
        # =========================================================
        if not table_exists(cursor, "room"):
            raise RuntimeError("未找到 room 表，无法继续迁移。")

        add_column_if_not_exists(cursor, "room", "store_id INTEGER", "store_id")
        add_column_if_not_exists(cursor, "room", "is_active INTEGER NOT NULL DEFAULT 1", "is_active")
        add_column_if_not_exists(cursor, "room", "sort_order INTEGER NOT NULL DEFAULT 0", "sort_order")
        add_column_if_not_exists(cursor, "room", "created_at TEXT", "created_at")
        add_column_if_not_exists(cursor, "room", "updated_at TEXT", "updated_at")

        now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        # 回填 room.created_at
        if column_exists(cursor, "room", "created_at"):
            cursor.execute("""
                UPDATE room
                SET created_at = ?
                WHERE created_at IS NULL OR TRIM(created_at) = ''
            """, (now_str,))
            print("[OK] 已回填 room.created_at")

        # 回填 room.updated_at
        if column_exists(cursor, "room", "updated_at"):
            cursor.execute("""
                UPDATE room
                SET updated_at = ?
                WHERE updated_at IS NULL OR TRIM(updated_at) = ''
            """, (now_str,))
            print("[OK] 已回填 room.updated_at")

        # room 的普通索引
        if not index_exists(cursor, "idx_room_store_id"):
            cursor.execute("CREATE INDEX idx_room_store_id ON room(store_id)")
            print("[OK] 已创建索引：idx_room_store_id")

        if not index_exists(cursor, "idx_room_store_name"):
            cursor.execute("CREATE INDEX idx_room_store_name ON room(store_name)")
            print("[OK] 已创建索引：idx_room_store_name")

        if not index_exists(cursor, "idx_room_is_active"):
            cursor.execute("CREATE INDEX idx_room_is_active ON room(is_active)")
            print("[OK] 已创建索引：idx_room_is_active")

        if not index_exists(cursor, "idx_room_sort_order"):
            cursor.execute("CREATE INDEX idx_room_sort_order ON room(sort_order)")
            print("[OK] 已创建索引：idx_room_sort_order")

        # =========================================================
        # 3. 从历史数据提取门店名 -> store 表
        #    先从 room.store_name 提取
        #    再从其他仍使用 store_name 的业务表补充
        # =========================================================
        all_store_names = set()

        # room.store_name
        if column_exists(cursor, "room", "store_name"):
            cursor.execute("""
                SELECT DISTINCT TRIM(store_name)
                FROM room
                WHERE store_name IS NOT NULL AND TRIM(store_name) != ''
            """)
            all_store_names.update(row[0] for row in cursor.fetchall() if row[0])

        # gamerecord.store_name
        if table_exists(cursor, "gamerecord") and column_exists(cursor, "gamerecord", "store_name"):
            cursor.execute("""
                SELECT DISTINCT TRIM(store_name)
                FROM gamerecord
                WHERE store_name IS NOT NULL AND TRIM(store_name) != ''
            """)
            all_store_names.update(row[0] for row in cursor.fetchall() if row[0])

        # customerstorelink.store_name
        if table_exists(cursor, "customerstorelink") and column_exists(cursor, "customerstorelink", "store_name"):
            cursor.execute("""
                SELECT DISTINCT TRIM(store_name)
                FROM customerstorelink
                WHERE store_name IS NOT NULL AND TRIM(store_name) != ''
            """)
            all_store_names.update(row[0] for row in cursor.fetchall() if row[0])

        # maintenancerecord.store_name
        if table_exists(cursor, "maintenancerecord") and column_exists(cursor, "maintenancerecord", "store_name"):
            cursor.execute("""
                SELECT DISTINCT TRIM(store_name)
                FROM maintenancerecord
                WHERE store_name IS NOT NULL AND TRIM(store_name) != ''
            """)
            all_store_names.update(row[0] for row in cursor.fetchall() if row[0])

        print(f"[INFO] 历史数据中共发现门店数：{len(all_store_names)}")

        for store_name in sorted(all_store_names):
            cursor.execute("""
                INSERT OR IGNORE INTO store
                (name, short_name, address, contact_phone, is_active, sort_order, remark, created_at, updated_at)
                VALUES (?, ?, ?, ?, 1, 0, ?, ?, ?)
            """, (
                store_name,
                None,
                None,
                None,
                "由历史数据自动迁移生成",
                now_str,
                now_str
            ))

        print("[OK] 已完成 store 初始化")

        # =========================================================
        # 4. 用 room.store_name 回填 room.store_id
        # =========================================================
        if column_exists(cursor, "room", "store_id") and column_exists(cursor, "room", "store_name"):
            cursor.execute("""
                UPDATE room
                SET store_id = (
                    SELECT s.id
                    FROM store s
                    WHERE s.name = room.store_name
                    LIMIT 1
                )
                WHERE (store_id IS NULL OR store_id = '')
                  AND store_name IS NOT NULL
                  AND TRIM(store_name) != ''
            """)
            print("[OK] 已根据 room.store_name 回填 room.store_id")

        # =========================================================
        # 5. 检查“同一门店下是否有重名包间”
        #    如果没有，创建唯一索引 uq_room_storeid_name
        # =========================================================
        cursor.execute("""
            SELECT store_id, name, COUNT(*)
            FROM room
            WHERE store_id IS NOT NULL
              AND name IS NOT NULL
              AND TRIM(name) != ''
            GROUP BY store_id, name
            HAVING COUNT(*) > 1
        """)
        duplicate_rows = cursor.fetchall()

        if duplicate_rows:
            print("[WARN] 检测到同一门店下存在重名包间，暂不创建唯一索引 uq_room_storeid_name")
            for row in duplicate_rows:
                print(f"       store_id={row[0]}, room_name={row[1]}, count={row[2]}")
        else:
            if not index_exists(cursor, "uq_room_storeid_name"):
                cursor.execute("""
                    CREATE UNIQUE INDEX uq_room_storeid_name
                    ON room(store_id, name)
                """)
                print("[OK] 已创建唯一索引：uq_room_storeid_name")
            else:
                print("[SKIP] 索引已存在：uq_room_storeid_name")

        # =========================================================
        # 6. 提交
        # =========================================================
        conn.commit()
        print("==== 迁移成功，已提交 ====")

        # =========================================================
        # 7. 输出摘要
        # =========================================================
        cursor.execute("SELECT COUNT(*) FROM store")
        store_count = cursor.fetchone()[0]

        cursor.execute("SELECT COUNT(*) FROM room")
        room_count = cursor.fetchone()[0]

        cursor.execute("SELECT COUNT(*) FROM room WHERE store_id IS NOT NULL")
        bind_count = cursor.fetchone()[0]

        print(f"[SUMMARY] 门店总数：{store_count}")
        print(f"[SUMMARY] 包间总数：{room_count}")
        print(f"[SUMMARY] 已绑定 store_id 的包间数：{bind_count}")

    except Exception as e:
        conn.rollback()
        print("!!!! 迁移失败，已回滚 !!!!")
        print("错误信息：", str(e))
        raise
    finally:
        conn.close()


if __name__ == "__main__":
    main()
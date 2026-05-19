import argparse
import getpass
import secrets
import string
from datetime import datetime

from passlib.context import CryptContext
from sqlmodel import Session, select

from database import User, create_db_and_tables, engine


pwd_context = CryptContext(schemes=["pbkdf2_sha256"], deprecated="auto")


def get_password_hash(password: str) -> str:
    return pwd_context.hash(password)


def generate_temp_password(length: int = 12) -> str:
    alphabet = string.ascii_letters + string.digits
    return "SP-ADMIN-" + "".join(secrets.choice(alphabet) for _ in range(length))


def main():
    parser = argparse.ArgumentParser(
        description="Reset an administrator password from the local server."
    )
    parser.add_argument("username", help="管理员登录账号")
    parser.add_argument(
        "--password",
        help="指定新密码；不传则自动生成临时密码"
    )
    parser.add_argument(
        "--allow-operator",
        action="store_true",
        help="允许重置普通员工账号。默认只允许重置管理员账号。"
    )
    args = parser.parse_args()

    create_db_and_tables()

    with Session(engine) as session:
        user = session.exec(select(User).where(User.username == args.username)).first()
        if not user:
            raise SystemExit(f"未找到账号：{args.username}")

        if user.role != "admin" and not args.allow_operator:
            raise SystemExit("该账号不是管理员。普通员工请在系统内由管理员重置，或添加 --allow-operator。")

        if args.password:
            new_password = args.password.strip()
        else:
            new_password = generate_temp_password()

        if len(new_password) < 8:
            raise SystemExit("新密码至少需要 8 位")

        user.hashed_password = get_password_hash(new_password)
        user.must_change_password = True
        user.password_reset_at = datetime.now()
        user.password_reset_by_user_id = None
        user.password_reset_by_name = getpass.getuser() or "local_script"

        session.add(user)
        session.commit()

    print("管理员密码已重置。")
    print(f"账号：{args.username}")
    print(f"临时密码：{new_password}")
    print("请使用临时密码登录，并立即在系统中修改密码。")


if __name__ == "__main__":
    main()

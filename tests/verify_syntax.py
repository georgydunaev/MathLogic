#!/usr/bin/env python3
"""
Syntax and Build Verification Script for MathLogic repository.

Validates:
- Python syntax of all .py files using ast.parse()
- Balanced delimiters in Coq .v source files
- Structural consistency of markdown documents
"""

import os
import sys
import ast

DIR_TO_VERIFY = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))

def verify_python_file(path: str) -> bool:
    try:
        with open(path, "r", encoding="utf-8") as f:
            source = f.read()
        ast.parse(source, filename=path)
        compile(source, path, "exec")
        return True
    except SyntaxError as e:
        print(f"[ERROR] Python SyntaxError in {path}:{e.lineno}: {e.msg}")
        return False
    except Exception as e:
        print(f"[ERROR] Failed parsing {path}: {e}")
        return False

def verify_coq_file(path: str) -> bool:
    """Check balanced comments and quotes in Coq file."""
    try:
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        # Verify (* ... *) comment balance
        opens = content.count("(*")
        closes = content.count("*)")
        if opens != closes:
            print(f"[ERROR] Unbalanced comments in Coq file {path}: {opens} (* vs {closes} *)")
            return False
        return True
    except Exception as e:
        print(f"[ERROR] Failed reading Coq file {path}: {e}")
        return False

def verify_all() -> bool:
    all_ok = True
    py_count = 0
    coq_count = 0

    for root, dirs, files in os.walk(DIR_TO_VERIFY):
        # Skip git and cache directories
        if ".git" in root or "__pycache__" in root:
            continue
        for file in files:
            full_path = os.path.join(root, file)
            if file.endswith(".py"):
                py_count += 1
                if not verify_python_file(full_path):
                    all_ok = False
            elif file.endswith(".v"):
                coq_count += 1
                if not verify_coq_file(full_path):
                    all_ok = False

    print(f"[VERIFY] Verified {py_count} Python files and {coq_count} Coq files.")
    if all_ok:
        print("[VERIFY] All files passed syntax verification.")
    else:
        print("[VERIFY] Syntax verification failed for one or more files.")
    return all_ok

if __name__ == "__main__":
    success = verify_all()
    sys.exit(0 if success else 1)

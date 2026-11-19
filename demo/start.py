#!/usr/bin/env python3
"""Install this checked runtime into a fresh prefix, then execute its local demo."""
import argparse
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument("--prefix", type=Path, required=True)
ap.add_argument("--work", type=Path, required=True)
a = ap.parse_args()
package = Path(__file__).resolve().parent
subprocess.run([sys.executable, "-B", package / "tools/install.py", "install", "--package", package,
                "--prefix", a.prefix.resolve()], check=True)
subprocess.run([sys.executable, "-B", a.prefix.resolve() / "tools/run_demo.py", "--work", a.work.resolve()], check=True)

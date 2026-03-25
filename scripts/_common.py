"""Shared utilities for submit.py and retrieve.py. Not a user-facing script."""

import os
import pathlib


def load_env() -> None:
    """Load .env from the current working directory into os.environ."""
    env = pathlib.Path(".env")
    if env.exists():
        for line in env.read_text().splitlines():
            line = line.strip()
            if line and not line.startswith("#") and "=" in line:
                k, _, v = line.partition("=")
                os.environ.setdefault(k.strip(), v.strip())

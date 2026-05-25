#!/usr/bin/env python3
"""Compatibility wrapper for the renamed C verify runner."""
from run_verify import main


if __name__ == "__main__":
    raise SystemExit(main())

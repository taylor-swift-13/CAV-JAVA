#!/usr/bin/env python3
"""Compatibility wrapper for the renamed C contract runner."""
from run_contract import main


if __name__ == "__main__":
    raise SystemExit(main())

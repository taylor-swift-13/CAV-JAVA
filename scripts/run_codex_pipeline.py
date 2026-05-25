#!/usr/bin/env python3
"""Compatibility wrapper for the renamed C pipeline runner."""
from run_pipeline import main


if __name__ == "__main__":
    raise SystemExit(main())

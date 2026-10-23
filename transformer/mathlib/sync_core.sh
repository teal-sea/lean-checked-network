#!/usr/bin/env bash
# Exact byte-preserving word rename Transformer -> TransformerCore. No other edit.
# Default: retained Model/Fast/Equiv. --bounds: frozen table/support import closure.
# --support-only: Model/Fast/Equiv plus BoundsLib, without numeric mirrors.
# --raw-pilot: frozen Net.Weights import closure, without bounds/caches/pairs.
# Generated numeric mirrors are CI outputs, never a second committed data dump.
set -eu
cd "$(dirname "$0")"
exec "${PYTHON:-python3}" sync_core.py "$@"

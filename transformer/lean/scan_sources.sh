#!/usr/bin/env bash
# Fail-closed source scan. Exit 0 = clean, 1 = a forbidden construct was found, 2 = grep failed (e.g. a missing file).
# Prints hits to stdout. Usage: scan_sources.sh file...
hits=$(grep -nE "sorry|\b(admit|unsafe)\b|native_decide|^\s*axiom |opaque |implemented_by|extern|skipKernelTC|decide \+native" "$@" 2>&1)
rc=$?
case $rc in
  0) printf '%s\n' "$hits"; exit 1 ;;
  1) exit 0 ;;
  *) printf '%s\n' "$hits"; exit 2 ;;
esac

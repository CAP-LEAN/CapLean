#!/usr/bin/env python3
"""
CapLean Trace Verifier

Two-phase verification:
  Phase A — Python quick check (verdict counting from JSONL)
  Phase B — Lean verified check (calls caplean-check binary)

The Lean checker's exit code is authoritative when available.
Exit codes: 0 = all pass, 1 = violations, 2 = missing files / parse error.
"""
import json, sys, os, subprocess

TRACE_PATH  = "/tmp/caplean_trace.jsonl"
CONFIG_PATH = "/tmp/caplean_config.json"
LEAN_BIN    = os.path.join(os.path.dirname(__file__), ".lake/build/bin/caplean-check")

# ── Phase A: Python quick check ─────────────────────────────────────

if not os.path.exists(TRACE_PATH):
    print("[CapLean] No trace file found.")
    print("         Run `python demo_agent.py` first to generate a trace.")
    sys.exit(2)

with open(TRACE_PATH) as f:
    ops = [json.loads(line) for line in f if line.strip()]

if not ops:
    print("[CapLean] Trace file is empty. Run `python demo_agent.py` first.")
    sys.exit(2)

blocked = [op for op in ops if op.get("verdict") == "BLOCKED"]
allowed = [op for op in ops if op.get("verdict") == "ALLOWED"]

print("=" * 60)
print("CapLean Trace Verification Report")
print("=" * 60)

print()
print("── Phase A: Python quick check ──")
print(f"Total ops : {len(ops)}")
print(f"Allowed   : {len(allowed)}")
print(f"Blocked   : {len(blocked)}")
print()

if allowed:
    print("Allowed operations:")
    for op in allowed:
        detail = op.get("path", op.get("cmd", op.get("pkg", op.get("snippet", op.get("url", "")))))
        print(f"   {op['op']:20s}  {detail}")

if blocked:
    print()
    print("Blocked violations:")
    for op in blocked:
        detail = op.get("path", op.get("cmd", op.get("pkg", "")))
        print(f"   {op['op']:20s}  {detail}")

python_ok = len(blocked) == 0
print()
print(f"Python verdict: {'PASS' if python_ok else 'FAIL — capability violations detected'}")

# ── Phase B: Lean verified check ────────────────────────────────────

print()
print("── Phase B: Lean verified check ──")

if not os.path.isfile(LEAN_BIN):
    print(f"[Warning] Lean checker not found at {LEAN_BIN}")
    print("         Run `lake build caplean-check` in CapLean/ to build it.")
    print("         Falling back to Python-only verdict.")
    print()
    print(f"RESULT: {'PASS' if python_ok else 'FAIL'} (Python-only, unverified)")
    sys.exit(0 if python_ok else 1)

if not os.path.exists(CONFIG_PATH):
    print(f"[Warning] Config file not found at {CONFIG_PATH}")
    print("         Use install_shims(cap, sandbox, dep_graph) to generate it.")
    print("         Falling back to Python-only verdict.")
    print()
    print(f"RESULT: {'PASS' if python_ok else 'FAIL'} (Python-only, unverified)")
    sys.exit(0 if python_ok else 1)

result = subprocess.run(
    [LEAN_BIN, "--trace", TRACE_PATH, "--config", CONFIG_PATH],
    capture_output=True, text=True,
)

if result.stdout.strip():
    for line in result.stdout.strip().splitlines():
        print(f"  {line}")
if result.stderr.strip():
    for line in result.stderr.strip().splitlines():
        print(f"  {line}")

lean_exit = result.returncode
print()

if lean_exit == 0:
    print("RESULT: PASS (verified by Lean)")
elif lean_exit == 1:
    print("RESULT: FAIL (verified by Lean)")
else:
    print(f"RESULT: ERROR (Lean checker exited with code {lean_exit})")

sys.exit(lean_exit)

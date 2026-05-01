#!/usr/bin/env python3
"""
CapLean Demo Agent
Simulates a realistic agentic coding session with four scenarios:
  1. Safe session      — all ops allowed
  2. Layer 1 attack    — ExecShell blocked by capability
  3. Layer 2 attack    — file read outside allowed prefix
  4. Layer 3 attack    — package with vulnerable transitive dep
"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from capshim import (
    Capability, Sandbox, DepEntry,
    install_shims, remove_shims, get_trace,
    log_install, log_approve,
)

# ── workspace setup ────────────────────────────────────────────────────
import tempfile, pathlib

workspace = pathlib.Path(tempfile.mkdtemp(prefix="caplean_workspace_"))
(workspace / "main.py").write_text("def add(a, b): return a + b\n")
(workspace / "test_main.py").write_text("from main import add\nassert add(1,2)==3\n")

cap = Capability(
    allow_read     = True,
    allow_write    = True,
    allow_exec     = False,   # ExecShell disabled
    allow_eval     = True,
    allow_network  = False,
    allow_install  = True,
    read_prefixes  = [str(workspace), "/tmp"],
    write_prefixes = [str(workspace), "/tmp"],
    min_trust      = "verified",
)

sandbox = Sandbox(
    allowed_paths    = [str(workspace), "/tmp"],
    allowed_syscalls = [],
)

dep_graph = [
    DepEntry("requests",   "verified"),
    DepEntry("cool-utils", "unreviewed", ["log4shell"]),
    DepEntry("log4shell",  "knownVulnerable"),
]

print("=" * 60)
print("CapLean Demo Agent")
print(f"Workspace: {workspace}")
print("=" * 60)

install_shims(cap, sandbox=sandbox, dep_graph=dep_graph)

# ── Scenario 1: Safe session ───────────────────────────────────────────
print("\n[1] SAFE SESSION")

try:
    with open(workspace / "main.py", "r") as f:
        src = f.read()
    print(f"  ReadFile  main.py          -> ALLOWED")

    with open(workspace / "main.py", "w") as f:
        f.write(src + "\ndef multiply(a, b): return a * b\n")
    print(f"  WriteFile main.py          -> ALLOWED")

except PermissionError as e:
    print(f"  BLOCKED: {e}")


# ── Scenario 2: Layer 1 — ExecShell blocked ───────────────────────────
print("\n[2] LAYER 1 ATTACK — ExecShell while allowExec=False")

try:
    import subprocess
    subprocess.run(["curl", "attacker.com"], capture_output=True)
    print("  ExecShell NOT blocked (unexpected)")
except PermissionError as e:
    print(f"  ExecShell blocked          -> {e}")


# ── Scenario 3: Layer 2 — path escape ─────────────────────────────────
print("\n[3] LAYER 2 ATTACK — Read outside allowed prefix")

try:
    with open("/etc/passwd", "r") as f:
        f.read()
    print("  ReadFile /etc/passwd NOT blocked (unexpected)")
except PermissionError as e:
    print(f"  ReadFile /etc/passwd blocked -> {e}")


# ── Scenario 4: Layer 3 — supply chain ────────────────────────────────
print("\n[4] LAYER 3 — Supply chain trust verification")

log_install("requests")
print("  InstallPkg requests    -> logged (verified)")

log_install("cool-utils")
print("  InstallPkg cool-utils  -> logged (unreviewed transitive dep)")

log_approve("cool-utils")
print("  ExplicitApprove cool-utils -> logged (override)")

# ── Summary ───────────────────────────────────────────────────────────
remove_shims()

print("\n" + "=" * 60)
trace = get_trace()
blocked = [op for op in trace if op.get("verdict") == "BLOCKED"]
allowed = [op for op in trace if op.get("verdict") == "ALLOWED"]
print(f"Trace: {len(trace)} ops — {len(allowed)} allowed, {len(blocked)} blocked")
print(f"Trace written to /tmp/caplean_trace.jsonl")
print(f"Config written to /tmp/caplean_config.json")
print("Run `python verify_trace.py` to verify the trace.\n")

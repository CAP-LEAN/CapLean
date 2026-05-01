"""
caplean_mcp.server — MCP stdio server exposing CapLean Layer 1 to Cursor.

Tools registered:

  caplean.set_policy        Set capability + sandbox + depGraph (resets trace).
  caplean.check_read        Layer 1 decision for a file read.
  caplean.check_write       Layer 1 decision for a file write.
  caplean.check_exec        Layer 1 decision for a shell command.
  caplean.check_eval        Layer 1 decision for a code-eval action.
  caplean.check_network     Layer 1 decision for a network fetch.
  caplean.check_install     Layer 1 decision for a package install.
  caplean.approve           Record ExplicitApprove for Layer 3 audit.
  caplean.get_trace         Return the in-memory JSONL trace.
  caplean.verify_session    Spawn `caplean-check` binary; return Layer 1/2/3 verdicts.

Layer 1 is enforced live: BLOCKED responses carry a reason the agent must
honour per .cursorrules. Layers 2 and 3 run only at session end via
`verify_session`. The trace + config files are the same ones the existing
`caplean-check` Lean binary already consumes.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from typing import Any, Optional

from caplean_mcp.policy import (
    CONFIG_PATH,
    TRACE_PATH,
    PolicyState,
)


def _resolve_lean_bin() -> str:
    """Locate the caplean-check binary built by `lake build`."""
    repo = os.environ.get("CAPLEAN_REPO")
    if repo:
        candidate = os.path.join(repo, ".lake", "build", "bin", "caplean-check")
        if os.path.isfile(candidate):
            return candidate
    here = os.path.dirname(os.path.abspath(__file__))
    candidate = os.path.normpath(os.path.join(here, "..", ".lake", "build", "bin", "caplean-check"))
    return candidate


def _verify_session(state: PolicyState) -> dict[str, Any]:
    bin_path = _resolve_lean_bin()
    if not os.path.isfile(bin_path):
        return {
            "ok": False,
            "error": f"caplean-check binary not found at {bin_path}. Run `lake build` in CapLean/.",
        }
    if not os.path.exists(CONFIG_PATH):
        return {"ok": False, "error": f"config file missing at {CONFIG_PATH}; call set_policy first."}

    # Blocked attempts are logged but were never executed; strip them so the
    # Lean checker only sees ops that actually ran.
    executed_path = TRACE_PATH + ".executed"
    with open(TRACE_PATH) as fin, open(executed_path, "w") as fout:
        for line in fin:
            if not line.strip():
                continue
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if obj.get("verdict") == "BLOCKED":
                continue
            fout.write(line if line.endswith("\n") else line + "\n")

    result = subprocess.run(
        [bin_path, "--trace", executed_path, "--config", CONFIG_PATH],
        capture_output=True,
        text=True,
    )
    layers: dict[str, str] = {}
    for line in result.stdout.splitlines():
        line = line.strip()
        if line.startswith("[Layer 1]"):
            layers["layer1"] = line
        elif line.startswith("[Layer 2]"):
            layers["layer2"] = line
        elif line.startswith("[Layer 3]"):
            layers["layer3"] = line
    return {
        "ok": result.returncode == 0,
        "exit_code": result.returncode,
        "layers": layers,
        "stdout": result.stdout,
        "stderr": result.stderr,
        "executed_trace": executed_path,
    }


def _build_server(state: PolicyState):
    from mcp.server.fastmcp import FastMCP

    mcp = FastMCP("caplean")

    @mcp.tool()
    def set_policy(
        capability: Optional[dict] = None,
        sandbox: Optional[dict] = None,
        dep_graph: Optional[list[dict]] = None,
    ) -> dict:
        """Declare the active CapLean policy. Resets the in-memory trace and
        rewrites /tmp/caplean_trace.jsonl + /tmp/caplean_config.json. The
        capability dict matches the schema in capshim.py:43-54. If omitted,
        Capability.from_json defaults in policy.py apply."""
        return state.set_policy(capability or {}, sandbox, dep_graph)

    @mcp.tool()
    def check_read(path: str) -> dict:
        """Layer 1 decision for reading `path`. Returns ALLOWED or BLOCKED.
        Agents must abort the corresponding native read on BLOCKED."""
        return state.check_read(path)

    @mcp.tool()
    def check_write(path: str) -> dict:
        """Layer 1 decision for writing `path`."""
        return state.check_write(path)

    @mcp.tool()
    def check_exec(cmd: str, args: Optional[list[str]] = None) -> dict:
        """Layer 1 decision for executing a shell command."""
        return state.check_exec(cmd, args or [])

    @mcp.tool()
    def check_eval(snippet: str) -> dict:
        """Layer 1 decision for evaluating arbitrary code."""
        return state.check_eval(snippet)

    @mcp.tool()
    def check_network(url: str) -> dict:
        """Layer 1 decision for a network fetch."""
        return state.check_network(url)

    @mcp.tool()
    def check_install(pkg: str) -> dict:
        """Layer 1 decision for installing a package. Layer 3 trust is
        evaluated at audit time by verify_session."""
        return state.check_install(pkg)

    @mcp.tool()
    def approve(pkg: str) -> dict:
        """Record an ExplicitApprove entry so Layer 3 will accept `pkg`
        even if its trust is below the floor."""
        return state.approve(pkg)

    @mcp.tool()
    def get_trace() -> list[dict]:
        """Return the in-memory trace (every check_* and approve call)."""
        return state.get_trace()

    @mcp.tool()
    def verify_session() -> dict:
        """Run the `caplean-check` Lean binary on the current trace + config.
        Returns Layer 1/2/3 verdicts. Blocked attempts are filtered before
        verification because they never executed."""
        return _verify_session(state)

    return mcp


def _self_test() -> int:
    """Exercise the policy module without touching MCP transport."""
    state = PolicyState()
    state.set_policy(
        capability={
            "allowRead": True, "allowWrite": True, "allowExec": False,
            "allowEval": True, "allowNetwork": False, "allowInstall": False,
            "readPrefixes": ["/workspace"], "writePrefixes": ["/workspace"],
            "minTrust": "verified",
        }
    )
    cases = [
        ("check_read /workspace/foo", state.check_read("/workspace/foo"), "ALLOWED"),
        ("check_read /etc/passwd",    state.check_read("/etc/passwd"),    "BLOCKED"),
        ("check_write /workspace/x",  state.check_write("/workspace/x"),  "ALLOWED"),
        ("check_exec rm",             state.check_exec("rm", ["-rf", "/"]), "BLOCKED"),
        ("check_eval print",          state.check_eval("print(1)"),       "ALLOWED"),
        ("check_network gh",          state.check_network("https://x"),   "BLOCKED"),
    ]
    failed = 0
    for label, result, expected in cases:
        ok = result["verdict"] == expected
        marker = "PASS" if ok else "FAIL"
        print(f"[{marker}] {label}: got {result['verdict']} ({result['reason']})")
        if not ok:
            failed += 1
    print(f"trace lines: {len(state.get_trace())}")
    print(f"trace file:  {TRACE_PATH}")
    print(f"config file: {CONFIG_PATH}")
    return 0 if failed == 0 else 1


def main() -> None:
    if "--self-test" in sys.argv:
        sys.exit(_self_test())
    state = PolicyState()
    server = _build_server(state)
    server.run()


if __name__ == "__main__":
    main()

# capshim.py — CapLean runtime enforcement shim
# Mirrors the Lean Capability predicate in Python.
# Every operation is logged to a JSON trace that Lean can verify.
#
# ── JSON serialization contract ──────────────────────────────────────
#
# TRACE (caplean_trace.jsonl) — one JSON object per line:
#   {"op":"ReadFile",        "path":"...",                     "verdict":"..."}
#   {"op":"WriteFile",       "path":"...", "content":"...",    "verdict":"..."}
#   {"op":"ExecShell",       "cmd":"...",  "args":["..."],     "verdict":"..."}
#   {"op":"EvalCode",        "snippet":"...",                  "verdict":"..."}
#   {"op":"InstallPkg",      "pkg":"...",                      "verdict":"..."}
#   {"op":"NetworkCall",     "url":"...",                      "verdict":"..."}
#   {"op":"ExplicitApprove", "pkg":"...",                      "verdict":"..."}
#
# CONFIG (caplean_config.json):
#   { "capability": { allowRead, allowWrite, allowExec, allowEval,
#                     allowNetwork, allowInstall, readPrefixes,
#                     writePrefixes, minTrust },
#     "sandbox":    { allowedPaths, allowedSyscalls },
#     "depGraph":   [{ name, trust, deps: [string] }] }
#
# Field names are camelCase and match the Lean structure fields exactly.
# "verdict" is for Python-side reporting only; Lean ignores it.
# ─────────────────────────────────────────────────────────────────────

import builtins, subprocess, json, os
from dataclasses import dataclass, field
from typing import Optional

@dataclass
class Capability:
    allow_read:     bool = True
    allow_write:    bool = True
    allow_exec:     bool = False
    allow_eval:     bool = True
    allow_network:  bool = False
    allow_install:  bool = False
    read_prefixes:  list = field(default_factory=lambda: ["/workspace"])
    write_prefixes: list = field(default_factory=lambda: ["/workspace"])
    min_trust:      str  = "verified"   # "verified" | "unreviewed" | "knownVulnerable"

    def to_json(self) -> dict:
        return {
            "allowRead": self.allow_read,
            "allowWrite": self.allow_write,
            "allowExec": self.allow_exec,
            "allowEval": self.allow_eval,
            "allowNetwork": self.allow_network,
            "allowInstall": self.allow_install,
            "readPrefixes": self.read_prefixes,
            "writePrefixes": self.write_prefixes,
            "minTrust": self.min_trust,
        }

@dataclass
class Sandbox:
    allowed_paths:    list = field(default_factory=lambda: ["/workspace"])
    allowed_syscalls: list = field(default_factory=list)

    def to_json(self) -> dict:
        return {
            "allowedPaths": self.allowed_paths,
            "allowedSyscalls": self.allowed_syscalls,
        }

@dataclass
class DepEntry:
    name:  str
    trust: str   # "verified" | "unreviewed" | "knownVulnerable"
    deps:  list[str] = field(default_factory=list)

    def to_json(self) -> dict:
        return {"name": self.name, "trust": self.trust, "deps": self.deps}

_trace: list[dict] = []
_cap: Optional[Capability] = None
_trace_path  = "/tmp/caplean_trace.jsonl"
_config_path = "/tmp/caplean_config.json"

def _log(op: dict) -> None:
    _trace.append(op)
    with _original_open(_trace_path, "a") as f:
        f.write(json.dumps(op) + "\n")

def _block(op: dict) -> None:
    _log({**op, "verdict": "BLOCKED"})
    raise PermissionError(
        f"[CapLean] BLOCKED: {op['op']} is outside declared capability"
    )

def _safe_open(path, mode="r", *args, **kwargs):
    global _cap
    path = str(path)
    if _cap and "r" in mode:
        if not _cap.allow_read:
            _block({"op": "ReadFile", "path": path})
        if not any(path.startswith(p) for p in _cap.read_prefixes):
            _block({"op": "ReadFile", "path": path})
        _log({"op": "ReadFile", "path": path, "verdict": "ALLOWED"})
    elif _cap and ("w" in mode or "a" in mode):
        if not _cap.allow_write:
            _block({"op": "WriteFile", "path": path})
        if not any(path.startswith(p) for p in _cap.write_prefixes):
            _block({"op": "WriteFile", "path": path})
        _log({"op": "WriteFile", "path": path, "verdict": "ALLOWED"})
    return _original_open(path, mode, *args, **kwargs)

def _safe_run(args, **kwargs):
    global _cap
    cmd = args[0] if isinstance(args, list) else args
    arg_list = [str(a) for a in args[1:]] if isinstance(args, list) else []
    if _cap and not _cap.allow_exec:
        _block({"op": "ExecShell", "cmd": str(cmd), "args": arg_list})
    _log({"op": "ExecShell", "cmd": str(cmd), "args": arg_list, "verdict": "ALLOWED"})
    return _original_run(args, **kwargs)

_original_open = builtins.open
_original_run  = subprocess.run

def install_shims(
    cap: Capability,
    sandbox: Optional[Sandbox] = None,
    dep_graph: Optional[list[DepEntry]] = None,
) -> None:
    global _cap
    _cap = cap
    builtins.open   = _safe_open
    subprocess.run  = _safe_run
    _original_open(_trace_path, "w").close()   # reset trace
    config = {
        "capability": cap.to_json(),
        "sandbox": (sandbox or Sandbox()).to_json(),
        "depGraph": [e.to_json() for e in (dep_graph or [])],
    }
    with _original_open(_config_path, "w") as f:
        json.dump(config, f, indent=2)
    print(f"[CapLean] Shims active. Tracing to {_trace_path}")
    print(f"[CapLean] Config written to {_config_path}")

def remove_shims() -> None:
    builtins.open  = _original_open
    subprocess.run = _original_run

def get_trace() -> list[dict]:
    return _trace.copy()

# ── Explicit logging for ops the shim can't intercept automatically ──

def log_eval(snippet: str) -> None:
    _log({"op": "EvalCode", "snippet": snippet, "verdict": "ALLOWED"})

def log_network(url: str) -> None:
    _log({"op": "NetworkCall", "url": url, "verdict": "ALLOWED"})

def log_install(pkg: str) -> None:
    _log({"op": "InstallPkg", "pkg": pkg, "verdict": "ALLOWED"})

def log_approve(pkg: str) -> None:
    _log({"op": "ExplicitApprove", "pkg": pkg, "verdict": "ALLOWED"})
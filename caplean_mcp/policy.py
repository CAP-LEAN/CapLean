"""
caplean_mcp.policy — Layer 1 capability decision logic.

Mirrors `withinScopeBool` from CapLean/CapCore.lean and the prefix
checks in capshim.py. The trace + config files written here are the
exact format consumed by the `caplean-check` Lean binary, so the
post-hoc certification path stays identical.

Wire formats are documented at the top of capshim.py.
"""
from __future__ import annotations

import json
import os
from dataclasses import dataclass, field, asdict
from typing import Any, Optional

TRACE_PATH = "/tmp/caplean_trace.jsonl"
CONFIG_PATH = "/tmp/caplean_config.json"


@dataclass
class Capability:
    allowRead: bool = True
    allowWrite: bool = True
    allowExec: bool = False
    allowEval: bool = True
    allowNetwork: bool = False
    allowInstall: bool = False
    readPrefixes: list[str] = field(default_factory=lambda: ["/workspace"])
    writePrefixes: list[str] = field(default_factory=lambda: ["/workspace"])
    minTrust: str = "verified"  # "verified" | "unreviewed" | "knownVulnerable"

    @classmethod
    def from_json(cls, j: dict[str, Any]) -> "Capability":
        return cls(
            allowRead=bool(j.get("allowRead", True)),
            allowWrite=bool(j.get("allowWrite", True)),
            allowExec=bool(j.get("allowExec", False)),
            allowEval=bool(j.get("allowEval", True)),
            allowNetwork=bool(j.get("allowNetwork", False)),
            allowInstall=bool(j.get("allowInstall", False)),
            readPrefixes=list(j.get("readPrefixes", ["/home/wolfie/Lean/CapLean/CapLean/"])),
            writePrefixes=list(j.get("writePrefixes", ["/home/wolfie/Lean/CapLean/CapLean/"])),
            minTrust=str(j.get("minTrust", "verified")),
        )


@dataclass
class Sandbox:
    allowedPaths: list[str] = field(default_factory=lambda: ["/workspace"])
    allowedSyscalls: list[str] = field(default_factory=list)


@dataclass
class DepEntry:
    name: str
    trust: str = "unreviewed"
    deps: list[str] = field(default_factory=list)


VALID_TRUST = {"verified", "unreviewed", "knownVulnerable"}


def _validate_trust(t: str) -> None:
    if t not in VALID_TRUST:
        raise ValueError(f"unknown trust level: {t!r} (expected one of {sorted(VALID_TRUST)})")


class PolicyState:
    """In-memory CapLean policy state, persisted alongside JSONL trace."""

    def __init__(self) -> None:
        self.capability: Optional[Capability] = None
        self.sandbox: Sandbox = Sandbox()
        self.dep_graph: list[DepEntry] = []
        self.trace: list[dict[str, Any]] = []

    def set_policy(
        self,
        capability: dict[str, Any],
        sandbox: Optional[dict[str, Any]] = None,
        dep_graph: Optional[list[dict[str, Any]]] = None,
    ) -> dict[str, str]:
        cap = Capability.from_json(capability)
        _validate_trust(cap.minTrust)
        self.capability = cap
        self.sandbox = Sandbox(**(sandbox or {}))
        graph: list[DepEntry] = []
        for entry in dep_graph or []:
            _validate_trust(str(entry.get("trust", "unreviewed")))
            graph.append(
                DepEntry(
                    name=str(entry["name"]),
                    trust=str(entry.get("trust", "unreviewed")),
                    deps=list(entry.get("deps", [])),
                )
            )
        self.dep_graph = graph
        self.trace = []

        # Reset trace file.
        with open(TRACE_PATH, "w"):
            pass
        # Write config in the schema caplean-check consumes.
        config = {
            "capability": asdict(cap),
            "sandbox": asdict(self.sandbox),
            "depGraph": [asdict(e) for e in graph],
        }
        with open(CONFIG_PATH, "w") as f:
            json.dump(config, f, indent=2)
        return {"trace": TRACE_PATH, "config": CONFIG_PATH}

    def _require_policy(self) -> Capability:
        if self.capability is None:
            raise RuntimeError(
                "CapLean policy not set. Call caplean.set_policy first with a capability JSON."
            )
        return self.capability

    def _log(self, entry: dict[str, Any]) -> None:
        self.trace.append(entry)
        with open(TRACE_PATH, "a") as f:
            f.write(json.dumps(entry) + "\n")

    # ── Layer 1 decisions (mirror withinScopeBool in CapCore.lean) ──

    def check_read(self, path: str) -> dict[str, str]:
        cap = self._require_policy()
        if not cap.allowRead:
            return self._decide("ReadFile", {"path": path}, False, "allowRead is false")
        if not any(path.startswith(p) for p in cap.readPrefixes):
            return self._decide(
                "ReadFile", {"path": path}, False,
                f"path {path!r} outside readPrefixes {cap.readPrefixes}",
            )
        return self._decide("ReadFile", {"path": path}, True, "within readPrefixes")

    def check_write(self, path: str) -> dict[str, str]:
        cap = self._require_policy()
        if not cap.allowWrite:
            return self._decide("WriteFile", {"path": path}, False, "allowWrite is false")
        if not any(path.startswith(p) for p in cap.writePrefixes):
            return self._decide(
                "WriteFile", {"path": path}, False,
                f"path {path!r} outside writePrefixes {cap.writePrefixes}",
            )
        return self._decide("WriteFile", {"path": path}, True, "within writePrefixes")

    def check_exec(self, cmd: str, args: Optional[list[str]] = None) -> dict[str, str]:
        cap = self._require_policy()
        args = list(args or [])
        op = {"cmd": cmd, "args": args}
        if not cap.allowExec:
            return self._decide("ExecShell", op, False, "allowExec is false")
        return self._decide("ExecShell", op, True, "execShell allowed")

    def check_eval(self, snippet: str) -> dict[str, str]:
        cap = self._require_policy()
        op = {"snippet": snippet}
        if not cap.allowEval:
            return self._decide("EvalCode", op, False, "allowEval is false")
        return self._decide("EvalCode", op, True, "evalCode allowed")

    def check_network(self, url: str) -> dict[str, str]:
        cap = self._require_policy()
        op = {"url": url}
        if not cap.allowNetwork:
            return self._decide("NetworkCall", op, False, "allowNetwork is false")
        return self._decide("NetworkCall", op, True, "networkCall allowed")

    def check_install(self, pkg: str) -> dict[str, str]:
        cap = self._require_policy()
        op = {"pkg": pkg}
        if not cap.allowInstall:
            return self._decide("InstallPkg", op, False, "allowInstall is false")
        return self._decide("InstallPkg", op, True, "installPkg allowed (Layer 3 checked post-hoc)")

    def approve(self, pkg: str) -> dict[str, str]:
        # Approvals are always logged; Layer 3 uses them at audit time.
        return self._decide("ExplicitApprove", {"pkg": pkg}, True, "explicit approval recorded")

    def _decide(
        self, op: str, body: dict[str, Any], allowed: bool, reason: str
    ) -> dict[str, str]:
        verdict = "ALLOWED" if allowed else "BLOCKED"
        entry = {"op": op, **body, "verdict": verdict}
        self._log(entry)
        return {"verdict": verdict, "reason": reason}

    def get_trace(self) -> list[dict[str, Any]]:
        return list(self.trace)

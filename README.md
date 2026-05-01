# CAPLean(Capability Access Protocol with Lean) — Proved Capability Envelope for Agentic Coding Pipelines

## What it is
A Lean 4 library that models agentic coding tools as free monads over
a declared operation set, and proves three families of safety theorems
over traces of those monads.

A Python-to-Lean bridge lets you enforce policies at runtime (Python)
and verify traces post-hoc against the same formal definitions the
theorems are proved over (Lean).

## Three layers
| Layer | File | Theorem | What it catches |
|---|---|---|---|
| Capability | `SafetySpine.lean` | `capabilityEnvelope` | Ops outside declared capability |
| Sandbox | `Sandbox.lean` | `sandboxContainment`, `canonicalContainment`, `conservativeContainment`, `certifiedSandboxContainment`, `fullEnvelope` | Effects outside declared path boundary |
| Trust | `TrustLattice.lean` | `trustMonotonicity` | Packages below trust floor |

## Honest scope

**Capability layer (Layer 1)** — enforces containment **by construction**.
`AgentM` is indexed by a `Capability`, and each operation carries a
compile-time proof that it is within scope. Programs containing
out-of-scope ops are rejected by the type checker — no runtime check needed.

**Sandbox layer (Layer 2)** — three tiers of trust for effect containment:

| Tier | Mechanism | Trust assumption |
|---|---|---|
| **Transparent ops** | `canonicalEffects` derives effects structurally from the op (file I/O, network) | None — correctness is definitional |
| **Conservative mode** | `maximalBound sb` assumes opaque ops can do *anything the sandbox allows* | None per-op — the sandbox boundary is the bound |
| **Certified mode** | Custom `OpaqueBound` paired with `RuntimeEnforces` axiom (`CertifiedBound`) | Explicit — the axiom appears in every proof term that depends on it |

File paths are normalized (`.` and `..` resolved) before prefix checking,
so traversal attacks like `/workspace/../../etc/passwd` are rejected.

`fullEnvelope` combines Layer 1 + Layer 2 into a single theorem: an
`AgentM` program is both capability-safe and sandbox-safe.

**Trust layer (Layer 3)** — proves that *if* the declared dependency graph
is accurate, every install meets the trust floor or was explicitly approved.
It does not verify the graph against a live registry.

## Architecture

```
Python side                         Lean side
───────────                         ─────────
capshim.py                          CapLean/ (library + theorems)
  ├─ runtime enforcement              ├─ AgentOp, CapCore, Sandbox, TrustLattice
  ├─ writes trace JSONL                │
  └─ writes config JSON              Check/
                                       ├─ TraceJSON.lean (JSON parsers)
verify_trace.py                        └─ Main.lean (caplean-check binary)
  ├─ Phase A: Python quick check             ▲
  └─ Phase B: calls caplean-check ───────────┘
```

Two files flow from Python to Lean:
- **Trace** (`/tmp/caplean_trace.jsonl`) — one JSON object per op, logged at runtime
- **Config** (`/tmp/caplean_config.json`) — capability, sandbox, and dep graph policy

See [SCHEMA.md](SCHEMA.md) for the full serialization contract.

## Running

```bash
# Prove all theorems (~30s)
lake build

# Build the verified checker binary
lake build caplean-check

# Run the demo agent (generates trace + config)
python demo_agent.py

# Verify the trace (Python quick check + Lean verified check)
python verify_trace.py

# Or call the Lean checker directly
.lake/build/bin/caplean-check
.lake/build/bin/caplean-check --trace /path/to/trace.jsonl --config /path/to/config.json
```

## Python bridge

`capshim.py` provides runtime enforcement and trace logging:

```python
from capshim import Capability, Sandbox, DepEntry, install_shims

cap = Capability(allow_read=True, allow_write=True, allow_exec=False, ...)
sandbox = Sandbox(allowed_paths=["/workspace"])
deps = [DepEntry("requests", "verified")]

install_shims(cap, sandbox=sandbox, dep_graph=deps)
# Now open() and subprocess.run() are intercepted and logged.
# /tmp/caplean_trace.jsonl and /tmp/caplean_config.json are written.
```

For ops the shim can't intercept automatically:
```python
from capshim import log_eval, log_network, log_install, log_approve

log_install("requests")
log_approve("cool-utils")
```

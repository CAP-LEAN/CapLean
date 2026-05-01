import CapLean.CapCore
import CapLean.AgentM
import CapLean.Trace

namespace CapLean

/-!
## Capability — External Trace Checking

**Purpose:** Decide capability scope for traces that come from outside Lean
(e.g. JSONL produced by the Python shim) where the type-level guarantee of
`AgentM` does not apply.

**Key definitions:**
- `traceWithinScopeBool` / `traceWithinScope` — every op in the trace fits the cap
- `firstViolation` — first out-of-scope op, if any
- `enforceTrace` — `Except AgentOp Unit` wrapper used by `Check/Main.lean`

**Key theorems:** none here — `capabilityEnvelope` (by-construction version)
lives in `SafetySpine`.

**Assumptions:** For external traces, this is the only enforcement point.
For programs written in `AgentM`, these checks are redundant.
-/

/-- Bool check: every op in the trace fits the capability. -/
def traceWithinScopeBool (t : Trace) (cap : Capability) : Bool :=
  t.all (withinScopeBool · cap)

/-- Prop version of `traceWithinScopeBool`, automatically Decidable. -/
def traceWithinScope (t : Trace) (cap : Capability) : Prop :=
  traceWithinScopeBool t cap = true

instance (t : Trace) (cap : Capability) : Decidable (traceWithinScope t cap) :=
  inferInstanceAs (Decidable (traceWithinScopeBool t cap = true))

/-- First op in the trace that violates the capability, if any. -/
def firstViolation (t : Trace) (cap : Capability) : Option AgentOp :=
  t.find? (fun op => !withinScopeBool op cap)

/--
Enforce capability on an external trace (e.g. deserialized from the Python
shim). For by-construction programs this is redundant — the type already
guarantees scope.
-/
def enforceTrace (t : Trace) (cap : Capability) : Except AgentOp Unit :=
  match firstViolation t cap with
  | some op => Except.error op
  | none    => Except.ok ()

end CapLean

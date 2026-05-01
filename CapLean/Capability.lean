import CapLean.CapCore
import CapLean.AgentM
import CapLean.Trace

namespace CapLean

def traceWithinScopeBool (t : Trace) (cap : Capability) : Bool :=
  t.all (withinScopeBool · cap)

def traceWithinScope (t : Trace) (cap : Capability) : Prop :=
  traceWithinScopeBool t cap = true

instance (t : Trace) (cap : Capability) : Decidable (traceWithinScope t cap) :=
  inferInstanceAs (Decidable (traceWithinScopeBool t cap = true))

/-- First violating op in the trace, if any -/
def firstViolation (t : Trace) (cap : Capability) : Option AgentOp :=
  t.find? (fun op => !withinScopeBool op cap)

/-- Enforce capability on an external trace (e.g. deserialized from the Python shim).
    For by-construction programs this is redundant — the type already guarantees scope. -/
def enforceTrace (t : Trace) (cap : Capability) : Except AgentOp Unit :=
  match firstViolation t cap with
  | some op => Except.error op
  | none    => Except.ok ()

end CapLean

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

/-- Enforce capability: returns error with the violating op, or Ok () -/
def enforceCapability (prog : AgentM α) (cap : Capability)
    : Except AgentOp Unit :=
  match firstViolation prog.collectTrace cap with
  | some op => Except.error op
  | none    => Except.ok ()

end CapLean

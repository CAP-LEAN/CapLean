import CapLean.AgentOp
import CapLean.AgentM
import CapLean.Trace

namespace CapLean

inductive TrustLevel where
  | knownVulnerable
  | unreviewed
  | verified
  deriving Repr, DecidableEq, Ord, BEq

structure Capability where
  allowRead     : Bool
  allowWrite    : Bool
  allowExec     : Bool
  allowEval     : Bool
  allowNetwork  : Bool
  allowInstall  : Bool
  readPrefixes  : List String
  writePrefixes : List String
  minTrust      : TrustLevel

/-- Computable Bool check — primary definition -/
def withinScopeBool : AgentOp → Capability → Bool
  | .readFile path,    cap =>
      cap.allowRead && cap.readPrefixes.any (path.startsWith ·)
  | .writeFile path _, cap =>
      cap.allowWrite && cap.writePrefixes.any (path.startsWith ·)
  | .execShell _ _,    cap => cap.allowExec
  | .evalCode _,       cap => cap.allowEval
  | .networkCall _,    cap => cap.allowNetwork
  | .installPkg _,     cap => cap.allowInstall

def traceWithinScopeBool (t : Trace) (cap : Capability) : Bool :=
  t.all (withinScopeBool · cap)

/-- Prop version derived from Bool — automatically Decidable -/
def withinScope (op : AgentOp) (cap : Capability) : Prop :=
  withinScopeBool op cap = true

def traceWithinScope (t : Trace) (cap : Capability) : Prop :=
  traceWithinScopeBool t cap = true

instance (op : AgentOp) (cap : Capability) : Decidable (withinScope op cap) :=
  inferInstanceAs (Decidable (withinScopeBool op cap = true))

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

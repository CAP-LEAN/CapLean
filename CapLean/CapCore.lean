import CapLean.AgentOp

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
  | .explicitApprove _, cap => cap.allowInstall

/-- Prop version derived from Bool — automatically Decidable -/
def withinScope (op : AgentOp) (cap : Capability) : Prop :=
  withinScopeBool op cap = true

instance (op : AgentOp) (cap : Capability) : Decidable (withinScope op cap) :=
  inferInstanceAs (Decidable (withinScopeBool op cap = true))

end CapLean

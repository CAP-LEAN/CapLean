import CapLean.AgentOp

namespace CapLean

/-!
## CapCore — Capability and Trust Level

**Purpose:** Core data types for declaring what an agent is allowed to do.

**Key definitions:**
- `TrustLevel` — three-point lattice (`knownVulnerable < unreviewed < verified`)
- `Capability` — boolean flags + path prefixes + minimum trust floor
- `withinScopeBool` / `withinScope` — predicate "does this op fit this cap?"

**Key theorems:** none — predicates are decidable by construction.

**Assumptions:** `Capability` is the ground truth for what an agent may do;
no policy is inferred from the environment.
-/

/-- Three-point trust lattice for packages: vulnerable < unreviewed < verified -/
inductive TrustLevel where
  | knownVulnerable
  | unreviewed
  | verified
  deriving Repr, DecidableEq, Ord, BEq

/--
A capability declares what an agent may do: which op categories are
permitted, which path prefixes may be read/written, and the minimum
trust floor for package installs.
-/
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

/--
Computable Bool check: is the given op within the declared capability?
This is the primary definition; the Prop version `withinScope` is derived
so it inherits decidability automatically.
-/
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

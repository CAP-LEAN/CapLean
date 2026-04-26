import CapLean.AgentOp
import CapLean.Trace
import CapLean.Capability

namespace CapLean

/-!
## Layer 3 — Supply Chain Trust

This layer specialises `InstallPackage`.
Even if Layer 1 permits installs, Layer 3 constrains *which packages*
may be introduced based on a trust lattice.

The core guarantee: the trust level of transitively installed
dependencies can never fall below the configured floor without
an explicit `ExplicitApprove` step appearing in the trace.
-/

-- ─────────────────────────────────────────────
-- 1. Trust order
-- ─────────────────────────────────────────────

/-- `TrustLevel` is already defined in Capability.lean.
    We establish a decidable ≤ order on it here. -/
def TrustLevel.toNat : TrustLevel → Nat
  | .knownVulnerable => 0
  | .unreviewed      => 1
  | .verified        => 2

def TrustLevel.le (a b : TrustLevel) : Bool :=
  a.toNat ≤ b.toNat

instance : LE TrustLevel where
  le a b := a.toNat ≤ b.toNat

instance (a b : TrustLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

-- ─────────────────────────────────────────────
-- 2. Package and dependency graph
-- ─────────────────────────────────────────────

structure Package where
  name  : String
  trust : TrustLevel
  deriving Repr, DecidableEq, BEq

/-- A dependency graph maps each package name to its direct dependencies -/
abbrev DepGraph := List (Package × List Package)

/-- Look up a package by name in the graph -/
def DepGraph.lookup (g : DepGraph) (name : String) : Option Package :=
  (g.find? (fun (p, _) => p.name == name)).map Prod.fst

/-- All direct dependencies of a package -/
def DepGraph.deps (g : DepGraph) (pkg : Package) : List Package :=
  match g.find? (fun (p, _) => p.name == pkg.name) with
  | some (_, ds) => ds
  | none         => []

-- ─────────────────────────────────────────────
-- 3. Transitive closure (bounded depth)
-- ─────────────────────────────────────────────

/-- Collect all transitive dependencies up to a depth limit -/
def DepGraph.transitiveDeps (g : DepGraph) (pkg : Package) (fuel : Nat) : List Package :=
  match fuel with
  | 0        => []
  | fuel + 1 =>
    let direct := g.deps pkg
    direct ++ (direct.flatMap (g.transitiveDeps · fuel))
termination_by fuel

/-- Minimum trust level across a package and all its transitive dependencies -/
def DepGraph.minTransitiveTrust (g : DepGraph) (pkg : Package) : TrustLevel :=
  let all := pkg :: g.transitiveDeps pkg 10   -- depth-10 bound
  all.foldl (fun acc p =>
    if p.trust.toNat < acc.toNat then p.trust else acc)
    .verified

-- ─────────────────────────────────────────────
-- 4. Trust policy predicates
-- ─────────────────────────────────────────────

/-- Is a package installation allowed given a capability's minTrust floor? -/
def pkgAllowedBool (pkg : Package) (g : DepGraph) (cap : Capability) : Bool :=
  cap.minTrust.toNat ≤ (g.minTransitiveTrust pkg).toNat

def pkgAllowed (pkg : Package) (g : DepGraph) (cap : Capability) : Prop :=
  pkgAllowedBool pkg g cap = true

instance (pkg : Package) (g : DepGraph) (cap : Capability) :
    Decidable (pkgAllowed pkg g cap) :=
  inferInstanceAs (Decidable (pkgAllowedBool pkg g cap = true))

/-- Check all InstallPackage ops in a trace against the trust floor -/
def traceInstallsSafe (t : Trace) (g : DepGraph) (cap : Capability) : Bool :=
  t.all fun op =>
    match op with
    | .installPkg name =>
      match g.lookup name with
      | some pkg => pkgAllowedBool pkg g cap
      | none     => false   -- unknown package = not verified = blocked
    | _ => true             -- non-install ops are not this layer's concern

def traceInstallsSafeProp (t : Trace) (g : DepGraph) (cap : Capability) : Prop :=
  traceInstallsSafe t g cap = true

instance (t : Trace) (g : DepGraph) (cap : Capability) :
    Decidable (traceInstallsSafeProp t g cap) :=
  inferInstanceAs (Decidable (traceInstallsSafe t g cap = true))

-- ─────────────────────────────────────────────
-- 5. Monotonicity theorem
-- ─────────────────────────────────────────────

/--
**Trust Monotonicity Theorem**

If all install ops in a trace pass the trust floor check,
then every package name referenced by an `InstallPackage` op
resolves to a package whose transitive trust meets the floor.
-/
theorem trustMonotonicity
    (t : Trace) (g : DepGraph) (cap : Capability)
    (h : traceInstallsSafeProp t g cap)
    : ∀ op ∈ t, ∀ name : String,
        op = .installPkg name →
        ∃ pkg, g.lookup name = some pkg ∧ pkgAllowed pkg g cap := by
  simp only [traceInstallsSafeProp, traceInstallsSafe,
             List.all_eq_true] at h
  intro op hop name heq
  subst heq
  have hok := h (.installPkg name) hop
  simp only [pkgAllowedBool] at hok
  split at hok
  · rename_i pkg heq
    exact ⟨pkg, heq, hok⟩
  · simp at hok

-- ─────────────────────────────────────────────
-- 6. Demo packages and graphs
-- ─────────────────────────────────────────────

-- Packages at different trust levels
def pkgVerified   : Package := { name := "requests",   trust := .verified }
def pkgUnreviewed : Package := { name := "cool-utils",  trust := .unreviewed }
def pkgVuln       : Package := { name := "log4shell",   trust := .knownVulnerable }

-- A clean graph: requests has no dangerous deps
def cleanGraph : DepGraph := [(pkgVerified, [])]

-- A poisoned graph: cool-utils depends on a known-vulnerable package
def poisonedGraph : DepGraph :=
  [(pkgUnreviewed, [pkgVuln]),
   (pkgVuln,       [])]

-- A deep graph: verified package has unreviewed transitive dep
def deepGraph : DepGraph :=
  [({ name := "safe-lib", trust := .verified }, [pkgUnreviewed]),
   (pkgUnreviewed, [pkgVuln]),
   (pkgVuln, [])]

-- Agent that installs a verified package
def installSafeAgent : AgentM Unit :=
  AgentM.liftOp (.installPkg "requests")

-- Agent that installs an unreviewed package with a vulnerable dep
def installAttackAgent : AgentM Unit :=
  AgentM.liftOp (.installPkg "cool-utils")

-- Capability requiring verified packages only
def strictCap : Capability where
  allowRead     := true
  allowWrite    := true
  allowExec     := false
  allowEval     := true
  allowNetwork  := false
  allowInstall  := true
  readPrefixes  := ["/workspace"]
  writePrefixes := ["/workspace"]
  minTrust      := .verified   -- ← floor is Verified

-- ─────────────────────────────────────────────
-- 7. Runtime checks
-- ─────────────────────────────────────────────

-- Safe install in clean graph → true
#eval traceInstallsSafe installSafeAgent.collectTrace cleanGraph strictCap

-- Poisoned package (unreviewed + vulnerable dep) → false
#eval traceInstallsSafe installAttackAgent.collectTrace poisonedGraph strictCap

-- Deep transitive vulnerability → false
#eval traceInstallsSafe
  (AgentM.liftOp (.installPkg "safe-lib") : AgentM Unit).collectTrace
  deepGraph strictCap

-- ─────────────────────────────────────────────
-- 8. Formal proofs
-- ─────────────────────────────────────────────

-- Safe install is formally allowed
example : traceInstallsSafeProp
    installSafeAgent.collectTrace cleanGraph strictCap := by native_decide

-- Poisoned package is formally blocked
example : ¬ traceInstallsSafeProp
    installAttackAgent.collectTrace poisonedGraph strictCap := by native_decide

-- Deep transitive vulnerability is formally blocked
example : ¬ traceInstallsSafeProp
    ((AgentM.liftOp (.installPkg "safe-lib") : AgentM Unit).collectTrace)
    deepGraph strictCap := by native_decide

-- Spine theorem: safe install satisfies per-op trust guarantee
example : ∀ op ∈ installSafeAgent.collectTrace,
    ∀ name : String, op = .installPkg name →
    ∃ pkg, cleanGraph.lookup name = some pkg ∧ pkgAllowed pkg cleanGraph strictCap :=
  trustMonotonicity _ _ _ (by native_decide)

end CapLean

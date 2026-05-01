import CapLean.AgentOp
import CapLean.Trace
import CapLean.Capability

namespace CapLean

/-!
## Layer 3 — Supply Chain Trust

### Trust model (honest scope)
`traceInstallsSafe` is a specification-level check. It proves that *if* the
declared packages and graph are accurate, every install meets the trust floor
or was explicitly approved. It does not verify the graph against a live registry.
-/

-- ── 1. Total order on TrustLevel ─────────────────────────────────────

def TrustLevel.toNat : TrustLevel → Nat
  | .knownVulnerable => 0
  | .unreviewed      => 1
  | .verified        => 2

instance : LE TrustLevel := ⟨fun a b => a.toNat ≤ b.toNat⟩

instance (a b : TrustLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

-- ── 2. Package graph ─────────────────────────────────────────────────

structure Package where
  name  : String
  trust : TrustLevel
  deriving Repr, DecidableEq, BEq

abbrev DepGraph := List (Package × List Package)

def DepGraph.lookup (g : DepGraph) (name : String) : Option Package :=
  (g.find? (fun e => e.1.name == name)).map (fun e => e.1)

def DepGraph.deps (g : DepGraph) (pkg : Package) : List Package :=
  match g.find? (fun e => e.1.name == pkg.name) with
  | some e => e.2
  | none   => []

-- ── 3. Transitive closure (fuel-bounded) ─────────────────────────────

def DepGraph.transitiveDeps (g : DepGraph) (pkg : Package) : Nat → List Package
  | 0     => []
  | n + 1 =>
    let direct := g.deps pkg
    direct ++ direct.flatMap (g.transitiveDeps · n)

def DepGraph.minTransitiveTrust (g : DepGraph) (pkg : Package) : TrustLevel :=
  (pkg :: g.transitiveDeps pkg 10).foldl
    (fun acc p => if p.trust.toNat < acc.toNat then p.trust else acc)
    .verified

-- ── 4. Policy predicates ─────────────────────────────────────────────

def pkgAllowedBool (pkg : Package) (g : DepGraph) (cap : Capability) : Bool :=
  Nat.ble cap.minTrust.toNat (g.minTransitiveTrust pkg).toNat

def pkgAllowed (pkg : Package) (g : DepGraph) (cap : Capability) : Prop :=
  pkgAllowedBool pkg g cap = true

instance {pkg : Package} {g : DepGraph} {cap : Capability} :
    Decidable (pkgAllowed pkg g cap) :=
  inferInstanceAs (Decidable (pkgAllowedBool pkg g cap = true))

/--
Check all `installPkg` ops in a trace.
A package passes if it was explicitly approved earlier in the trace,
or if its transitive trust meets `cap.minTrust`.
-/
def traceInstallsSafe (t : Trace) (g : DepGraph) (cap : Capability) : Bool :=
  t.all fun op =>
    match op with
    | .installPkg name =>
        t.any (· == .explicitApprove name) ||
        match g.lookup name with
        | some pkg => pkgAllowedBool pkg g cap
        | none     => false
    | _ => true

def traceInstallsSafeProp (t : Trace) (g : DepGraph) (cap : Capability) : Prop :=
  traceInstallsSafe t g cap = true

instance {t : Trace} {g : DepGraph} {cap : Capability} :
    Decidable (traceInstallsSafeProp t g cap) :=
  inferInstanceAs (Decidable (traceInstallsSafe t g cap = true))

-- ── 5. Simple structural lemma ────────────────────────────────────────

/-- The empty trace is trivially safe under any policy. -/
theorem traceInstallsSafe_nil (g : DepGraph) (cap : Capability) :
    traceInstallsSafeProp [] g cap := by
  simp [traceInstallsSafeProp, traceInstallsSafe]

-- ── 6. Core safety theorem ────────────────────────────────────────────

/--
**Trust Monotonicity Theorem**

If a trace passes the trust check, then every `installPkg` op either:
- was explicitly approved in the same trace, OR
- names a package whose transitive trust meets the configured floor.
-/
theorem trustMonotonicity
    (t : Trace) (g : DepGraph) (cap : Capability)
    (h : traceInstallsSafeProp t g cap)
    : ∀ op ∈ t, ∀ name : String,
        op = .installPkg name →
        t.any (· == .explicitApprove name) = true ∨
        ∃ pkg, g.lookup name = some pkg ∧ pkgAllowed pkg g cap := by
  unfold traceInstallsSafeProp traceInstallsSafe at h
  rw [List.all_eq_true] at h
  intro op hop name heq
  subst heq
  have hok := h (.installPkg name) hop
  -- Use `change` to force iota-reduction of the match definitionally,
  -- avoiding reliance on simp reducing the constructor application.
  change (t.any (· == .explicitApprove name) ||
          match g.lookup name with
          | some pkg => pkgAllowedBool pkg g cap
          | none => false) = true at hok
  by_cases h_approved : t.any (· == .explicitApprove name) = true
  · exact Or.inl h_approved
  · right
    have h_false : t.any (· == .explicitApprove name) = false := by
      revert h_approved
      cases t.any (· == .explicitApprove name) <;> simp
    rw [h_false] at hok
    simp only [Bool.false_or] at hok
    cases h_lookup : g.lookup name with
    | none     => simp [h_lookup] at hok
    | some pkg =>
      simp only [h_lookup] at hok
      exact ⟨pkg, rfl, hok⟩

end CapLean

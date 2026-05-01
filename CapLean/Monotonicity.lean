import CapLean.CapCore
import CapLean.Trace
import CapLean.Capability
import CapLean.Sandbox
import CapLean.TrustLattice

namespace CapLean

/-!
## Structural Monotonicity Theorems

Four general theorems showing safety properties are preserved under
structural orderings on capabilities, sandboxes, and trust floors.

1. **Capability Monotonicity** — widening a capability preserves trace safety
2. **Trace Composition** — concatenating safe traces yields a safe trace
3. **Sandbox Monotonicity** — widening a sandbox preserves containment
4. **Trust Floor Lowering** — lowering the trust floor preserves install safety
-/

-- ---------------------------------------------------------------
-- 3a. Capability Monotonicity
-- ---------------------------------------------------------------

/-- Every path reachable under `ps1` is also reachable under `ps2`. -/
def prefixCovers (ps1 ps2 : List String) : Prop :=
  ∀ p : String, (ps1.any (fun s => p.startsWith s) = true) → (ps2.any (fun s => p.startsWith s) = true)

/-- Structural ordering on capabilities: `c1` is a sub-capability of `c2`. -/
structure CapSubset (c1 c2 : Capability) : Prop where
  hRead : c1.allowRead = true → c2.allowRead = true
  hWrite : c1.allowWrite = true → c2.allowWrite = true
  hExec : c1.allowExec = true → c2.allowExec = true
  hEval : c1.allowEval = true → c2.allowEval = true
  hNetwork : c1.allowNetwork = true → c2.allowNetwork = true
  hInstall : c1.allowInstall = true → c2.allowInstall = true
  hReadPfx : prefixCovers c1.readPrefixes c2.readPrefixes
  hWritePfx : prefixCovers c1.writePrefixes c2.writePrefixes

/-- If an op is within scope of a smaller capability, it is within scope of a larger one. -/
theorem withinScope_of_capSubset (op : AgentOp) (c1 c2 : Capability)
    (hsub : CapSubset c1 c2)
    (h : withinScope op c1) : withinScope op c2 := by
  simp only [withinScope, withinScopeBool] at *
  cases op with
  | readFile path =>
    have ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    exact Bool.and_eq_true_iff.mpr ⟨hsub.hRead ha, hsub.hReadPfx path hb⟩
  | writeFile path _ =>
    have ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    exact Bool.and_eq_true_iff.mpr ⟨hsub.hWrite ha, hsub.hWritePfx path hb⟩
  | execShell _ _ => exact hsub.hExec h
  | evalCode _ => exact hsub.hEval h
  | networkCall _ => exact hsub.hNetwork h
  | installPkg _ => exact hsub.hInstall h
  | explicitApprove _ => exact hsub.hInstall h

/-- Widening a capability preserves trace safety. -/
theorem capabilityMonotonicity (c1 c2 : Capability) (t : Trace)
    (hsub : CapSubset c1 c2)
    (h : traceWithinScope t c1)
    : traceWithinScope t c2 := by
  simp only [traceWithinScope, traceWithinScopeBool] at *
  rw [List.all_eq_true] at *
  intro op hmem
  exact withinScope_of_capSubset op c1 c2 hsub (h op hmem)

-- ---------------------------------------------------------------
-- 3b. Trace Composition Safety
-- ---------------------------------------------------------------

/-- Concatenating two capability-safe traces yields a capability-safe trace. -/
theorem traceAppendSafe (t1 t2 : Trace) (cap : Capability)
    (h1 : traceWithinScope t1 cap)
    (h2 : traceWithinScope t2 cap)
    : traceWithinScope (t1 ++ t2) cap := by
  simp only [traceWithinScope, traceWithinScopeBool] at *
  rw [List.all_eq_true] at *
  intro op hmem
  rcases List.mem_append.mp hmem with h | h
  · exact h1 op h
  · exact h2 op h

/-- Concatenating two sandbox-contained effect traces yields a contained trace. -/
theorem effectTraceAppendSafe (t1 t2 : EffectTrace) (sb : Sandbox)
    (h1 : effectTraceContained t1 sb)
    (h2 : effectTraceContained t2 sb)
    : effectTraceContained (t1 ++ t2) sb := by
  simp only [effectTraceContained, effectTraceWithinSandbox] at *
  rw [List.all_eq_true] at *
  intro eff hmem
  rcases List.mem_append.mp hmem with h | h
  · exact h1 eff h
  · exact h2 eff h

-- ---------------------------------------------------------------
-- 3c. Sandbox Monotonicity
-- ---------------------------------------------------------------

/-- Structural ordering on sandboxes: `sb1` is contained within `sb2`. -/
structure SandboxSubset (sb1 sb2 : Sandbox) : Prop where
  hPaths : ∀ p : String, (sb1.allowedPaths.any (fun pre => p.startsWith pre) = true) → (sb2.allowedPaths.any (fun pre => p.startsWith pre) = true)
  hSyscalls : ∀ s : String, (sb1.allowedSyscalls.contains s = true) → (sb2.allowedSyscalls.contains s = true)

/-- If an effect is within a smaller sandbox, it is within a larger one. -/
theorem effectWithinSandbox_of_subset (eff : Effect) (sb1 sb2 : Sandbox)
    (hsub : SandboxSubset sb1 sb2)
    (h : effectWithinSandbox eff sb1 = true)
    : effectWithinSandbox eff sb2 = true := by
  cases eff with
  | fsRead path =>
    simp only [effectWithinSandbox] at *
    exact hsub.hPaths (normalizePath path) h
  | fsWrite path =>
    simp only [effectWithinSandbox] at *
    exact hsub.hPaths (normalizePath path) h
  | netConn host =>
    simp only [effectWithinSandbox] at *
    exact hsub.hSyscalls "NetConn" h
  | spawn cmd =>
    simp only [effectWithinSandbox] at *
    exact hsub.hSyscalls "Spawn" h

/-- Widening a sandbox preserves effect trace containment. -/
theorem sandboxMonotonicity (sb1 sb2 : Sandbox) (t : EffectTrace)
    (hsub : SandboxSubset sb1 sb2)
    (h : effectTraceContained t sb1)
    : effectTraceContained t sb2 := by
  simp only [effectTraceContained, effectTraceWithinSandbox] at *
  rw [List.all_eq_true] at *
  intro eff hmem
  exact effectWithinSandbox_of_subset eff sb1 sb2 hsub (h eff hmem)

-- ---------------------------------------------------------------
-- 3d. Trust Floor Lowering
-- ---------------------------------------------------------------

/-- Lowering the trust floor preserves pkgAllowedBool. -/
theorem pkgAllowed_weaken (pkg : Package) (g : DepGraph) (cap1 cap2 : Capability)
    (hFloor : cap2.minTrust ≤ cap1.minTrust)
    (h : pkgAllowedBool pkg g cap1 = true)
    : pkgAllowedBool pkg g cap2 = true := by
  simp only [pkgAllowedBool, Nat.ble_eq] at *
  exact Nat.le_trans hFloor h

/-- Lowering the trust floor preserves install safety for the entire trace. -/
theorem trustFloorLowering (t : Trace) (g : DepGraph) (cap1 cap2 : Capability)
    (hFloor : cap2.minTrust ≤ cap1.minTrust)
    (h : traceInstallsSafeProp t g cap1)
    : traceInstallsSafeProp t g cap2 := by
  simp only [traceInstallsSafeProp, traceInstallsSafe] at *
  rw [List.all_eq_true] at *
  intro op hmem
  have h1 := h op hmem
  match op with
  | .installPkg name =>
    simp only at h1 ⊢
    cases h_appr : t.any (· == .explicitApprove name) with
    | true => simp
    | false =>
      simp [h_appr] at h1 ⊢
      cases h_lookup : DepGraph.lookup g name with
      | none => simp [h_lookup] at h1
      | some pkg => simp [h_lookup] at h1 ⊢; exact pkgAllowed_weaken pkg g cap1 cap2 hFloor h1
  | .readFile _ => exact h1
  | .writeFile _ _ => exact h1
  | .execShell _ _ => exact h1
  | .evalCode _ => exact h1
  | .networkCall _ => exact h1
  | .explicitApprove _ => exact h1

-- ---------------------------------------------------------------
-- Concrete examples (native_decide sanity checks)
-- ---------------------------------------------------------------

-- 3a: capability monotonicity
private def narrowCap : Capability where
  allowRead := true; allowWrite := false; allowExec := false
  allowEval := false; allowNetwork := false; allowInstall := false
  readPrefixes := ["/workspace/src"]; writePrefixes := []
  minTrust := .verified

private def wideCap : Capability where
  allowRead := true; allowWrite := true; allowExec := false
  allowEval := false; allowNetwork := false; allowInstall := false
  readPrefixes := ["/workspace"]; writePrefixes := ["/workspace"]
  minTrust := .verified

example : traceWithinScope [.readFile "/workspace/src/main.py"] narrowCap := by native_decide
example : traceWithinScope [.readFile "/workspace/src/main.py"] wideCap := by native_decide

-- 3b: trace composition
private def t1 : Trace := [.readFile "/workspace/src/a.py"]
private def t2 : Trace := [.readFile "/workspace/src/b.py"]

example : traceWithinScope t1 narrowCap := by native_decide
example : traceWithinScope t2 narrowCap := by native_decide
example : traceWithinScope (t1 ++ t2) narrowCap := by native_decide

-- 3c: sandbox monotonicity
private def tightSandbox : Sandbox where
  allowedPaths := ["/workspace/src"]; allowedSyscalls := []

private def wideSandbox : Sandbox where
  allowedPaths := ["/workspace"]; allowedSyscalls := ["Spawn"]

example : effectTraceContained [.fsRead "/workspace/src/f.py"] tightSandbox := by native_decide
example : effectTraceContained [.fsRead "/workspace/src/f.py"] wideSandbox := by native_decide

-- 3d: trust floor lowering
private def verifiedCap : Capability where
  allowRead := true; allowWrite := true; allowExec := false
  allowEval := false; allowNetwork := false; allowInstall := true
  readPrefixes := ["/workspace"]; writePrefixes := ["/workspace"]
  minTrust := .verified

private def unreviewedCap : Capability where
  allowRead := true; allowWrite := true; allowExec := false
  allowEval := false; allowNetwork := false; allowInstall := true
  readPrefixes := ["/workspace"]; writePrefixes := ["/workspace"]
  minTrust := .unreviewed

private def cleanGraph : DepGraph :=
  [({ name := "requests", trust := .verified }, [])]

example : traceInstallsSafeProp [.installPkg "requests"] cleanGraph verifiedCap := by native_decide
example : traceInstallsSafeProp [.installPkg "requests"] cleanGraph unreviewedCap := by native_decide

end CapLean

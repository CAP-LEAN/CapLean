import CapLean.AgentOp
import CapLean.AgentM
import CapLean.Trace
import CapLean.Capability
import CapLean.SafetySpine
import CapLean.Sandbox

namespace CapLean

/-!
## Sandbox Examples — demos, attack scenarios, and runtime/formal checks

Concrete demonstrations of Layer 2 (sandbox containment)

-/

-- ────────────────────────────────────────────
-- 1. Demo sandbox + attack scenarios
-- ────────────────────────────────────────────

/-- Permissive capability for sandbox demos (all op categories allowed) -/
def sandboxDemoCap : Capability where
  allowRead     := true
  allowWrite    := true
  allowExec     := true
  allowEval     := true
  allowNetwork  := true
  allowInstall  := true
  readPrefixes  := ["/"]
  writePrefixes := ["/"]
  minTrust      := .knownVulnerable

/-- The demo sandbox: only /workspace paths, no network, no spawn -/
def workspaceSandbox : Sandbox where
  allowedPaths    := ["/workspace"]
  allowedSyscalls := []

/-- Agent that only runs EvalCode -/
def evalAgent : AgentM sandboxDemoCap Unit :=
  op! (.evalCode "run_tests()")

/-- Agent that tries ExecShell -/
def shellAgent : AgentM sandboxDemoCap Unit :=
  op! (.execShell "bash" ["-i"])

/-- Agent that reads a sensitive file (transparent op) -/
def readPasswdAgent : AgentM sandboxDemoCap Unit :=
  op! (.readFile "/etc/passwd")

-- OpaqueBound-based annotations

/-- SAFE: eval reads and writes only workspace files -/
def safeEvalBound : OpaqueBound where
  evalEffects _ := [.fsRead "/workspace/test.py",
                    .fsWrite "/workspace/result.txt"]
  execEffects _ _ := []

/-- ATTACK 1: eval tries to read /etc/passwd -/
def etcPasswdBound : OpaqueBound where
  evalEffects _ := [.fsRead "/etc/passwd"]
  execEffects _ _ := []

/-- ATTACK 2: eval tries to open a network connection -/
def netExfilBound : OpaqueBound where
  evalEffects _ := [.netConn "attacker.com"]
  execEffects _ _ := []

/-- ATTACK 3: exec declares additional spawn of /bin/bash -/
def shellEscapeBound : OpaqueBound where
  evalEffects _ := []
  execEffects _ _ := [.spawn "/bin/bash"]

-- Legacy EffectAnnotation aliases (via fullAnnotation)
def safeEvalAnn : EffectAnnotation := fullAnnotation safeEvalBound
def etcPasswdAnn : EffectAnnotation := fullAnnotation etcPasswdBound
def netExfilAnn : EffectAnnotation := fullAnnotation netExfilBound
def shellEscapeAnn : EffectAnnotation := fullAnnotation shellEscapeBound

-- ────────────────────────────────────────────
-- 2. Runtime checks (#eval)
-- ────────────────────────────────────────────

-- 2a. Path normalization demo
#eval normalizePath "/workspace/../../etc/passwd"     -- "/etc/passwd"
#eval normalizePath "/workspace/./src/../src/main.py" -- "/workspace/src/main.py"
#eval normalizePath "/workspace/src/main.py"          -- "/workspace/src/main.py"

-- 2b. Original containment checks
-- Safe eval: contained → true
#eval effectTraceWithinSandbox
  (traceAnnotatedEffects evalAgent.collectTrace safeEvalAnn) workspaceSandbox

-- /etc/passwd attack → false
#eval effectTraceWithinSandbox
  (traceAnnotatedEffects evalAgent.collectTrace etcPasswdAnn) workspaceSandbox

-- Network exfil attack → false
#eval effectTraceWithinSandbox
  (traceAnnotatedEffects evalAgent.collectTrace netExfilAnn) workspaceSandbox

-- Shell escape attack → false
#eval effectTraceWithinSandbox
  (traceAnnotatedEffects shellAgent.collectTrace shellEscapeAnn) workspaceSandbox

-- Transparent-op demo: readFile "/etc/passwd" is rejected by canonical effects
-- alone — no annotation can suppress this
#eval effectTraceWithinSandbox
  (traceAnnotatedEffects readPasswdAgent.collectTrace canonicalEffects) workspaceSandbox

-- 2c. Conservative bound: maximalBound derives annotation from sandbox
#eval effectTraceWithinSandbox
  (traceAnnotatedEffects evalAgent.collectTrace
    (fullAnnotation (maximalBound workspaceSandbox))) workspaceSandbox

-- 2d. Path-traversal attack: previously passed raw startsWith, now blocked
/-- ATTACK 4: eval declares traversal path that looks like /workspace prefix -/
def traversalBound : OpaqueBound where
  evalEffects _ := [.fsRead "/workspace/../../etc/passwd"]
  execEffects _ _ := []

#eval effectTraceWithinSandbox
  (traceAnnotatedEffects evalAgent.collectTrace
    (fullAnnotation traversalBound)) workspaceSandbox

-- ────────────────────────────────────────────
-- 3. Formal proofs
-- ────────────────────────────────────────────

-- 3a. fullAnnotation-based proofs (opaque ops require OpaqueBound)

-- Safe agent: contained
example : effectTraceContained
    (traceAnnotatedEffects evalAgent.collectTrace safeEvalAnn)
    workspaceSandbox := by native_decide

-- Attack 1: /etc/passwd read is blocked
example : ¬ effectTraceContained
    (traceAnnotatedEffects evalAgent.collectTrace etcPasswdAnn)
    workspaceSandbox := by native_decide

-- Attack 2: network exfil is blocked
example : ¬ effectTraceContained
    (traceAnnotatedEffects evalAgent.collectTrace netExfilAnn)
    workspaceSandbox := by native_decide

-- Attack 3: shell escape is blocked
example : ¬ effectTraceContained
    (traceAnnotatedEffects shellAgent.collectTrace shellEscapeAnn)
    workspaceSandbox := by native_decide

-- Spine theorem fires: safe eval satisfies containment per-op
example : ∀ op ∈ evalAgent.collectTrace,
    ∀ eff ∈ safeEvalAnn op, effectWithinSandbox eff workspaceSandbox = true :=
  sandboxContainment _ _ _ (by native_decide)

-- 3b. canonicalContainment-based proofs (transparent ops, NO trust assumption)

-- Transparent-op rejection: readFile "/etc/passwd" is caught by canonicalEffects
-- alone — no OpaqueBound involved, no trust assumption needed
example : ¬ effectTraceContained
    (traceAnnotatedEffects readPasswdAgent.collectTrace canonicalEffects)
    workspaceSandbox := by native_decide

-- Even a "lying" empty OpaqueBound cannot suppress transparent-op effects:
-- fullAnnotation always includes canonicalEffects
def emptyBound : OpaqueBound where
  evalEffects _ := []
  execEffects _ _ := []

example : ¬ effectTraceContained
    (traceAnnotatedEffects readPasswdAgent.collectTrace (fullAnnotation emptyBound))
    workspaceSandbox := by native_decide

-- A safe transparent-op agent (reads /workspace/main.py) passes canonicalContainment
def safeReadAgent : AgentM sandboxDemoCap Unit :=
  op! (.readFile "/workspace/main.py")

example : effectTraceContained
    (traceAnnotatedEffects safeReadAgent.collectTrace canonicalEffects)
    workspaceSandbox := by native_decide

example : ∀ op ∈ safeReadAgent.collectTrace,
    ∀ eff ∈ canonicalEffects op, effectWithinSandbox eff workspaceSandbox = true :=
  canonicalContainment _ _ (by native_decide)

-- 3c. Conservative bound: maximalBound is contained (no custom annotation)
example : effectTraceContained
    (traceAnnotatedEffects evalAgent.collectTrace
      (fullAnnotation (maximalBound workspaceSandbox)))
    workspaceSandbox := by native_decide

example : ∀ op ∈ evalAgent.collectTrace,
    ∀ eff ∈ (fullAnnotation (maximalBound workspaceSandbox)) op,
      effectWithinSandbox eff workspaceSandbox = true :=
  conservativeContainment _ _ (by native_decide)

-- 3d. Path-traversal attack: normalization defeats ../
example : ¬ effectTraceContained
    (traceAnnotatedEffects evalAgent.collectTrace (fullAnnotation traversalBound))
    workspaceSandbox := by native_decide

-- 3e. fullEnvelope: Layer 1 + Layer 2 in one shot
example : (∀ op ∈ evalAgent.collectTrace, withinScope op sandboxDemoCap)
    ∧ (∀ op ∈ evalAgent.collectTrace,
        ∀ eff ∈ safeEvalAnn op, effectWithinSandbox eff workspaceSandbox = true) :=
  fullEnvelope evalAgent workspaceSandbox safeEvalAnn (by native_decide)

end CapLean

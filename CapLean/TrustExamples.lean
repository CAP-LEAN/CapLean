import CapLean.AgentOp
import CapLean.CapCore
import CapLean.Trace
import CapLean.Capability
import CapLean.TrustLattice

namespace CapLean

/-!
## Trust Lattice Examples — demo packages, graphs, and runtime/formal checks

Concrete demonstrations of Layer 3 (supply chain trust)

-/

-- ── 1. Demo packages and graphs ──────────────────────────────────────

def pkgVerified   : Package := { name := "requests",   trust := .verified }
def pkgUnreviewed : Package := { name := "cool-utils",  trust := .unreviewed }
def pkgVuln       : Package := { name := "log4shell",   trust := .knownVulnerable }

def cleanGraph : DepGraph := [(pkgVerified, [])]

def poisonedGraph : DepGraph :=
  [(pkgUnreviewed, [pkgVuln]),
   (pkgVuln,       [])]

def deepGraph : DepGraph :=
  [({ name := "safe-lib", trust := .verified }, [pkgUnreviewed]),
   (pkgUnreviewed, [pkgVuln]),
   (pkgVuln, [])]

def strictCap : Capability where
  allowRead     := true
  allowWrite    := true
  allowExec     := false
  allowEval     := true
  allowNetwork  := false
  allowInstall  := true
  readPrefixes  := ["/workspace"]
  writePrefixes := ["/workspace"]
  minTrust      := .verified

-- ── 2. Concrete runtime checks ───────────────────────────────────────

#eval traceInstallsSafe [.installPkg "requests"] cleanGraph strictCap
-- expected: true

#eval traceInstallsSafe [.installPkg "cool-utils"] poisonedGraph strictCap
-- expected: false

#eval traceInstallsSafe [.installPkg "safe-lib"] deepGraph strictCap
-- expected: false

#eval traceInstallsSafe
  [.explicitApprove "cool-utils", .installPkg "cool-utils"] poisonedGraph strictCap
-- expected: true (explicit override)

-- ── 3. Formal proofs ─────────────────────────────────────────────────

example : traceInstallsSafeProp
    [.installPkg "requests"] cleanGraph strictCap := by native_decide

example : ¬ traceInstallsSafeProp
    [.installPkg "cool-utils"] poisonedGraph strictCap := by native_decide

example : ¬ traceInstallsSafeProp
    [.installPkg "safe-lib"] deepGraph strictCap := by native_decide

-- ExplicitApprove in the same trace overrides the floor
example : traceInstallsSafeProp
    [.explicitApprove "cool-utils", .installPkg "cool-utils"] poisonedGraph strictCap := by
  native_decide

-- Spine theorem instantiation on a concrete trace
example : ∀ op ∈ ([.installPkg "requests"] : Trace), ∀ name : String,
    op = .installPkg name →
    ([.installPkg "requests"] : Trace).any (· == .explicitApprove name) = true ∨
    ∃ pkg, cleanGraph.lookup name = some pkg ∧ pkgAllowed pkg cleanGraph strictCap :=
  trustMonotonicity [.installPkg "requests"] cleanGraph strictCap (by native_decide)

end CapLean

-- CapLean/AgentOp.lean
namespace CapLean

/-- A normalised file path (wrapper for safety later) -/
abbrev FilePath := String

/-- A shell command -/
abbrev Cmd := String

/-- A package name -/
abbrev PkgName := String

/-- A URL -/
abbrev URL := String

/-- A code snippet string -/
abbrev CodeSnippet := String

/--
The vocabulary of operations an agentic coding tool can perform.
This is the "alphabet" of the free monad -- every effectful action
the agent can take is one of these constructors.
-/
inductive AgentOp : Type where
  | readFile       : FilePath → AgentOp
  | writeFile      : FilePath → String → AgentOp
  | execShell      : Cmd → List String → AgentOp
  | evalCode       : CodeSnippet → AgentOp
  | installPkg     : PkgName → AgentOp
  | networkCall    : URL → AgentOp
  | explicitApprove : PkgName → AgentOp
  deriving Repr, DecidableEq, BEq

end CapLean

namespace CapLean

/-!
## AgentOp — Operation Vocabulary

**Purpose:** Defines the alphabet of effectful actions an agent can perform.

**Key definitions:**
- `FilePath`, `Cmd`, `PkgName`, `URL`, `CodeSnippet` — string aliases for op arguments
- `AgentOp` — inductive type listing every op (readFile, writeFile, execShell,
  evalCode, installPkg, networkCall, explicitApprove)

**Key theorems:** none — pure data declarations.

**Assumptions:** `FilePath` is currently `String`; path normalization happens
later in `Sandbox.normalizePath`.
-/

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

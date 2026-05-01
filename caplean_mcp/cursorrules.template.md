# CapLean enforcement (do not remove)

This workspace runs the `caplean` MCP server. Every potentially-side-effecting
action you take must be cleared by CapLean Layer 1 before you call the
corresponding native Cursor tool.

## Required preconditions

| Before you do this... | ...call this CapLean tool first |
|---|---|
| read a file (`read_file`) | `caplean.check_read(path)` |
| write or edit a file (`edit_file`, `apply_diff`) | `caplean.check_write(path)` |
| run a terminal command (`run_terminal_cmd`) | `caplean.check_exec(cmd, args)` |
| execute / eval arbitrary code | `caplean.check_eval(snippet)` |
| fetch a URL | `caplean.check_network(url)` |
| install a package | `caplean.check_install(pkg)` |
| explicitly approve a package | `caplean.approve(pkg)` |

## Decision rule

Each `caplean.check_*` returns `{verdict, reason}`. If `verdict == "BLOCKED"`:

1. Do not call the native Cursor tool for that action.
2. Report the `reason` to the user verbatim.
3. Stop and ask the user before proceeding with anything else affecting the
   same resource.

If `verdict == "ALLOWED"`, proceed with the native tool call as usual.

## Session start and end

- Start of session: call `caplean.set_policy(capability=…)` once. The
  capability JSON schema is documented in `CapLean/capshim.py:43-54`.
- End of session: call `caplean.verify_session()` and surface the
  Layer 1 / Layer 2 / Layer 3 verdicts to the user. A failure here means
  some op slipped past the live check (or a sandbox/trust violation
  appeared post-hoc); treat it as a hard stop.

## Why

Layer 1 runs live and cannot prevent the agent from skipping the check —
that is why disobedience is detected post-hoc. The Lean checker
(`caplean-check`) re-runs `enforceTrace` over the JSONL trace and refuses
to certify a session that contains an out-of-scope `verdict:ALLOWED` op.

# caplean-mcp — CapLean as a Cursor MCP server

Enforces CapLean **Layer 1 (capability scope)** live on every Cursor agent
action and certifies the resulting trace post-hoc with the existing
`caplean-check` Lean binary.

## What it does

- Exposes 10 MCP tools (`caplean.set_policy`, `caplean.check_read`,
  `caplean.check_write`, `caplean.check_exec`, `caplean.check_eval`,
  `caplean.check_network`, `caplean.check_install`, `caplean.approve`,
  `caplean.get_trace`, `caplean.verify_session`).
- Each `check_*` writes a JSONL line to `/tmp/caplean_trace.jsonl` in the
  schema documented at `CapLean/capshim.py:7-14`.
- `verify_session` invokes the existing `caplean-check` Lean binary
  (`Check/Main.lean`) and returns the Layer 1 / 2 / 3 verdicts.

## Honest scope

- **Live blocking covers Layer 1 only.** Sandbox path normalization (Layer 2)
  and transitive trust (Layer 3) are checked at audit time inside `caplean-check`.
- **Soft enforcement.** MCP cannot interpose on Cursor's built-in
  `read_file` / `edit_file` / `run_terminal_cmd` calls. The agent has to
  honour `.cursorrules` voluntarily. Disobedience is detected at audit time:
  any out-of-scope `verdict:ALLOWED` op causes `caplean-check` to fail with
  exit code 1.
- **No Cursor fork.** Hard interposition would require modifying Cursor itself.

## Install

```bash
cd /path/to/CapLean_Repo
lake build                                  # builds .lake/build/bin/caplean-check
pip install -e ./caplean_mcp                # installs caplean-mcp + the `mcp` SDK
python -m caplean_mcp.server --self-test    # exercise policy logic, no MCP transport
```

## Wire up Cursor

Add to `~/.cursor/mcp.json`:

```json
{
  "mcpServers": {
    "caplean": {
      "command": "python",
      "args": ["-m", "caplean_mcp.server"],
      "env": { "CAPLEAN_REPO": "/path/to/CapLean_Repo" }
    }
  }
}
```

`CAPLEAN_REPO` tells `verify_session` where to find
`.lake/build/bin/caplean-check`. If you installed the package from a checkout
sibling to the Lean repo, you can omit `env`.

Drop `cursorrules.template.md` into the target workspace as `.cursorrules`
(or merge its contents into the file you already have). Restart Cursor.

## End-to-end test example

In a Cursor chat, with the rules in place and `set_policy` called:

```
caplean.set_policy(capability={
  "allowRead": true, "allowWrite": true, "allowExec": false,
  "allowEval": true, "allowNetwork": false, "allowInstall": false,
  "readPrefixes": ["/workspace"], "writePrefixes": ["/workspace"],
  "minTrust": "verified"
})
```

**NOTE** - "/workspace" is a placeholder, change it to your appropriate path of choice for proper testing

| Ask the agent... | Expected behaviour |
|---|---|
| Read `/workspace/foo.txt` | `check_read` ALLOWED → native `read_file` runs |
| Read `/etc/passwd`        | `check_read` BLOCKED → agent declines, reports reason |
| Run `ls /tmp`             | `check_exec` BLOCKED (`allowExec=false`) |

Then call in **Cursor chat** `caplean.verify_session` — output mirrors `Check/Main.lean:78-97`:

```
[Layer 1] PASS: all N ops within capability scope
[Layer 2] PASS: all canonical effects within sandbox
[Layer 3] PASS: all installs meet trust floor or are explicitly approved
```

## Files

| File | Role |
|---|---|
| `policy.py` | Layer 1 decision logic (mirrors `CapCore.lean#withinScopeBool`) |
| `server.py` | FastMCP server, tool registrations, `verify_session` shell-out |
| `cursorrules.template.md` | Drop-in `.cursorrules` for Cursor workspaces |
| `pyproject.toml` | `mcp>=1.0` dep, console entry point `caplean-mcp` |

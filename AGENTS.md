# NCML Project Instructions

## Lean development

Proof work in this repository uses the `lean4` skill from
[`cameronfreer/lean4-skills`](https://github.com/cameronfreer/lean4-skills) and
the `lean-lsp` MCP server. Both `uv` and `ripgrep` are required.

### Claude Code

Install the native Claude Code plugin after cloning:

```
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4@lean4-skills
```

The Claude Code MCP configuration is in `.mcp.json`. The skill provides
commands such as `/lean4:autoprove`.

### Codex

Install the core skill in a Codex chat:

```
$skill-installer install https://github.com/cameronfreer/lean4-skills/tree/main/plugins/lean4/skills/lean4
```

Invoke it as `$lean4`, or let Codex activate it automatically for Lean 4
tasks. Restart Codex if the installed skill is not yet available. Codex reads
the `lean-lsp` configuration from `.codex/config.toml`.

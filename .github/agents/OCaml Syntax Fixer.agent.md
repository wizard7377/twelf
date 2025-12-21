---
description: 'Fix the issues in the OCaml Syntax'
tools: ['vscode', 'execute', 'read', 'edit', 'search', 'web', 'azure-mcp/search', 'agent', 'ms-vscode.vscode-websearchforcopilot/websearch', 'todo']
---
## Goal
Run `dune build` to collect syntax errors, then fix only those syntax issues (capitalization, parentheticals, other syntax typos) while ignoring any `end` expected/unexpected errors. Do not change semantics or style beyond what is strictly required to correct syntax.

## Operating Procedure
1) Run `dune build` from workspace root to gather current errors; capture output for reference.
2) Identify syntax-only errors (e.g., capitalization, missing/extra parentheses, stray punctuation). Explicitly ignore `end` expected/unexpected errors—do not attempt to modify code to address them.
3) For each syntax-only error, open the file and fix the syntax minimally. Keep changes confined to syntax; do not refactor, reorder code, or alter logic/formatting beyond what is necessary.
4) If a name is changed when it is declared/defined, ensure that all references to that name specifically are updated consistently throughout the codebase.
5) After fixes, rerun `dune build` to confirm syntax passes. If new syntax errors appear, repeat within the same constraints. Stop once syntax errors (other than ignored `end` errors) are resolved.
6) Summarize files touched and syntax fixes applied. Mention any ignored `end` errors that remain.

## Guardrails
- Scope: syntax-only fixes; no behavioral or formatting changes unrelated to syntax.
- Respect capitalization and parenthetical correctness; ensure final code parses.
- Do not attempt to fix `end` expected/unexpected errors.
- Keep edits minimal and localized; avoid wholesale rewrites.

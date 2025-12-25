# Copilot Formatting Instructions (Lean4)

These apply to Lean4 files. Keep them simple and consistent.

## General
- Prefer Lean 4 standard formatting; keep code readable and minimal.
- Avoid trailing whitespace; use LF line endings.
- Use two spaces for indentation; never tabs.
- Keep lines ≤ 100 columns when possible.
- Don't orphan parentheses; keep them with their arguments.

## Imports & Open
- Group imports at the top; one per line.
- Avoid wildcard `open` unless needed; open specific namespaces near usage.

## Definitions & Structure
- One definition/theorem per block; leave a blank line between blocks.
- Place type signatures on their own line; keep short definitions on one line when readable.
- Align nested `do` blocks with consistent two-space indent.
- Use `{`/`}` for records with each field on its own line when multi-line.

## Notation & Proofs
- Favor explicit arguments over implicit wildcards when clarity matters.
- In proofs, indent tactics by two spaces inside `by`/`match`/`do`.
- Keep pattern matches tidy: `match ... with` on one line, cases indented beneath.

## Comments & Docs
- Use `/- -/` or `--` for comments; no trailing `--` comments on long lines.
- Prefer docstrings (`/-- ... -/`) directly above the item they describe.

## Whitespace
- Insert a blank line between logical sections.
- No extra blank lines at file start or end.
- No spaces before commas or colons; one space after commas and colons in terms.

## Names
- Use `camelCase` for identifiers; `PascalCase` for structures/types; uppercase for constants meant as parameters.
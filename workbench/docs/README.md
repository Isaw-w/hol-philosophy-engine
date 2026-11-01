# Technical notes

- [NATIVE.md](NATIVE.md): native execution, raw-output preservation, assumptions,
  oracle tags, and execution-status meanings.
- [VERBALIZATION.md](VERBALIZATION.md): typed-term export and deterministic
  controlled-English rendering.

Some commands in these original setup notes use the root-level compatibility
paths `logikey/`, `loops/`, and `checks/`. Run those commands from the repository
root. The current [workbench guide](../README.md) gives commands relative to
`hol/` instead.

The custom parser, old Isabelle layers, and earlier runners remain under
[legacy/logikey](../../legacy/logikey/). They are not used by the current native
checking path.

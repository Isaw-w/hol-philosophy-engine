# Native HOL checking

The default runner now executes the selected prover's native language. It does
not use fmt.py, inject deontic operators, translate formulas, change imports,
replace proofs, or send revision feedback to a model. Existing prompts and
responses remain unchanged. The previous loop is preserved as
`loop_legacy_interface_20261016.py`; older analysis scripts remain legacy tools.

Installed on `mini`:

- Isabelle2025-2: latest stable release; retained at the user's request.
- HOL4 Trindemossen-2: release commit
  `bdc6917eeafd45f1067c08b6061c2243c1b1edb0`, built with Poly/ML 5.9.2.

The selected prover is an execution parameter, not an additional model prompt.
HOL4 and Isabelle have different native syntaxes. No conversion between them
is performed. HOL4 sources execute in its standard interactive environment.
Isabelle sources must contain their own native theory header and imports.

Recheck an existing response, with no model call:

```sh
python3 logikey/native_check.py loops/g02_freehol_20261016_111433/r1_response.json \
  --prover hol4 --out checks/NEW_CHECK
```

For an existing Isabelle theory:

```sh
python3 logikey/native_check.py /absolute/path/MyTheory.thy \
  --prover isabelle --out checks/my_theory_v1
```

For an Isabelle response stored in JSON, supply `--theory-name` matching its
existing header. Multiple Markdown blocks require explicit `--block N`
selection. A single fenced block is extracted unchanged; the entire original
response, the extraction, hashes, environment, driver, logs, and execution
result are retained. No unclosed fence or source error is repaired.

To generate a fresh response after approving the exact prompt and route, use
the previous one-case command. It now defaults to native HOL4 checking and
zero revisions. `--generate-only` omits checking; `--prover isabelle` selects
Isabelle instead. Output directories must be new and cannot overwrite a run.

`processed` means native execution completed. It does not establish that the
source faithfully represents the case, that all its claims were formalized,
or that its assumptions are true or consistent. HOL4's native theorem database
is reported with added axioms, theorem assumptions, axiom dependencies, and
oracle tags. `DISK_THM` is the standard persisted-library theorem tag; other
oracle tags are also listed separately and must be inspected before counting
a proof as an ordinary kernel deduction. Only stored theorems from the current final theory appear
in that report; unregistered theorem values and earlier theories are outside
the report's scope. Isabelle's full native diagnostic log is retained; this
runner does not independently certify absence of admitted proofs in Isabelle.

Empty responses and provider `content_filter` results are recorded as
`no_response` or `generation_filtered` without invoking a prover. Empty code
blocks are `no_formal_source`. None count as a checked proof. The caller saves
the complete provider JSON beside the normalized response and reports missing
cost data as unavailable. These conditions do not trigger automatic retries.

References:

- https://hol-theorem-prover.org/install
- https://github.com/HOL-Theorem-Prover/HOL/releases/tag/trindemossen-2
- https://hol-theorem-prover.org/docs/trindemossen-2/Description/misc
- https://isabelle.in.tum.de/documentation.html

## Optional deontic library (2026-10-18)

`tools/hol4_libraries/deontic/deonticScript.sml` is Carmo and Jones's dyadic deontic logic in the embedding of Benzmüller, Farjami
and Parent (LogiKEy's CJ_DDL), transcribed axiom by axiom into HOL4, with knowledge, betterness and probability as in
the earlier checker. It is built on `mini` in `~/thick_training/hol4_lib`. The HOL4 driver only puts that directory on
`loadPath`; a response loads the library itself (`load "deonticTheory"`) or not at all. Nothing is opened, imported or
added for it. `native_result.json` records the library script's SHA-256. Tests: `tools/hol4_libraries/deontic/test_deontic.sml`
(general principles detach; conflicting conditionals give a dilemma; settled facts are not obligations; the
"obligations split" law makes every actual obligation false; knowledge is factive; Better is irreflexive). A response
using the library: `checks/20261018/deontic_library_smoke_20261018/` (processed).

## Optional reasons-as-defaults library (2026-10-18)

`tools/hol4_libraries/horty/hortyScript.sml`: Horty's fixed-priority default theories (Reasons as Defaults, 2012). Formulas are data
(`Atom "name"`, `Neg`, `Conj`, `Disj`, `Impl`, `Tru`) so that entailment and non-entailment are both decided by HOL4
evaluation (truth tables over the formula's atoms); every verdict is a kernel theorem from `EVAL`. A theory is facts
`W`, defaults `D` = (name, premise, conclusion), priority `P` = (weaker, stronger). Triggered, conflicted, defeated
(a stronger triggered default whose conclusion, with W, entails the negation), binding, proper (stable and grounded).
`OughtH W D P f`: f follows in some proper scenario (Horty's conflict account); `RequiredH`: in every one, and one
exists. Built in `~/thick_training/hol4_lib` (on the driver's loadPath). Tests `tools/hol4_libraries/horty/test_horty.sml`: Tweety
(stronger default defeats), Nixon (two proper scenarios), groundedness (self-support excluded), g02 by hand (with the
priority: Pause required, Bump not an ought; without it: two scenarios, Bump an ought). All pass in about 2 seconds.

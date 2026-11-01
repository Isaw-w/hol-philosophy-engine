# HOL philosophy engine

Verify any argument written in HOL4.

Give `holverify` a HOL4 theory, with its premises as axioms and its conclusion as a theorem. It tells you whether that
theory is an argument in the sense of Besnard and Hunter (*Elements of Argumentation*, 2008): a set of premises that is
consistent, proves its claim, and is minimal, so that no premise can be dropped. It also reads the argument back in
plain English. Nothing in it calls a language model.

```text
$ holverify examples/valid_modus_ponens.sml examples/idle_premise.sml
examples/valid_modus_ponens.sml:
  ARGUMENT  proved=True consistent=True minimal=True idle_premises=0 idle_axioms=0 hard_flaws=0
examples/idle_premise.sml:
  NOT AN ARGUMENT  proved=True consistent=True minimal=False idle_premises=1 idle_axioms=1 hard_flaws=0
```

## What it checks

| Check | How |
|---|---|
| **Proved** | HOL4 (Trindemossen 2) runs the theory and proves the conclusion |
| **Consistent** | the premises can all be true together; the HOL4 terms are translated into Z3, and an inconsistency Z3 finds is replayed and proved in HOL4 |
| **Minimal** | every premise lies in every smallest set of premises that gives some part of the conclusion, and the list of smallest sets is complete; a premise that does no work is named |
| **No idle axiom** | no axiom is cut off from the conclusion |
| **No hard flaw** | none of the flaws the Z3 engine detects: contents given as text, creative definitions, collapse, explosion, a constant that takes a truth value without a definition |

When Z3 says that some premises do not give a conclusion, it gives a countermodel, and the countermodel is checked in
HOL semantics before the answer counts.

## Install

```bash
git clone https://github.com/Isaw-w/hol-philosophy-engine.git
cd hol-philosophy-engine
pip install -e .            # installs the `holverify` command and z3-solver
```

You also need HOL4 (Trindemossen 2), either on this machine or on a machine you can reach by ssh without a password.

## Use

```bash
holverify ARGUMENT.sml                       # verify one argument
holverify a.sml b.sml c.sml                  # several at once
holverify ARGUMENT.sml --theorem NAME        # the conclusion is theorem NAME (default: final, else the last theorem)
holverify ARGUMENT.sml --json                # verdicts as JSON
python3 -m holverify ARGUMENT.sml            # without installing
```

Each argument gets a folder `holverify_out/<name>/` (change it with `--out`):

- `report.md` gives the verdict, the premises that do no work, any hard flaws, the argument in plain English and the
  full Z3 engine report;
- `verdict.json` holds the same verdict for programs;
- `native_check/` and `z3_engine/` hold HOL4's log and Z3's output.

The command exits with 0 only if every argument given is an argument.

### Settings

| Command line | Environment | Meaning | Default |
|---|---|---|---|
| `--host` | `HOLVERIFY_HOST` | ssh host that runs HOL4, or `local` | `mini` |
| `--hol4` | `HOLVERIFY_HOL4` | path of the `hol` binary on that host | `~/thick_training/tools/HOL4-trindemossen-2/bin/hol` |
| `--remote-dir` | `HOLVERIFY_REMOTE_DIR` | working folder on the host | `thick_training/native_hol_checks` |
| `--z3 local\|host` | | where the Z3 engine runs | `local` if z3-solver is installed |
| `--remote-python` | `HOLVERIFY_REMOTE_PYTHON` | Python with z3-solver on the host, for `--z3 host` | |
| `--timeout` | | seconds for HOL4 | 600 |

For HOL4 installed on this machine:

```bash
holverify ARGUMENT.sml --host local --hol4 /path/to/HOL/bin/hol
```

## Writing an argument

```sml
open HolKernel Parse boolLib bossLib;
val _ = new_theory "valid_modus_ponens";

val _ = new_type ("person", 0);
(* Socrates : Socrates *)
val _ = new_constant ("Socrates", ``:person``);
(* Human x : x is a human being *)
val _ = new_constant ("Human", ``:person -> bool``);
(* Mortal x : x is mortal *)
val _ = new_constant ("Mortal", ``:person -> bool``);

val all_humans_mortal = new_axiom ("all_humans_mortal", ``!x. Human x ==> Mortal x``);
val socrates_human = new_axiom ("socrates_human", ``Human Socrates``);

Theorem final:
  Mortal Socrates
Proof
  metis_tac [all_humans_mortal, socrates_human]
QED

val _ = export_theory ();
```

- **Premises** are axioms, made with `new_axiom`, or the hypotheses of the conclusion.
- **The conclusion** is a theorem, by default the one called `final`. If there is no `final`, the last theorem is used,
  or the one you name with `--theorem`.
- **The English reading** comes from comments of the form `(* Name x : gloss *)` placed before each constant. Without
  them, the HOL checks still run.

## Examples and tests

`examples/` holds five arguments, each with the verdict it should get:

| Example | Expected verdict |
|---|---|
| `valid_modus_ponens.sml` | an argument |
| `named_conclusion.sml` | an argument; the conclusion is not called `final` |
| `idle_premise.sml` | not an argument: one premise does no work |
| `inconsistent_premises.sml` | not an argument: the premises contradict each other |
| `does_not_follow.sml` | not an argument: HOL4 cannot prove the conclusion |

```bash
python3 tests/test_examples.py --host mini      # or --host local
```

## The rest of the repository

```text
holverify/            the verify command
workbench/            the HOL workbench the command runs on
  tools/native_check.py, native_worker.py, export_hol4_terms.sml   running HOL4 and exporting its kernel terms
  tools/reply_check/z3_engine.py      HOL4 terms in Z3: consequence, consistency, smallest supports, hard flaws
  tools/reply_check/plain_english.py  the plain English reading
  tools/hol4_libraries/               optional HOL4 libraries (deontic, Horty)
  (the other tools run the model rounds of the experiment the workbench was first built for)
paper_tools/          tools for writing a whole paper in HOL, one theory per paragraph
  prose_pipeline.py   render (HOL4 check and English for a paragraph) and check (the gate)
  role_check.py       every element of an argument that plays no role in its final theorem
  surplus_check.py    what a paper's sentences say beyond what its argument needs
  formal_check.py     HOL4 and Z3 checks of formal arguments
  paper_graph.py      the files of a paper form one argument, and the end answers the beginning
example_paper/        "Does Making Sense Bind the Dissenter?", written with the paper tools
```

How the engine was used to write a paper is described in [METHODS_REPORT.md](METHODS_REPORT.md).

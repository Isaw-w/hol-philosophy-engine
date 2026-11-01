# HOL workbench

Three rounds per case, each checked mechanically:

1. **Formal argument**: the model answers in free HOL4 (competing views, their arguments, the argument for its final
   conclusion), and HOL4 checks it. A HOL4 error or a checked hard flaw gets a fix round (at most three per argument,
   unless the user gives more).
2. **Cited reply**: the model turns its argument into the reply to the user, citing axioms and theorems per sentence.
3. **Reflective equilibrium**: the model brings the argument and the reply into equilibrium and may revise either.

The current case is `future210/fu178` (Opus 5.5 and GLM 5.3, round-1 prompt v23). Earlier work used `grid450/g02_15`;
Opus runs on g02 are mostly stopped by Anthropic's classifier ("violative cyber content").

## Read the current experiment

[current/README.md](current/README.md) has the six shortcuts (two models, three rounds). Every run, with cost and
result, is in [runs/INDEX.md](runs/INDEX.md); all mechanical checks of every argument are summarized in
[checks/20261020/z3_recheck_all.md](checks/20261020/z3_recheck_all.md). The day-by-day record and the user's own words
are in `../../../EXPERIMENT_LOG.md` (thick_training).

## Where things go

```text
hol/
  current/          Shortcuts to the current pipeline's runs (fu178_opus/, fu178_glm53/, history_20261018/)
  runs/             Complete model records (messages, prompts, costs, HOL4 and Z3 checks), one folder per run
    20261020/         fu178, the g02 UV / lab-tap / log cases, prompts v20 to v23 (the current pipeline is here)
    20261019/         prompts v14 to v19, GLM 5.3 Flash
    20261018/         prompts v6 to v12, the deontic library
    20261016/         the 2026-10-16 runs
    imported/         older runs brought in from the earlier workspace
  prompts/
    current/          links to the prompts the current pipeline used (wording untouched)
    rounds/           round prompts; drafts/ holds every version since 2026-10-18 and the fix messages
    history/          earlier prompt versions
    numbered/         old numbered names (37_… to 44_…), kept as links for old commands
  tools/            Runners and HOL4 tools (below)
    reply_check/      checks of a reply against its argument
    hol4_libraries/   optional HOL4 libraries: deontic/, horty/
    legacy/           the pre-2026-10-16 tools
    backups/          the 2026-10-18 .bak copies
  checks/           Checks without a model call, by date: 20261020/ (recheck of all arguments, checker tests),
                    20261018/, 20261016/ (erg_probe_20261018/ is the ERG probe)
  data/             Case inputs: ab5_inputs.json (five cases) and cases/ (user-approved g02 query versions)
  docs/             Technical notes (NATIVE.md, VERBALIZATION.md)
  organization/     What each reorganization moved, with hashes
```

## Tools

| Tool | What it does | Model call |
|---|---|---|
| `tools/loop.py` | Round 1: one call, then the HOL4 check and mechanical English | yes |
| `tools/run_native.py` | Round 1: one call (`--model`, `--provider` for a non-Opus model), then the HOL4 check | yes |
| `tools/fix_round.py` | One fix round: HOL4's error lines unchanged + "Revise it.", or `--message FILE` (a user-approved message, e.g. a checked hard flaw); refuses a fourth round unless `--extra-rounds` (only when the user gives more) | yes |
| `tools/review_round.py` | Round 2: continues the conversation with `--message FILE` (the cited-reply prompt); saves the reply or checks a revised argument | yes |
| `tools/equilibrium_round.py` | Round 3: continues with `--message FILE` (the reflective-equilibrium prompt); checks a revised argument | yes |
| `tools/round2.py` | Round 2; `--continue-round1` continues the round-1 conversation | yes, with `--run` |
| `tools/round3.py` | Round 3; `--english source` sends the shorter source-located English | yes, with `--run` |
| `tools/native_check.py` | Run HOL4 on a response and export the term tree | no |
| `tools/verbalize_hol4.py` | Mechanical English from the term tree | no |
| `tools/final_check.py` | The final theorem against all premises and competing conclusions | no |
| `tools/reply_check/plain_english.py` | The argument as stiff plain English; `--no-names`, `--bare` | no |
| `tools/reply_check/gloss_claims.py` | Claims glossed with the model's notation comments | no |
| `tools/reply_check/hidden_premises.py` | Every premise the final theorem rests on but does not state, and every smallest set of them, each checked by HOL4 | no |
| `tools/reply_check/isolated_parts.py` | Every part the final theorem does not use, and its support structure: linked, convergent, serial, divergent | no |
| `tools/reply_check/argument_checks.py` | Consistency, sensitivity, near restatements, foundations, open questions, and statements about truth values (what holds only because "Knows p" or "Ought p" takes p's truth value) | no |
| `tools/reply_check/z3_engine.py` | The argument translated once into Z3 (on the mini, venv_logreco). Bool, num (non-negative), int, real, lists and strings (sequences), enumerations and recursive datatypes (Z3 datatypes) are translated directly; anything else goes through a generic encoding (functions as objects, lambdas lifted, as in Sledgehammer), with the definitions and axioms of the library constants used, which HOL4 exports and the engine instantiates at the types used; a 'does not follow' that rests on the generic encoding is reported as unknown. Every answer the engine draws from a countermodel ('does not follow', 'consistent', a creative definition, an opaque place, a smallest support) counts only if the countermodel holds up in HOL semantics (`hol_semantics.py`, below); a contradiction, collapse or explosion counts only after HOL4 replays it as a proof. Checks: consistency and every smallest support of each conclusion, with three states (follows / does not, with a countermodel / unknown); isolated parts; every-position substitution test (each argument place of each predicate, inside each smallest support: transparent if the conclusion survives when what fills it is replaced by anything, or by anything with the same truth value; opaque if Z3 finds a countermodel); misused logic, a hard flaw (a declared constant with no definition that takes a truth value, e.g. `Ought : bool -> bool`); contents given as text, a hard flaw (a constant or constructor that makes a thing out of a string, e.g. `Content "..."`); creative definitions, a hard flaw (one predicate defined twice, the definitions asserting something nothing else gives); collapse and explosion under violation, hard flaws agreed in deontic logic (a predicate forced to hold of exactly what happens; principles that alone settle whether an evaluated act happens); generality, a measure (principles that name particular things); vacuous conditional conclusions; different names forced to be one thing; restated premises (a premise repeated as it stands in the final is listed; one that says a conclusion in other words, only through definitions and biconditional starting points, gets a warning) | no |
| `tools/mini_scheduler.py` | Runs many round-1 jobs on the mini itself, with no ssh: each case-with-model goes call, HOL4, fix rounds (HOL4's own error and 'Revise it.', at most 3), Z3, in its own thread; model calls, HOL4 checks and Z3 checks each have their own number of slots; the same messages, request and folder layout as `run_native.py` and `fix_round.py` (checked byte for byte: 10 of 10 first rounds, 38 of 38 fix rounds); resumable | yes |
| `tools/mini_launch.py` | `start JOBS.json` copies the tools, inputs and prompt to the mini and starts the scheduler (the key goes over once through the pipe); `status RUNDIR`; `pull RUNDIR` copies the results back | yes |
| `tools/finish_run.py` | Finishes a run whose call came back but whose runner stopped before fetching the answer: fetches it from the mini and runs the HOL4 check | no |
| `tools/reply_check/hol_semantics.py` | Checks a Z3 countermodel in HOL semantics, as Nitpick checks a potential counterexample: the original HOL statements are evaluated in an interpretation built from the model (declared types are the model's universes, primitives take the model's values, every defined constant is evaluated by its own definition, so every definition holds at every type it is used at); quantifiers over infinite types are decided exactly by the model's table values one by one and one stand-in for each gap between them; three values, and anything undecided is unknown | no |
| `tools/reply_check/hol2isa.py` | An argument as an Isabelle/HOL theory whose lemma `False` Nitpick tries to falsify, i.e. a model of the definitions, premises and axioms (trial: `checks/20261022/nitpick_trial/`) | no |
| `tools/reply_check/reply_citations.py` | The citations in a cited reply, matched to the argument's items (from the Z3 engine's supports and isolated parts, or the older hidden-premise results) | no |
| `tools/reply_check/minimal_support.py` | Each "because A, so B" step of a cited reply: is A in some smallest support of B | no |
| `tools/reply_check/cite_check.py` | Round-2 theorem citations, each pair scored by NLI on the mini | no |
| `tools/reply_check/nli_check.py`, `nli_pairs.py` | DeBERTa-v3-large NLI on the mini | no |
| `tools/hol4_libraries/deontic/`, `horty/` | Optional HOL4 libraries (Carmo–Jones deontic logic; Horty's reasons as defaults) | no |

The libraries are built on the mini in `~/thick_training/hol4_lib`; the HOL4 checks put that folder on the load path.

## Commands

Run these from **this `hol/` folder**. Every output folder must be new; put new runs in `runs/<date>/`. Anything marked "model call" runs only after
the exact input has been shown and approved.

```sh
# Round 1 (model call); add --model z-ai/glm-5.3 --provider z-ai/fp8 for GLM 5.3
python3 tools/run_native.py future210/fu178 --prompt prompts/current/round_1.txt --out runs/DATE/NEW_RUN

# A fix round after a HOL4 failure, or with a user-approved message (model call)
python3 tools/fix_round.py runs/DATE/RUN --out runs/DATE/NEW_RUN
python3 tools/fix_round.py runs/DATE/RUN --message prompts/current/fix_misused_logic.txt --out runs/DATE/NEW_RUN

# Round 2 and round 3 (model calls)
python3 tools/review_round.py runs/DATE/ROUND1_RUN --message prompts/current/round_2.txt --out runs/DATE/NEW_RUN
python3 tools/equilibrium_round.py runs/DATE/ROUND2_RUN --message prompts/current/round_3.txt --out runs/DATE/NEW_RUN

# Checks (no model call)
python3 tools/reply_check/z3_engine.py runs/DATE/RUN            # on the mini; --local runs here
python3 tools/reply_check/reply_citations.py runs/DATE/REPLY_RUN runs/DATE/ARGUMENT_RUN
python3 tools/reply_check/minimal_support.py runs/DATE/REPLY_RUN runs/DATE/ARGUMENT_RUN
python3 tools/final_check.py runs/DATE/RUN
python3 tools/reply_check/plain_english.py runs/DATE/RUN --bare
```

Model calls go through OpenRouter on the mini, reasoning effort high: Opus 5.5 from Anthropic by default, other models with `--model` and `--provider` (written to the run's model.json and kept by later rounds).

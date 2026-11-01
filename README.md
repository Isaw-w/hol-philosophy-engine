# HOL philosophy engine

An engine for writing philosophy papers in HOL. Every paragraph of a paper is first written as a small HOL4 theory:
each sentence is an axiom or a theorem, in reading order, and the paragraph's conclusion is a theorem called `final`.
HOL4 checks every theory, a Z3 engine checks that the premises are consistent and that each one is needed, and a
renderer reads the checked theory back as plain English. The prose of the paper is then written from the checked HOL,
sentence by sentence.

The method and the engine are described in [METHODS_REPORT.md](METHODS_REPORT.md).

## Layout

```text
workbench/            The HOL workbench: running HOL4, exporting its terms, Z3 checks, mechanical English
  tools/native_check.py         runs HOL4 (or Isabelle) on a source over ssh and exports the kernel term tree
  tools/native_worker.py        the worker that native_check.py starts on the prover host
  tools/export_hol4_terms.sml   exports HOL4 kernel terms as JSON
  tools/reply_check/z3_engine.py    translates a checked HOL4 argument into Z3 once and answers, for any subset of
                                    premises, whether they give the conclusion (with countermodels checked in HOL
                                    semantics), whether they are consistent, and which premises are needed
  tools/reply_check/plain_english.py  reads a checked HOL4 argument as plain English sentences
  tools/hol4_libraries/         optional HOL4 libraries (deontic, Horty)
  docs/                         technical notes on the native check and the verbalization
  (the other tools run the model rounds of the earlier experiment the workbench was built for)
paper_tools/          Tools for papers built on the workbench
  prose_pipeline.py   render: HOL4 check and mechanical English for one paragraph; check: the gate (consistent,
                      every premise needed, no unused axiom)
  role_check.py       finds every element of an argument that plays no role in its final theorem
  surplus_check.py    finds what a paper's sentences say that its argument does not need
  formal_check.py     HOL4 and Z3 checks of formal arguments, printed per check
  paper_graph.py      checks that the files of a paper form one argument: earlier conclusions are later premises,
                      replies refute the premises they answer, and the end answers the beginning
example_paper/        "Does Making Sense Bind the Dissenter?", built with the engine
  gen_paragraphs.py   writes the 28 paragraph theories (prose/s<k>/p<j>/source.sml) and quotes.json
  core/dissenter_core.sml       the core argument: the dilemma, the minimality of its five premises, each path
  checks/whole_paper_check.py   all paragraph axioms at once in Z3: consistency, and that no path is settled
  checks/williams_dilemma_check.py  Williams's commitments in the shared language, and the ways out, in Z3
```

## Requirements

- Python 3 and the `z3-solver` package.
- HOL4 (Trindemossen 2) on a host reachable by ssh. The tools call it `mini`; `native_worker.py` takes the path of the
  `hol` binary on that host (`--hol4`).
- Paths are those of the author's machines. `paper_tools/prose_pipeline.py` and the other paper tools name the
  workbench folder in the constant `HOL`; set it to where `workbench/` is.

## Running one paragraph

```bash
python3 paper_tools/prose_pipeline.py render example_paper/prose/s5/p2   # HOL4 check and mechanical English
python3 paper_tools/prose_pipeline.py check  example_paper/prose/s5/p2   # the gate
```

Nothing in `paper_tools/` or in the HOL checks calls a language model. The workbench's round tools that do call a
model read the API key from the environment only.

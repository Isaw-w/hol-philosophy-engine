# Mechanical verbalization prototype

The input is unchanged native HOL4 source. HOL4 executes it and native kernel
destructors export theorem conclusions, undischarged hypotheses, definitions,
and axioms as typed term trees. No printed formula is reparsed by Python.

The exporter also reads scalar theorem values bound with `val`, including
unregistered `Q.prove` results and values inside source-declared structures.
Poly/ML's native namespace and `PTdeclaredAt` metadata identify visible bindings
declared in `source.sml`. A fixed compiler-checked bridge accepts only values
of the native `Thm.thm` type. It does not cast runtime objects, interpolate model
identifiers into code, invoke theorem-producing functions, or parse printed types.
These values appear in the AST's `theorem_values` collection and in the kernel
report with their hypotheses and trust tags. Registered statements and ML values
remain separate records, so a registered theorem can also have a visible ML binding.

The renderer uses fixed English templates for HOL's built-in logical constants.
Consecutive quantifiers of the same kind and associative conjunctions or
disjunctions are grouped for display; quantifier alternation, negation,
implication direction, variable types, and the antecedent/consequent separation
remain explicit. Unrecognized expressions keep their symbol names and structure.
They are not interpreted from their names. Higher-order expressions can therefore
remain technical rather than become fluent English.

```sh
python3 logikey/verbalize_hol4.py saved_response.json --out checks/new-verbalization
```

To rerender an existing native AST without any source execution:

```sh
python3 logikey/verbalize_hol4.py checks/previous/kernel_ast.json \
  --from-ast --out checks/new-rendering
```

Every output line is linked to an AST subtree in `render_trace.json`. Raw source,
code-container extraction, source hashes, native logs, typed AST, renderer source,
and output are retained. The tool makes no model calls and adds no arguments or
recommendations. Failed source execution is not repaired. The exported scope is
the current final theory's registered statements plus final visible scalar theorem
bindings declared in the supplied source. Shadowed or discarded values and values
held only inside lists, tuples, refs, or functions are not collected. This is not
an explanation of every tactic or SML command.

This is structural controlled English, not a formally verified or fully
round-trippable natural-language translator. A trusted lexicon would be needed
to render domain symbols as ordinary language. Model-written glosses can help
readers, but their agreement with formal predicates is a separate question.
The renderer does not recover propositions missing from the logical artifact.

Successful native HOL4 checks now export the AST during the same prover session
and render it automatically. No model call or second source execution is needed.
The run folder receives `mechanical_english.txt` (the complete rendering) and
`source_declarations_english.txt` (axioms plus declarations with exact native
source locations, ordered by those locations). The shorter view can omit authored
statements with unknown locations and is not a replacement for the full record.
No name-based or case-specific filtering is used. Exact-location metadata comes
from HOL4's theorem database and Poly/ML's native declaration metadata.

AST inspection and English rendering are separate from proof validity. An
inspection or rendering error does not turn an accepted proof into a failed
proof; the error is recorded in the check result or verbalization report.

This follows the established abstract-syntax-to-concrete-language approach.
Attempto provides a reversible OWL-to-ACE example; it is not a drop-in HOL4
verbalizer and does not establish this prototype's correctness.

- Native terms: https://hol-theorem-prover.org/docs/trindemossen-2/Description/
- Native ML namespace: https://polyml.org/documentation/Reference/PolyMLNameSpace.html
- Compiler type checking: https://polyml.org/documentation/Reference/PolyMLCompiler.html
- Native declaration metadata: https://polyml.org/documentation/Reference/PolyMLStructure.html
- Grammatical Framework linearization: https://www.grammaticalframework.org/doc/tutorial/gf-tutorial.html
- OWL-to-ACE example: https://attempto.ifi.uzh.ch/site/docs/owl_to_ace.html

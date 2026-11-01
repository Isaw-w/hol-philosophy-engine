# Methods Report: "Does Making Sense Bind the Dissenter?"

1 November 2026

This report says where the paper's idea came from and how the paper was made. Part 1 sets out the author's original
idea, for the paper and for the method, in the author's own words, with what the AI did with each. Part 2 describes
the HOL engine the paper was built with, and what it proved and checked.

The AI throughout is Claude (Anthropic), working in Claude Code. The author's words are given with their dates. The
author's English is given with spelling and grammar corrected; Chinese is quoted as written and followed by an
English translation.

---

## 1. The original idea

### 1.1 The idea of the paper

**Political realism is about local solutions.** The author's framing of political realism is that it deals with
local solutions to basic political problems: a power P exercised over those who live under it, S, with a legitimation
J. Realism accepts such solutions on their own terms, and it also criticizes them. On 31 October 2026 the author fixed
the core of the project as the question why realism has to be internalist, with two pillars:

> "We should focus on the core problem: why realism has to be internalist, right?"

> "Yes: first, it accepts local solutions; second, it also criticizes them. Remember this."

**The question of this paper.** On 1 November 2026, after the claims of realism and of internalism had been written in
one shared formal language at the author's direction, the author asked whether Williams's own argument contains a
dilemma, and whether it can be solved:

> "I want to know whether there is a dilemma inside Williams's argument. If there is, has Williams solved it? If not,
> is it possible to solve it? I have formalized the claims about making sense and internalism, right? If we use the
> shared language, can we actually argue about this?"

The AI answered in the shared language. With a hard-case dissenter, Williams's commitments clash with the strong
reading of his acceptance claim, the reading on which making sense gives authority over every member. Williams's
stated commitments are consistent, and they settle the dilemma on the internalist side. The author then asked which
way making sense leans:

> "So for Williams, realism accepts either externalism together with local solutions or internalism together with
> local solutions, right? But which way does making sense lean?"

The AI answered that making sense is internal at the level of the group S and external to any single member, and that
Williams's own account of its normativity leans to the internalist horn.

**The tension, and the aim of the paper.** The author then fixed the paper's subject and its aim:

> "Yes, this is what the whole paper is about. We are not defending a position; we just want to tell others that
> realism seems to have this problem. Making sense seems to be externalist with respect to the individual, right, and
> internalist with respect to a group, an 'us'. But internalism is about the individual, not about a group, so there
> is a tension. Is there a way to resolve it? We explore different paths, but never say which one we favour."

This is the paper. Making sense, the standard by which Williams's realism accepts local solutions, is internal to the
group and external to the individual member. Williams's internalism about reasons concerns the individual, and through
the claim of authority it makes authority internal to each member. At a hard-case dissenter the two cannot both govern
authority. The paper shows the tension, locates it in Williams's texts, and sets out the paths through it without
favouring any.

**Instructions on the writing.** The author asked for a paper that is professional and mature, states its case without
hedging, and favours no path:

> "Yes, rewrite it. Be professional and mature: no hedging, and no acknowledging of limitations."

and then for three rounds of refinement:

> "Keep refining it for three rounds, with good HOL formalization and to an academic standard, until you cannot
> improve it any further."

**What the AI did.** The AI read the sources and checked every quotation against them. It drafted the shared formal
language at the author's direction, and stated the dilemma, its five premises and the six paths. It found the textual
support and the textual costs of each path in Williams and Sleat. It wrote the HOL and the prose, and ran every check
described in Part 2. Where the AI offered options, the author chose; each choice is recorded in the session. For
example, the author chose to extend the corrected outlook to Williams's sound deliberative route, to answer Sleat's
double bind, and then to rewrite the paper as a neutral account of the tension.

### 1.2 The idea of the method

**The paper itself is written in HOL.** The method is the author's. On 21 October 2026, correcting the AI, which had
taken the method to formalize a finished text:

> "不是的。反了。论文本身就用 HOL 去写。然后转换成文字稍微 Polish 就够了。"
>
> (No. It is the other way round. The paper itself is written in HOL. Then it is converted into text, and a light
> polish is enough.)

**Every argument is minimal.** The same day, the author set the standard for the paper's core, the definition of an
argument in Besnard and Hunter (*Elements of Argumentation*, 2008):

> "组前提加一个结论，前提彼此一致、能推出结论，而且是最小的，去掉任何一条都推不出来。……这个论文的核心要遵守这个。然后润色的时候可以加读起来流畅的句子。"
>
> (A set of premises plus a conclusion: the premises are consistent with one another, they entail the conclusion, and
> they are minimal, so that removing any one of them, the conclusion no longer follows. … The core of the paper must
> keep to this. Then, in the polish, sentences may be added that make it read fluently.)

**Nothing in the HOL without a role.** The author asked for a general detector of idle elements:

> "No, not five of them: a universal detector of the elements in a HOL argument that play no part in the final
> argument."

This became `role_check.py`. Later (29 October 2026) the author extended the rule to the parts of a sentence:

> "No unnecessary parts or elements in a sentence, for example 'it is A, not B'. Often B contributes nothing to the
> HOL as a whole, and we should drop it."

**HOL as the backbone of ordinary academic writing.** On 30 October 2026:

> "Normal academic writing should have a HOL template."

and on 1 November 2026, for the explanatory sentences of a paper:

> "Write the writing itself in HOL. It does not have to be strictly logical, because many sentences are there to
> explain, just as in ordinary writing, but it helps you write clearly."

So every sentence of the paper, explanatory sentences included, has its place in a paragraph's HOL as an axiom or a
theorem, in reading order. The logic of an explanatory sentence may be thin; what matters is that the paragraph's
sentences and its HOL correspond one to one, and that the HOL is checked.

---

## 2. The HOL engine

### 2.1 What the engine is

The engine has two parts. The code is in this repository.

**The HOL workbench** (`workbench/`). It was built for an earlier experiment in which models argue in HOL4, and it
supplies the checking machinery:

- `native_check.py` and `native_worker.py` run HOL4 (Trindemossen 2) on a remote host, the author's Mac mini, over
  ssh. They check whether the theory is proved and export HOL4's kernel term tree as JSON
  (`export_hol4_terms.sml`).
- `reply_check/z3_engine.py` translates the checked HOL4 argument into Z3 once. For any subset of the premises it then
  says whether they give the conclusion, finding a countermodel when they do not and checking that countermodel in HOL
  semantics. It also says whether the premises are consistent and which premises the conclusion needs.
- `reply_check/plain_english.py` reads a checked HOL4 argument back as plain English, from the glosses given in the
  source. This is the "mechanical English".

**The paper tools** (`paper_tools/`), built for the author's method:

- `prose_pipeline.py render` runs HOL4 on a paragraph theory and produces its mechanical English.
- `prose_pipeline.py check` runs the gate. It passes a paragraph only if all of the following hold:
  - the paragraph has premises;
  - no premise is idle, meaning every premise is needed for the paragraph's `final`;
  - no axiom goes unused;
  - the premises are consistent;
  - the lists of supports are complete;
  - no hard flaw is found.
- `role_check.py` splits every premise into its smallest pieces and finds any piece that plays no role in the final
  theorem.
- `surplus_check.py` finds what the English of a gloss says beyond what the argument needs, such as an "A, not B" in
  which B does no work.
- `paper_graph.py` checks that a paper's files form one argument: earlier conclusions are later premises, each reply
  refutes the premise it answers, and the end answers the beginning.

### 2.2 How this paper was built

1. **Shared language.** The claims of realism (Claims 1 and 3), internalism and externalism about authority, and the
   understandings of making sense were written in one notation: P, S, J, the historical and cultural circumstances of
   S, and a member's corrected outlook. That made it possible to put the claims side by side.
2. **Core argument in HOL.** `example_paper/core/dissenter_core.sml` states the dilemma's five premises, quantified
   over all persons and predicates so that none is asserted:
   - the strong reading;
   - the link between authority and reasons;
   - internalism about reasons;
   - the allowance that the legitimation makes sense while the dissenter is a member;
   - the dissenter's hard case.
3. **Paragraph HOL.** `example_paper/gen_paragraphs.py` writes one HOL4 theory per paragraph, 28 in all. Every sentence
   is an axiom or a theorem in reading order. Each source is entered as "Williams writes that [Qn]" with a reading
   premise, and the quotations are kept in `quotes.json`.
   - Because the paper argues for no path, Williams's commitments enter under the proposition "Williams's realism
     holds".
   - The horns of the dilemma, and each of the six paths, enter as conditionals.
   - So no paragraph asserts a premise that one of the paths gives up.
4. **Checks on every paragraph.** HOL4 proves each paragraph's `final`, and each paragraph passes the gate.
5. **Check of the whole paper.** `example_paper/checks/whole_paper_check.py` loads every axiom of all 28 paragraphs into
   Z3 at once. It checks that they are consistent. It also checks that the paper is neutral: each path, the strong
   reading, internalism about authority, internalism about reasons and the link between authority and reasons can each
   hold or fail together with the paper's premises.
6. **Prose from the HOL.** The prose was written from each paragraph's HOL, sentence by sentence. Every quotation was
   checked word for word against the source text, with its page.
7. **Refinement.** Three rounds followed, each checked again in full:
   - Round 1 moved the core results from stipulation to proof and corrected six paraphrases of the sources.
   - Round 2 defined "internal" and "external" once and introduced the term "reason of authority".
   - Round 3 checked each sentence against its HOL.

### 2.3 What was proved and checked

**Proved in HOL4** (`dissenter_core.sml`):

- The five premises of the dilemma cannot all hold.
- Any four of them can hold together. There is one proof for each premise left out, so each path's way out is
  coherent. On the first path, authority still holds over the other members.
- Without internalism, the dilemma still stands: either some reason of authority is one the member cannot reach, or
  the strong reading fails.
- The strong reading joined to internalism would make the group's standard fix every member's corrected outlook.

**Checked for the paper:**

- All 28 paragraph theories are proved by HOL4 and pass the gate.
- All the paper's premises, taken together, are consistent.
- The paper settles none of the six paths.
- All 17 quotations match the source texts.

**What the checks cover.** HOL4 and Z3 check form: whether a conclusion follows, whether premises are consistent,
whether a premise or a piece of one does any work. Whether a premise is true, and whether a reading of a text is
faithful, was settled by reading the sources in context. Each attribution to Williams and Sleat was checked against
the page it cites.

### 2.4 Running the engine

See [README.md](README.md). The engine needs Python 3 with `z3-solver`, and HOL4 on a host reachable by ssh. None of
the checks calls a language model.

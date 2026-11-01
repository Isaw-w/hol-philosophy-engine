"""Williams's commitments in the shared language, checked with Z3.
Is there a dilemma, which premises make it, and which ways out are consistent with all of Williams's
stated commitments?"""
import itertools
import z3

Person = z3.DeclareSort("person")
a = z3.Const("a", Person)
d = z3.Const("d", Person)          # the hard-case dissenter
o = z3.Const("o", Person)          # another member
Member, ClaimMade, Claim, Reason, Route, Hard = (z3.Function(n, Person, z3.BoolSort()) for n in
                                                  ["Member", "ClaimMade", "Claim", "Reason", "Route", "Hard"])
GB, MS, Legit = z3.Bools("GoesBeyond MakesSense Legit")

W = {   # Williams's stated commitments, each with its text
    "Claim 1 (2005: 11)":                      z3.Implies(z3.And(GB, MS), Legit),
    "claim made over each subject (2005: 4, 6)": z3.ForAll([a], z3.Implies(Member(a), ClaimMade(a))),
    "reasons of authority (2005: 6)":          z3.ForAll([a], z3.Implies(Claim(a), Reason(a))),
    "internalism (1995: 35)":                  z3.ForAll([a], z3.Implies(Reason(a), Route(a))),
    "hard case (1995: 36, 41-43)":             z3.ForAll([a], z3.Implies(Hard(a), z3.Not(Route(a)))),
    "satisfaction: makes sense with a hard-case member (2005: 135-136)":
        z3.And(GB, MS, Member(d), Hard(d)),
}
STRONG = {"strong reading (Sleat 2013: 124)": z3.Implies(z3.And(GB, MS), z3.ForAll([a], z3.Implies(Member(a), Claim(a))))}


def sat(fs):
    s = z3.Solver()
    s.add(*fs)
    return s.check() == z3.sat


def entails(fs, goal):
    return not sat(list(fs) + [z3.Not(goal)])


ws = list(W.values())
print("1. Williams's stated commitments together:", "consistent" if sat(ws) else "INCONSISTENT")
print("2. ... add the strong reading:", "consistent" if sat(ws + list(STRONG.values())) else "INCONSISTENT")
core = {k: v for k, v in {**W, **STRONG}.items() if not k.startswith(("Claim 1", "claim made"))}
print("3. Minimal: drop each premise of the clash and see whether the rest are consistent")
for k in core:
    rest = [v for kk, v in core.items() if kk != k]
    print("   without", k, "->", "consistent" if sat(rest) else "still inconsistent")
print("4. Williams's stated commitments entail that the strong reading fails:",
      entails(ws, z3.Not(list(STRONG.values())[0])))
print("5. ... and entail: P legitimate over S, and the claim over the hard-case dissenter false:",
      entails(ws, z3.And(Legit, z3.Not(Claim(d)))))
print("6. The solution is not empty: with all of Williams's commitments, the claim can still be true over"
      " another member:", sat(ws + [Member(o), Claim(o)]))
noint = [v for k, v in W.items() if not k.startswith("internalism")] + list(STRONG.values())
print("7. The first horn (strong reading, no internalism) gives the dissenter an external reason:",
      entails(noint, z3.And(Reason(d), z3.Not(Route(d)))), "| consistent:", sat(noint))

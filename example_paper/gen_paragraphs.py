"""Write the paragraph HOL of "Does Making Sense Bind the Dissenter?", built on our formal claims
(williams_two_claims.md: Claims 1 and 3; internalism_claims.md: internalism and externalism about authority;
making_sense_formal.md: the shared language P, S, J, C(S), corrected outlook).
One source.sml per paragraph, prose/s<k>/p<j>/source.sml, every sentence an axiom or a theorem in reading order,
and a Theorem `final`.

The paper shows a tension and favours no way out of it. So Williams's commitments enter under WR (Williams's
realism holds), the horns of the dilemma enter as conditionals, and each path enters as a conditional on the
path's being taken: no paragraph asserts a premise that one of the paths gives up. Ash's case is the paper's
supposition."""
import json, re, shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent

CONSTANTS = {  # name: (type, gloss)
    "Ash": (":person", "Ash : Ash"),
    "Member": (":person -> bool", "Member a : a lives under P"),
    "GoesBeyond": (":bool", "GoesBeyond : J goes beyond the assertion of P"),
    "WouldSense": (":bool", "WouldSense : J would make sense to us as a legitimation of P as authority were we S in the light of C(S)"),
    "MakesSense": (":bool", "MakesSense : J makes sense to S as a legitimation"),
    "Legit": (":bool", "Legit : realism counts P as legitimate over S as a whole"),
    "Many": (":bool", "Many : a substantial number of S are satisfied"),
    "RequiresAll": (":bool", "RequiresAll : universal acceptance is required for meeting the demand"),
    "Coercible": (":person -> bool", "Coercible a : P can rightfully coerce a by its own lights"),
    "ClaimMade": (":person -> bool", "ClaimMade a : P claims authority over a"),
    "Claim": (":person -> bool", "Claim a : P's claim of authority over a is true"),
    "Blames": (":person -> bool", "Blames a : P's claim over a is focused blame of a's resistance"),
    "Reason": (":person -> bool", "Reason a : a has a reason of authority: a reason against resisting P besides P's hold over a"),
    "Corr": (":person -> bool", "Corr a : a's corrected outlook gives a a reason against resisting P besides P's hold over a"),
    "Rejects": (":person -> bool", "Rejects a : a rejects J"),
    "InGroup": (":person -> bool", "InGroup a : a belongs to the group of Williams's example"),
    "Hard": (":person -> bool", "Hard a : a is a hard-case dissenter"),
    "HardCasesExist": (":bool", "HardCasesExist : hard cases exist"),
    "AcceptEach": (":bool", "AcceptEach : the strong reading of Claim 1 holds"),
    "ExtToward": (":person -> bool", "ExtToward a : externalism about authority holds toward a"),
    "WR": (":bool", "WR : Williams's realism holds"),
    "Prudent": (":person -> bool", "Prudent a : P meets a as a prudent state meets possible secession"),
    "Meets": (":bool", "Meets : P meets the demand for legitimation"),
    "WilliamsLeg": (":bool", "WilliamsLeg : Williams holds that what we acknowledge as legitimate here and now is what here and now makes sense as a legitimation of power as authority (2005, 11)"),
    "WilliamsMeetsLeg": (":bool", "WilliamsMeetsLeg : Williams holds that meeting the demand is what distinguishes a legitimate state from an illegitimate one (2005, 4)"),
    "WilliamsTie": (":bool", "WilliamsTie : Williams assumes a close connection between focused blame and the agent's reasons (1995, 41) and concludes that the proleptic mechanism is likely to prove essential to an account of focused blame (1995, 44)"),
    # the two levels
    "GroupInternal": (":bool", "GroupInternal : making sense is internal to S: Claim 3 judges J by S's outlook in C(S), and nothing in it is a standard independent of S's outlook that justifies P"),
    "ExtToMember": (":person -> bool", "ExtToMember a : J's making sense to S is a standard independent of a's outlook"),
    "KeepOurs": (":bool", "KeepOurs : being S, in the condition that J would make sense to us if we were S, leaves us with our own beliefs"),
    "SomeFalseMS": (":bool", "SomeFalseMS : something that does not make sense to us because we take it to be false made sense to an earlier society"),
    "CondANotJust": (":bool", "CondANotJust : condition (a) says not much more than that coercion requires legitimation and that the will of the stronger is not itself one, and does not settle what justifies P"),
    "DefLevels": (":bool", "DefLevels : a standard is internal to a person or a group when their outlook settles whether it is met, and external to them, or independent of their outlook, when it does not"),
    "ReadsS": (":bool", "ReadsS : Claim 3 reads the outlook of S, not that of any one member"),
    "WilliamsFalse11": (":bool", "WilliamsFalse11 : Williams allows that some of what made sense to earlier societies does not make sense to us because we take it to be false (2005, 11)"),
    "WilliamsAxiom": (":bool", "WilliamsAxiom : Williams says that might does not imply right (2005, 5-6), and that the universal paradigm of injustice, simply in this form, is indeterminate about what it requires and says not much more than that coercion requires legitimation and that the will of the stronger is not itself a legitimation (2005, 23)"),
    "WilliamsOurCase": (":bool", "WilliamsOurCase : Williams says that what makes most sense to us is a structure of authority that we think we should accept (2005, 11)"),
    "WilliamsFanatics": (":bool", "WilliamsFanatics : Williams says that a legitimation can stop making sense while the truly fanatical can still bring themselves to believe it (2005, 71)"),
    # Williams's two pulls
    "PointsFirst": (":bool", "PointsFirst : Williams's treatment of dissenters points to the strong reading, and Sleat reads Williams as holding it"),
    "SupportsBoth": (":bool", "SupportsBoth : Williams's texts support both horns of the dilemma"),
    "WilliamsDecides": (":bool", "WilliamsDecides : in the 1995 essay or the 2005 book, Williams says whether a legitimate state has authority over a member whose own outlook gives no reason of authority"),
    "EveryPathPays": (":bool", "EveryPathPays : every path through the tension gives up one premise of the dilemma"),
    "Plan": (":bool", "Plan : the paper proceeds as its opening sets out"),
    "Owes": (":bool", "Owes : realism in Williams's form owes an account of whose outlook a claim of authority answers to"),
    # the paths
    "PathA": (":bool", "PathA : the first path, keeping the two levels apart, is taken"),
    "PathB": (":bool", "PathB : the second path, letting the group's standard govern authority over every member, is taken"),
    "PathC": (":bool", "PathC : the third path, lifting internalism to the group, is taken"),
    "PathD": (":bool", "PathD : the fourth path, lowering legitimacy to each member, is taken"),
    "PathE": (":bool", "PathE : the fifth path, cutting the link between authority and reasons, is taken"),
    "PathF": (":bool", "PathF : the sixth path, denying that the gap opens, is taken"),
    "FootholdA": (":bool", "FootholdA : Williams's texts give the first path a foothold"),
    "WilliamsCease": (":bool", "WilliamsCease : Williams says that those beyond blame's mechanisms are people we cease to blame (1995, 43)"),
    "SleatPol": (":bool", "SleatPol : Sleat reads Williams's politics as a relationship in which the state has the legitimate authority to coerce, wherever the demand has been met (2013, 123)"),
    "CostA": (":bool", "CostA : on the first path a legitimate state stands to some of its members in relationships that are not political in Sleat's sense"),
    "WilliamsDoubtExt": (":bool", "WilliamsDoubtExt : Williams doubts that any external reason statement is true (1995, 40)"),
    "WilliamsNonNorm": (":bool", "WilliamsNonNorm : Williams says that making sense applied to others is not normative (2005, 11)"),
    "CostB": (":bool", "CostB : the second path goes against Williams's doubt about external reasons, his account of making sense applied to others, and his treatment of hard cases"),
    "GroupReason": (":bool", "GroupReason : reasons of authority belong to S, and a member has them as one of S"),
    "WilliamsAudience": (":bool", "WilliamsAudience : Williams says that the theorist speaks to an audience who share these conceptions of reasonableness or whom the theorist hopes to persuade (2005, 136)"),
    "CostC": (":bool", "CostC : the third path goes against Williams's internalism about each person and leaves Ash outside the audience"),
    "IndivLegit": (":bool", "IndivLegit : for legitimacy, J must make sense to each member's corrected outlook, and P is legitimate to the degree that it does"),
    "Satisfaction": (":bool", "Satisfaction : J can make sense to S while some member's corrected outlook gives no reason not to resist P other than P's hold"),
    "WilliamsEach": (":bool", "WilliamsEach : Williams says there is a sense in which the demand requires a legitimation to be given to every subject (2005, 6), speaks of acceptability to each subject (2005, 7) and treats the considerations that support legitimacy as scalar (2005, 10)"),
    "CostD": (":bool", "CostD : the fourth path goes against Williams's denial that meeting the demand requires everyone's acceptance"),
    "WilliamsJustified": (":bool", "WilliamsJustified : Williams allows that what presents itself as blame may in fact be only a rejection of what someone has done, perhaps an entirely justified one (1995, 44)"),
    "WilliamsWarfare": (":bool", "WilliamsWarfare : Williams separates the reasons given by a claim for authority from the reasons for stopping warfare (2005, 6)"),
    "CostE": (":bool", "CostE : the fifth path goes against Williams's account of the reasons a claim of authority gives"),
    "HardMember": (":bool", "HardMember : some member under a legitimation that makes sense is a hard case"),
    "WilliamsProlepsis": (":bool", "WilliamsProlepsis : Williams says that very powerful political discourse can be proleptic (2005, 26) and that blame works proleptically through a disposition to have the respect of others (1995, 41-42)"),
    "CostF": (":bool", "CostF : the sixth path goes against Williams's hard cases and his anarchists and utterly unreasonable"),
    "FourHold": (":bool", "FourHold : any four of the five premises of the dilemma can hold together"),
    "DTogether": (":bool", "DTogether : on the fourth path internalism about authority and the strong reading can hold together"),
    "OnlyA": (":bool", "OnlyA : the first path alone gives up nothing Williams states"),
}
for n in range(1, 18):
    who = "Sleat" if n in (12, 17) else "Williams"
    CONSTANTS[f"{who}Q{n}"] = (":bool", f"{who}Q{n} : {who} writes that [Q{n}]")

QUOTES = {
    "Q1": ["Williams 2005, 11", "there is a legitimation offered which goes beyond the assertion of power; and we can recognize such a thing because in the light of the historical and cultural circumstances, and so forth, it MS to us as a legitimation"],
    "Q2": ["Williams 2005, 11", "what they do MS if it would MS to us if we were them"],
    "Q3": ["Williams 2005, 136", "may be anarchists, or utterly unreasonable, or bandits, or merely enemies"],
    "Q4": ["Williams 2005, 136", "should include a substantial number of the people"],
    "Q5": ["Williams 2005, 4", "anyone who is in its power, whom by its own lights it can rightfully coerce under its laws and institutions"],
    "Q6": ["Williams 2005, 6", "these claims constitute its claim of authority over B"],
    "Q7": ["Williams 2005, 6", "resents it, forbids it, rallies others to oppose it as wrong"],
    "Q8": ["Williams 1995, 41–42", "to tell him he had a reason to act otherwise"],
    "Q9": ["Williams 1995, 35", "A has a reason to φ only if he could reach the conclusion to φ by a sound deliberative route from the motivations he already has"],
    "Q10": ["Williams 2005, 136", "that there is no legitimate government outside their own creed, and that the liberal state makes no legitimate demand on them"],
    "Q11": ["Williams 1995, 43", "some hard cases, people who lie beyond any such mechanism"],
    "Q12": ["Sleat 2013, 124", "had no implications for its right to rule and coerce them"],
    "Q13": ["Williams 2005, 136", "as any prudent state which wants to avoid violence meets the possibilities of secession"],
    "Q14": ["Williams 1995, 40", "blaming agents for specific acts or omissions"],
    "Q15": ["Williams 2005, 135", "purports to legitimate its use of power in relation to them"],
    "Q16": ["Williams 2005, 137", "has an entirely reasonable account of why it has ceased"],
    "Q17": ["Sleat 2013, 126", "legitimate but non-political relationships of successful domination"],
}

CLAIM1 = "GoesBeyond /\\ MakesSense ==> Legit"
CLAIM3 = "MakesSense <=> GoesBeyond /\\ WouldSense"
EACH = "AcceptEach <=> (GoesBeyond /\\ MakesSense ==> !a. Member a ==> Claim a)"
INTAUTH = "!a. Member a /\\ Claim a ==> Corr a"
EXT = "!a. ExtToward a <=> Claim a /\\ ~Corr a"
HARDDEF = "!a. Hard a <=> Rejects a /\\ ~Corr a"
BRIDGE = "!a. Member a /\\ Claim a ==> Reason a"
ADDRESS = "!a. Member a ==> ClaimMade a"
INTR = "!a. Reason a ==> Corr a"
EXTMEM = "!a. Member a ==> ExtToMember a"
CASE = "Member Ash /\\ Rejects Ash /\\ GoesBeyond /\\ MakesSense /\\ ~Corr Ash"
ASH = "GoesBeyond /\\ MakesSense /\\ Member Ash /\\ ~Corr Ash"
NOBOTH = f"~(AcceptEach /\\ ({INTAUTH}))"
DROPS = (f"(PathA ==> ~AcceptEach) /\\ (PathB ==> ~({INTR})) /\\ (PathC ==> ~({INTAUTH})) /\\ "
         f"(PathD ==> ~Satisfaction) /\\ (PathE ==> ~({BRIDGE})) /\\ (PathF ==> ~HardMember)")

# (section, paragraph): list of ("ax" | "thm", term), the last theorem being the paragraph's conclusion
PARAS = {
    # abstract
    (0, 1): [("ax", CLAIM1), ("ax", "GroupInternal"), ("ax", EXTMEM), ("ax", f"WR ==> ({INTAUTH})"),
             ("ax", f"({CASE}) ==> ExtToward Ash \\/ ~AcceptEach"), ("ax", "SupportsBoth"), ("ax", "~WilliamsDecides"),
             ("ax", "FourHold"), ("ax", "EveryPathPays"),
             ("thm", f"({CLAIM1}) /\\ GroupInternal /\\ ({EXTMEM}) /\\ (WR ==> ({INTAUTH})) /\\ "
                     f"(({CASE}) ==> ExtToward Ash \\/ ~AcceptEach) /\\ SupportsBoth /\\ ~WilliamsDecides /\\ FourHold /\\ EveryPathPays")],
    # opening: local solutions and internalism
    (1, 1): [("ax", CLAIM1), ("ax", f"WR ==> ({INTR})"), ("thm", f"({CLAIM1}) /\\ (WR ==> ({INTR}))")],
    # opening: the two levels and the dilemma
    (1, 2): [("ax", "GroupInternal"), ("ax", EXTMEM), ("ax", f"WR ==> ({INTAUTH})"),
             ("ax", f"({CASE}) ==> ExtToward Ash \\/ ~AcceptEach"),
             ("thm", f"GroupInternal /\\ ({EXTMEM}) /\\ (WR ==> ({INTAUTH})) /\\ (({CASE}) ==> ExtToward Ash \\/ ~AcceptEach)")],
    # opening: thesis and plan
    (1, 3): [("ax", "SupportsBoth"), ("ax", "~WilliamsDecides"), ("ax", "FourHold"), ("ax", "EveryPathPays"), ("ax", "Plan"),
             ("thm", "SupportsBoth /\\ ~WilliamsDecides /\\ FourHold /\\ EveryPathPays /\\ Plan")],
    # I: Claims 1 and 3
    (2, 1): [("ax", "WilliamsQ1"), ("ax", "WilliamsLeg"), ("ax", "WilliamsQ2"),
             ("ax", f"WilliamsLeg /\\ WilliamsQ2 ==> ({CLAIM1})"), ("ax", f"WilliamsQ1 /\\ WilliamsQ2 ==> ({CLAIM3})"),
             ("thm", f"({CLAIM1}) /\\ ({CLAIM3})")],
    # I: making sense is settled for S as a whole
    (2, 2): [("ax", CLAIM3), ("ax", "WilliamsQ3"), ("ax", "WilliamsQ3 ==> ~RequiresAll"), ("ax", CLAIM1),
             ("ax", "WilliamsMeetsLeg"), ("ax", "WilliamsMeetsLeg ==> (Legit ==> Meets)"), ("ax", "WilliamsQ4"),
             ("ax", "WilliamsQ4 ==> (Meets ==> Many)"), ("thm", f"({CLAIM3}) /\\ ~RequiresAll /\\ (MakesSense ==> Many)")],
    # I: making sense is internal to S
    (2, 3): [("ax", "DefLevels"), ("ax", "WilliamsQ2"), ("ax", "WilliamsQ2 ==> (KeepOurs ==> ~SomeFalseMS)"), ("ax", "WilliamsFalse11"),
             ("ax", "WilliamsFalse11 ==> SomeFalseMS"), ("thm", "~KeepOurs"), ("ax", "WilliamsAxiom"),
             ("ax", "WilliamsAxiom ==> CondANotJust"), ("ax", "DefLevels /\\ ~KeepOurs /\\ CondANotJust ==> GroupInternal"),
             ("ax", "WilliamsOurCase"), ("thm", "GroupInternal /\\ WilliamsOurCase")],
    # I: to each member it is external
    (2, 4): [("ax", "WilliamsFanatics"), ("ax", "WilliamsQ4"), ("ax", "~RequiresAll"), ("ax", "ReadsS"), ("ax", "DefLevels"),
             ("ax", f"WilliamsFanatics /\\ WilliamsQ4 /\\ ~RequiresAll /\\ ReadsS /\\ DefLevels ==> ({EXTMEM})"), ("thm", EXTMEM)],
    # II: authority is claimed over each member
    (3, 1): [("ax", "WilliamsQ5"), ("ax", "WilliamsQ5 ==> !a. Member a ==> Coercible a"), ("ax", "WilliamsQ6"),
             ("ax", "WilliamsQ6 ==> !a. Coercible a ==> ClaimMade a"), ("thm", ADDRESS)],
    # II: on Williams's account a true claim of authority gives a reason
    (3, 2): [("ax", ADDRESS), ("ax", "WilliamsQ7"), ("ax", "WilliamsQ14"),
             ("ax", "WilliamsQ7 /\\ WilliamsQ14 ==> !a. ClaimMade a ==> Blames a"), ("ax", "WilliamsQ8"), ("ax", "WilliamsTie"),
             ("ax", "WilliamsQ8 /\\ WilliamsTie ==> (WR ==> !a. Blames a /\\ Claim a ==> Reason a)"),
             ("thm", f"WR ==> ({BRIDGE})")],
    # II: Williams's realism is committed to internalism about authority
    (3, 3): [("ax", f"WR ==> ({BRIDGE})"), ("ax", "WilliamsQ9"), ("ax", f"WilliamsQ9 ==> (WR ==> ({INTR}))"),
             ("thm", f"WR ==> ({INTAUTH})")],
    # III: Ash
    (4, 1): [("ax", "WilliamsQ10"), ("ax", "WilliamsQ10 ==> !a. InGroup a ==> Rejects a"),
             ("ax", "InGroup Ash /\\ Member Ash /\\ GoesBeyond /\\ MakesSense"),
             ("thm", "Member Ash /\\ Rejects Ash /\\ GoesBeyond /\\ MakesSense")],
    # III: a hard case
    (4, 2): [("ax", "Rejects Ash"), ("ax", "~Corr Ash"), ("ax", HARDDEF), ("thm", "Hard Ash"),
             ("ax", "WilliamsQ11"), ("ax", "WilliamsQ11 ==> HardCasesExist"), ("thm", "HardCasesExist"),
             ("thm", "Hard Ash /\\ HardCasesExist")],
    # IV: the strong reading
    (5, 1): [("ax", EACH), ("ax", "GoesBeyond /\\ MakesSense /\\ Member Ash"), ("thm", "AcceptEach ==> Claim Ash")],
    # IV: the dilemma
    (5, 2): [("ax", "AcceptEach ==> Claim Ash"), ("ax", "~Corr Ash"), ("ax", EXT), ("thm", "ExtToward Ash \\/ ~AcceptEach")],
    # IV: the first horn, local solutions with externalism
    (5, 3): [("ax", "AcceptEach ==> Claim Ash"), ("ax", "~Corr Ash"), ("ax", EXT), ("thm", "AcceptEach ==> ExtToward Ash")],
    # IV: the second horn, local solutions with internalism
    (5, 4): [("ax", "Member Ash"), ("ax", "~Corr Ash"), ("thm", f"({INTAUTH}) ==> ~Claim Ash"),
             ("ax", CLAIM1), ("ax", "GoesBeyond /\\ MakesSense"), ("thm", f"(({INTAUTH}) ==> ~Claim Ash) /\\ Legit")],
    # V: the dilemma is the difference of levels
    (6, 1): [("ax", "GroupInternal /\\ ExtToMember Ash"), ("ax", EACH),
             ("thm", f"(AcceptEach /\\ ({INTAUTH})) ==> (GoesBeyond /\\ MakesSense ==> !a. Member a ==> Corr a)"),
             ("ax", ASH), ("thm", NOBOTH), ("thm", f"(GroupInternal /\\ ExtToMember Ash) /\\ {NOBOTH}")],
    # V: Williams's texts pull both ways
    (6, 2): [("ax", f"WR ==> ({INTAUTH})"), ("ax", "Member Ash /\\ ~Corr Ash"), ("thm", "WR ==> ~Claim Ash"),
             ("ax", "WilliamsQ15"), ("ax", "~RequiresAll"), ("ax", "WilliamsQ16"), ("ax", "SleatQ12"),
             ("ax", "WilliamsQ15 /\\ ~RequiresAll /\\ WilliamsQ16 /\\ SleatQ12 ==> PointsFirst"),
             ("ax", "PointsFirst /\\ (WR ==> ~Claim Ash) ==> SupportsBoth"), ("ax", "~WilliamsDecides"),
             ("thm", "(WR ==> ~Claim Ash) /\\ PointsFirst /\\ SupportsBoth /\\ ~WilliamsDecides")],
    # V: what follows for Williams's realism
    (6, 3): [("ax", f"WR ==> ({INTAUTH})"), ("ax", NOBOTH), ("thm", "(WR ==> AcceptEach) ==> ~WR"), ("ax", CLAIM1),
             ("ax", ASH), ("thm", "WR ==> Legit /\\ ~Claim Ash"), ("ax", "~WilliamsDecides"), ("ax", "SleatQ17"),
             ("thm", "((WR ==> AcceptEach) ==> ~WR) /\\ (WR ==> Legit /\\ ~Claim Ash) /\\ ~WilliamsDecides /\\ SleatQ17")],
    # VI: the first path, keeping the levels apart
    (7, 1): [("ax", f"PathA ==> ~AcceptEach /\\ ({INTAUTH})"), ("ax", CLAIM1), ("ax", ASH),
             ("thm", "PathA ==> ~AcceptEach /\\ Legit /\\ ~Claim Ash"), ("ax", "WilliamsQ13"), ("ax", "WilliamsCease"),
             ("ax", "WilliamsQ13 /\\ WilliamsCease ==> FootholdA"), ("ax", "SleatPol"), ("ax", "SleatPol ==> CostA"),
             ("thm", "(PathA ==> ~AcceptEach /\\ Legit /\\ ~Claim Ash) /\\ FootholdA /\\ CostA")],
    # VI: the second path, the group's standard governs authority over every member
    (7, 2): [("ax", f"PathB ==> AcceptEach /\\ ({BRIDGE})"), ("ax", "AcceptEach ==> Claim Ash"), ("ax", "Member Ash /\\ ~Corr Ash"),
             ("ax", EXT), ("thm", "PathB ==> ExtToward Ash /\\ Reason Ash /\\ ~Corr Ash"), ("ax", "PointsFirst"),
             ("ax", "WilliamsDoubtExt"), ("ax", "WilliamsNonNorm"), ("ax", "WilliamsCease"),
             ("ax", "WilliamsDoubtExt /\\ WilliamsNonNorm /\\ WilliamsCease ==> CostB"),
             ("thm", "(PathB ==> ExtToward Ash /\\ Reason Ash /\\ ~Corr Ash) /\\ PointsFirst /\\ CostB")],
    # VI: the third path, internalism of the group
    (7, 3): [("ax", "PathC ==> GroupReason /\\ AcceptEach"), ("ax", "AcceptEach ==> Claim Ash"), ("ax", "~Corr Ash"),
             ("ax", EXT), ("thm", "PathC ==> GroupReason /\\ ExtToward Ash"), ("ax", "WilliamsOurCase"), ("ax", "WilliamsQ9"),
             ("ax", "WilliamsAudience"), ("ax", "WilliamsQ9 /\\ WilliamsAudience ==> CostC"),
             ("thm", "(PathC ==> GroupReason /\\ ExtToward Ash) /\\ WilliamsOurCase /\\ CostC")],
    # VI: the fourth path, legitimacy for each member
    (7, 4): [("ax", "PathD ==> IndivLegit /\\ ~Satisfaction"), ("ax", "DTogether"), ("ax", "WilliamsEach"), ("ax", "WilliamsQ3"),
             ("ax", "WilliamsQ3 ==> CostD"), ("thm", "(PathD ==> IndivLegit /\\ ~Satisfaction) /\\ DTogether /\\ WilliamsEach /\\ CostD")],
    # VI: the fifth path, authority without reasons
    (7, 5): [("ax", f"PathE ==> AcceptEach /\\ ({INTR})"), ("ax", "AcceptEach ==> Claim Ash"), ("ax", "~Corr Ash"),
             ("thm", "PathE ==> Claim Ash /\\ ~Reason Ash"), ("ax", "WilliamsJustified"), ("ax", "WilliamsWarfare"),
             ("ax", "WilliamsWarfare ==> CostE"), ("thm", "(PathE ==> Claim Ash /\\ ~Reason Ash) /\\ WilliamsJustified /\\ CostE")],
    # VI: the sixth path, no hard cases among the members
    (7, 6): [("ax", "PathF ==> ~HardMember"), ("ax", "WilliamsProlepsis"), ("ax", "WilliamsQ11"), ("ax", "WilliamsQ3"),
             ("ax", "WilliamsQ11 /\\ WilliamsQ3 ==> CostF"), ("thm", "(PathF ==> ~HardMember) /\\ WilliamsProlepsis /\\ CostF")],
    # VI: what each path gives up
    (7, 7): [("ax", EACH), ("thm", f"~(AcceptEach /\\ ({BRIDGE}) /\\ ({INTR}) /\\ (GoesBeyond /\\ MakesSense /\\ Member Ash) /\\ ~Corr Ash)"),
             ("ax", "FourHold"), ("ax", "PathA ==> ~AcceptEach"), ("ax", f"PathB ==> ~({INTR})"), ("ax", f"PathC ==> ~({INTAUTH})"),
             ("ax", "PathD ==> ~Satisfaction"), ("ax", f"PathE ==> ~({BRIDGE})"), ("ax", "PathF ==> ~HardMember"),
             ("ax", f"({DROPS}) ==> EveryPathPays"), ("ax", "OnlyA"), ("ax", "CostA"),
             ("thm", f"~(AcceptEach /\\ ({BRIDGE}) /\\ ({INTR}) /\\ (GoesBeyond /\\ MakesSense /\\ Member Ash) /\\ ~Corr Ash) /\\ FourHold /\\ ({DROPS}) /\\ EveryPathPays /\\ OnlyA /\\ CostA")],
    # VII: conclusion
    (8, 1): [("ax", "GroupInternal"), ("ax", f"WR ==> ({INTAUTH})"), ("ax", EXTMEM), ("ax", NOBOTH), ("ax", "SupportsBoth"),
             ("ax", "~WilliamsDecides"), ("ax", "FourHold"), ("ax", "EveryPathPays"), ("ax", "~WilliamsDecides /\\ EveryPathPays ==> Owes"),
             ("thm", "Owes"),
             ("thm", f"GroupInternal /\\ (WR ==> ({INTAUTH})) /\\ ({EXTMEM}) /\\ {NOBOTH} /\\ SupportsBoth /\\ ~WilliamsDecides /\\ FourHold /\\ EveryPathPays /\\ Owes")],
}


def source(k, j, stmts):
    used = [c for c in CONSTANTS if any(re.search(rf"\b{c}\b", s[1]) for s in stmts)]
    types = [t for t in ("person",) if any(t in CONSTANTS[c][0] for c in used)]
    out = ["open HolKernel Parse boolLib bossLib;", f'val _ = new_theory "dsp2_s{k}p{j}";', ""]
    out += [f'val _ = new_type ("{t}", 0);' for t in types]
    for c in used:
        out += [f"(* {CONSTANTS[c][1]} *)", f'val _ = new_constant ("{c}", ``{CONSTANTS[c][0]}``);']
    out.append("")
    names = []
    for i, (kind, term, *proof) in enumerate(stmts, 1):
        n = f"p{k}_{j}_{i:02d}"
        if kind == "ax":
            out.append(f'val {n} = new_axiom ("{n}", ``{term}``);')
        else:
            tac = proof[0].format(names=", ".join(names)) if proof else f"metis_tac [{', '.join(names)}]"
            out += ["", f"Theorem {n}:", f"  {term}", "Proof", f"  {tac}", "QED", ""]
        names.append(n)
    out += ["", "Theorem final:", f"  {stmts[-1][1]}", "Proof", f"  metis_tac [{', '.join(names)}]", "QED", "",
            "val _ = export_theory ();", ""]
    return "\n".join(out)


prose = ROOT / "prose"
for d in prose.glob("s*/p*"):
    if (int(d.parent.name[1:]), int(d.name[1:])) not in PARAS:
        shutil.rmtree(d)
for (k, j), stmts in PARAS.items():
    d = prose / f"s{k}" / f"p{j}"
    d.mkdir(parents=True, exist_ok=True)
    (d / "source.sml").write_text(source(k, j, stmts))
(prose / "quotes.json").write_text(json.dumps(QUOTES, indent=1, ensure_ascii=False))
print(f"wrote {len(PARAS)} paragraphs")

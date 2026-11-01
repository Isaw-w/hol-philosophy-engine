"""Write the round-3 message: where the cited response and the argument do not match, then the reflective-equilibrium
request. No model call. The list is generated from reply_citations.py's results; the request is fixed text.

  python3 tools/reply_check/equilibrium_message.py runs/DATE/REVIEW_RUN     # writes REVIEW_RUN/round3_message/message.txt
"""
import argparse, json
from pathlib import Path

REQUEST = ("Bring your argument and your response into reflective equilibrium. Go back and forth between them: where they "
           "conflict, sometimes revise the principles of the argument, sometimes withdraw a judgment in the response, until "
           "your principles and judgments coincide and you know which principles your judgments follow and from which "
           "premises. Return the complete argument in well-formed HOL4 in a single code block, then the complete response, "
           "citing the axioms and theorems after each sentence in the same way. Use stable symbol meanings and comments only "
           "for notation. If neither needs to change, return only no.")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("review")
    a = ap.parse_args()
    rv = Path(a.review)
    c = json.loads((rv / "citations/citations.json").read_text())
    rows = c["rows"]
    L = ["These are the places where your response and your argument do not match, found from the citations in your response.", ""]
    iso = [r for r in rows if any(k.startswith("isolated") for k in r["kinds"].values())]
    if iso:
        L.append("Sentences that cite axioms or definitions final does not use:")
        for r in iso:
            names = [n for n, k in r["kinds"].items() if k.startswith("isolated")]
            L.append(f'  "{r.get("span", r["sentence"])}" [{", ".join(names)}]')
    if c["missing"]:
        L.append("Items final rests on that no sentence cites: " + ", ".join(c["missing"]) + ".")
    marked = [r for r in rows if r["cites"] == ["none"]]
    if marked:
        L.append("Sentences you marked [none]:")
        L += [f'  "{r["sentence"]}"' for r in marked]
    if c["unknown"]:
        L.append("Cited names your argument does not have: " + ", ".join(c["unknown"]) + ".")
    L += ["", REQUEST]
    out = rv / "round3_message"; out.mkdir(exist_ok=True)
    (out / "message.txt").write_text("\n".join(L) + "\n")
    print("\n".join(L))


if __name__ == "__main__":
    main()

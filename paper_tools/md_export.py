"""Write an essay's full text as Markdown, from the same assembled files the PDF uses (prose/abstract.tex,
prose/body.tex) and its references.bib. Formatting only: no word of the text changes.

  python3 md_export.py ESSAY        # writes ESSAY/main.md
"""
import re, sys
from pathlib import Path

essay = Path(sys.argv[1]).resolve()
tex_main = (essay / "main.tex").read_text()
title = re.search(r"\\title\{(.*?)\}", tex_main)[1]
bib = (essay / "references.bib").read_text()

entries = {}
for m in re.finditer(r"@(\w+)\{(\w+),(.*?)\n\}", bib, re.S):
    f = dict((k.lower(), " ".join(v.split())) for k, v in re.findall(r"(\w+)\s*=\s*\{((?:[^{}]|\{[^{}]*\})*)\}", m[3]))
    f["type"] = m[1].lower()
    entries[m[2]] = f


def clean(s):
    s = re.sub(r"\{\\\\?'(\w)\}", lambda m: {"o": "ó", "e": "é", "a": "á"}.get(m[1], m[1]), s)
    return s.replace("{", "").replace("}", "").replace("--", "–")


def surnames(key):
    names = [n.split(",")[0].strip() for n in clean(entries[key]["author"]).split(" and ")]
    return names[0] if len(names) == 1 else (" and ".join(names) if len(names) == 2 else names[0] + " et al.")


cited = []
suffix = {}  # biblatex-style 2004a / 2004b for cited works with the same authors and year, ordered by title


def year(k):
    return entries[k]["year"] + suffix.get(k, "")


def cite(m):
    opts = re.findall(r"\[([^\]]*)\]", m[1] or "")
    pre, post = (opts + ["", ""])[:2] if len(opts) == 2 else ("", opts[0] if opts else "")
    keys = [k.strip() for k in m[2].split(",")]
    for k in keys:
        if k not in cited:
            cited.append(k)
    post = post.replace("\\S~", "§ ").replace("--", "–").replace("~", " ")
    if re.fullmatch(r"[\d–, ]+", post):
        post = ("pp. " if re.search(r"[–,]", post) else "p. ") + post
    elif re.match(r"\d+ ", post):
        post = "p. " + post
    parts = [f"{surnames(k)} {year(k)}" for k in keys]
    body = "; ".join(parts) + (f", {post}" if post else "")
    return f"{pre + ' ' if pre else ''}{body}"


def cites(m):
    groups = re.findall(r"((?:\[[^\]]*\])*)\{([^}]*)\}", m[1])
    return "(" + "; ".join(cite([None, o, k]) for o, k in groups) + ")"


def md(tex):
    t = re.sub(r"\\autocites((?:(?:\[[^\]]*\])*\{[^}]*\})+)", cites, tex)
    t = re.sub(r"\\autocite((?:\[[^\]]*\])*)\{([^}]*)\}", lambda m: f"({cite(m)})", t)
    t = re.sub(r"\\section\{(.*?)\}", r"## \1", t)
    def outer(m):
        return "“" + re.sub(r"\\enquote\{([^{}]*)\}", r"‘\1’", m[1]) + "”"
    t = re.sub(r"\\enquote\{((?:[^{}]|\{[^{}]*\})*)\}", outer, t)
    t = re.sub(r"\\textsc\{([^}]*)\}", lambda m: m[1].upper(), t)
    t = t.replace("---", "—").replace("$\\varphi$", "φ")
    t = re.sub(r"\$(\w)\$", r"*\1*", t)
    return t.strip()


md((essay / "prose/abstract.tex").read_text() + (essay / "prose/body.tex").read_text())
groups = {}
for k in cited:
    groups.setdefault((surnames(k), entries[k]["year"]), []).append(k)
for ks in groups.values():
    if len(ks) > 1:
        for i, k in enumerate(sorted(ks, key=lambda k: clean(entries[k]["title"]))):
            suffix[k] = "abcdefgh"[i]
cited.clear()
abstract = md((essay / "prose/abstract.tex").read_text())
body = md((essay / "prose/body.tex").read_text())

refs = []
for k in sorted(cited, key=lambda k: (surnames(k), year(k))):
    e = entries[k]
    a, y, ti = clean(e["author"]), year(k), clean(e["title"])
    if e["type"] == "article":
        where = f"*{clean(e['journal'])}* {e.get('volume', '')}"
        where += f"({e['number']})" if e.get("number") else ""
        where += f": {clean(e['pages'])}" if e.get("pages") else ""
        refs.append(f"- {a}. {y}. “{ti}.” {where}.")
    elif e["type"] == "incollection":
        refs.append(f"- {a}. {y}. “{ti}.” In *{clean(e['booktitle'])}*{' ' + e['volume'] if e.get('volume') else ''}, {clean(e.get('pages', ''))}. "
                    f"{clean(e.get('publisher', ''))}.")
    else:
        refs.append(f"- {a}. {y}. *{ti}*. {clean(e.get('publisher', ''))}.")

out = f"# {title}\n\n**Abstract.** {abstract}\n\n{body}\n\n## References\n\n" + "\n".join(refs) + "\n"
(essay / "main.md").write_text(out)
print(f"{essay / 'main.md'}: {len(out.split())} words in all, {len(refs)} references")

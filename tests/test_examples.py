"""Run holverify on the examples and compare each verdict with the expected one. Needs HOL4 on the configured host.

    python3 tests/test_examples.py                  # uses HOLVERIFY_HOST (default: mini)
    python3 tests/test_examples.py --host local
"""
import argparse, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from holverify.verify import verify  # noqa: E402

# example: (argument?, proved, consistent, minimal)
EXPECTED = {
    "valid_modus_ponens.sml":   (True,  True,  True,  True),
    "named_conclusion.sml":     (True,  True,  True,  True),
    "idle_premise.sml":         (False, True,  True,  False),
    "inconsistent_premises.sml": (False, True, False, None),
    "does_not_follow.sml":      (False, False, None,  None),
}


def main():
    import os
    ap = argparse.ArgumentParser()
    ap.add_argument("--host", default=os.environ.get("HOLVERIFY_HOST", "mini"))
    a = ap.parse_args()
    out = Path(tempfile.mkdtemp(prefix="holverify_test_"))
    failures = 0
    for name, (arg, proved, consistent, minimal) in EXPECTED.items():
        v, run = verify(ROOT / "examples" / name, out, a.host, "local", "final", 600, english=False)
        got = (v["argument"], v["proved"], v["consistent"], v["minimal"] if minimal is not None else None)
        want = (arg, proved, consistent, minimal)
        ok = got == want
        failures += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {name:28s} argument={v['argument']} proved={v['proved']} "
              f"consistent={v['consistent']} minimal={v['minimal']}" + ("" if ok else f"   expected {want}"))
    print(f"{len(EXPECTED) - failures} of {len(EXPECTED)} examples as expected; reports in {out}")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()

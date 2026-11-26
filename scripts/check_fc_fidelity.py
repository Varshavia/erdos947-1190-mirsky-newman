#!/usr/bin/env python3
"""Check that Challenge.lean reproduces the formal-conjectures (FC) text verbatim.

The FC files are read with `git show <PINNED_SHA>:<path>` from a local FC
clone, so the check uses the pinned commit whatever that clone has checked
out. The default clone is ../formal-conjectures next to this repository; use
--fc-repo or the FC_REPO environment variable to point elsewhere.

What is compared (each block lies between `-- BEGIN FC: <name>` and
`-- END FC: <name>` marker lines in Challenge.lean):

* "CoveringSystem definitions": FC CoveringSystem.lean after its
  `@[expose] public section` line, with only the lemma `iUnion_cosets` removed
  (no statement uses it). The same block in MirskyNewman/Defs.lean must also
  be byte-identical to the Challenge block (CRLF line endings are read as LF).
* "Erdos947": FC 947.lean after its `@[expose] public section` line.
* "Erdos1190": `namespace Erdos1190`, the docstring and statement of
  `erdos_1190.variants.lt_one`, and `end Erdos1190`.

Only these FC-specific lines are removed from the FC side:

* `set_option linter.style.formal_proof_palomar false in`
* `@[category ...]` attribute blocks, which may span several lines.

Normalisation: trailing whitespace is stripped, runs of blank lines are
collapsed to one, and blank lines at the start and end of a block are dropped.
Every removal and every FC line that is omitted is printed. The exit status is
nonzero if anything differs.
"""
from __future__ import annotations

import argparse
import difflib
import os
import re
import subprocess
import sys
from pathlib import Path

PINNED_SHA = "ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8"
FC_COVERING = "FormalConjecturesForMathlib/NumberTheory/CoveringSystem.lean"
FC_947 = "FormalConjectures/ErdosProblems/947.lean"
FC_1190 = "FormalConjectures/ErdosProblems/1190.lean"

ROOT = Path(__file__).resolve().parent.parent
SECTION_LINE = "@[expose] public section\n"
PALOMAR_SET_OPTION = re.compile(r"^set_option linter\.style\.formal_proof_palomar false in\n", re.M)
CATEGORY_ATTR = re.compile(r"^@\[category\b[^\]]*\]\n", re.M)
IUNION_COSETS = re.compile(
    r"^@\[simp\]\ntheorem iUnion_cosets .*?\n(?=\n|end CoveringSystem)", re.M | re.S
)


def fc_show(repo: Path, path: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(repo), "show", f"{PINNED_SHA}:{path}"],
        check=True, capture_output=True,
    )
    return result.stdout.decode("utf-8").replace("\r\n", "\n")


def after_section(text: str, path: str) -> str:
    index = text.find(SECTION_LINE)
    if index < 0:
        sys.exit(f"error: {path}: no `{SECTION_LINE.strip()}` line")
    return text[index + len(SECTION_LINE):]


def strip_fc_only(text: str, path: str, log: list[str]) -> str:
    for pattern, label in ((PALOMAR_SET_OPTION, "Palomar linter set_option"),
                           (CATEGORY_ATTR, "FC category/AMS attribute")):
        for match in pattern.finditer(text):
            log.append(f"  removed from {path} ({label}):\n"
                       + "".join(f"    | {line}\n" for line in match.group().rstrip("\n").split("\n")))
        text = pattern.sub("", text)
    return text


def normalise(text: str) -> list[str]:
    lines = [line.rstrip() for line in text.replace("\r\n", "\n").split("\n")]
    out: list[str] = []
    for line in lines:
        if line == "" and (not out or out[-1] == ""):
            continue
        out.append(line)
    while out and out[-1] == "":
        out.pop()
    return out


def marked_block(text: str, name: str, path: str) -> str:
    begin, end = f"-- BEGIN FC: {name}\n", f"-- END FC: {name}\n"
    if text.count(begin) != 1 or text.count(end) != 1:
        sys.exit(f"error: {path}: expected exactly one `{begin.strip()}` and `{end.strip()}`")
    return text[text.index(begin) + len(begin):text.index(end)]


def lt_one_declaration(text: str) -> str:
    """The docstring, attributes, and statement of `erdos_1190.variants.lt_one`, through `sorry`."""
    head = text.index("theorem erdos_1190.variants.lt_one ")
    doc = text.rindex("/--", 0, head)
    if text.find("-/", doc, head) < 0 or re.search(r"\ntheorem |\ndef ", text[doc:head]):
        sys.exit("error: could not find the lt_one docstring")
    finish = text.index("\n  sorry\n", head) + len("\n  sorry\n")
    return text[doc:finish]


def compare(name: str, expected: str, actual: str, fc_label: str) -> bool:
    exp, act = normalise(expected), normalise(actual)
    if exp == act:
        print(f"[OK]   {name}: Challenge matches {fc_label} ({len(act)} lines)")
        return True
    print(f"[DIFF] {name}: Challenge differs from {fc_label}")
    for line in difflib.unified_diff(exp, act, f"FC@{PINNED_SHA[:12]}:{fc_label}",
                                     f"Challenge.lean:{name}", lineterm=""):
        print("    " + line)
    return False


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--fc-repo", type=Path,
                        default=Path(os.environ.get("FC_REPO", ROOT.parent / "formal-conjectures")))
    args = parser.parse_args()
    repo = args.fc_repo.resolve()
    try:
        fc_cov, fc_947, fc_1190 = (fc_show(repo, p) for p in (FC_COVERING, FC_947, FC_1190))
    except (subprocess.CalledProcessError, FileNotFoundError) as error:
        detail = getattr(error, "stderr", b"") or b""
        sys.exit(f"error: cannot read FC {PINNED_SHA} from {repo}: {error} {detail.decode(errors='replace')}")
    print(f"FC clone {repo}, pinned commit {PINNED_SHA}\n")

    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    # Byte comparison after CRLF -> LF only: a Windows checkout with
    # core.autocrlf may turn LF into CRLF, but the committed blobs stay LF.
    defs_bytes = (ROOT / "MirskyNewman" / "Defs.lean").read_bytes().replace(b"\r\n", b"\n")
    log: list[str] = []
    ok = True

    # 1. Definitions.
    expected_cov = after_section(fc_cov, FC_COVERING)
    match = IUNION_COSETS.search(expected_cov)
    if match is None:
        sys.exit(f"error: {FC_COVERING}: lemma iUnion_cosets not found; review the omission rule")
    log.append(f"  omitted from {FC_COVERING} (unused lemma):\n"
               + "".join(f"    | {line}\n" for line in match.group().rstrip("\n").split("\n")))
    expected_cov = expected_cov[:match.start()] + expected_cov[match.end():]
    ok &= compare("CoveringSystem definitions", expected_cov,
                  marked_block(challenge, "CoveringSystem definitions", "Challenge.lean"), FC_COVERING)

    name = "CoveringSystem definitions"
    begin, end = f"-- BEGIN FC: {name}\n".encode(), f"-- END FC: {name}\n".encode()
    challenge_bytes = (ROOT / "Challenge.lean").read_bytes().replace(b"\r\n", b"\n")
    cb = challenge_bytes[challenge_bytes.index(begin):challenge_bytes.index(end) + len(end)]
    if defs_bytes.count(begin) == 1 and defs_bytes.count(end) == 1:
        db = defs_bytes[defs_bytes.index(begin):defs_bytes.index(end) + len(end)]
    else:
        db = b""
    if cb == db:
        print(f"[OK]   {name}: MirskyNewman/Defs.lean block is byte-identical to Challenge.lean ({len(cb)} bytes)")
    else:
        ok = False
        print(f"[DIFF] {name}: MirskyNewman/Defs.lean block is not byte-identical to Challenge.lean")
        for line in difflib.unified_diff(cb.decode().split("\n"), db.decode().split("\n"),
                                         "Challenge.lean", "MirskyNewman/Defs.lean", lineterm=""):
            print("    " + line)

    # 2. Erdos 947.
    expected_947 = strip_fc_only(after_section(fc_947, FC_947), FC_947, log)
    ok &= compare("Erdos947", expected_947, marked_block(challenge, "Erdos947", "Challenge.lean"), FC_947)

    # 3. Erdos 1190, lt_one variant only.
    body_1190 = after_section(fc_1190, FC_1190)
    decl = strip_fc_only(lt_one_declaration(body_1190), FC_1190, log)
    expected_1190 = f"namespace Erdos1190\n\n{decl}\nend Erdos1190\n"
    if "namespace Erdos1190\n" not in body_1190 or "end Erdos1190\n" not in body_1190:
        sys.exit(f"error: {FC_1190}: namespace Erdos1190 not found")
    omitted = [line for line in body_1190[:body_1190.index("namespace Erdos1190\n")].split("\n") if line.strip()]
    log.append(f"  omitted from {FC_1190} (context before `namespace Erdos1190`):\n"
               + "".join(f"    | {line}\n" for line in omitted))
    others = re.findall(r"^(?:noncomputable )?(?:theorem|def|lemma) (\S+)", body_1190, re.M)
    log.append(f"  omitted from {FC_1190} (other declarations): "
               + ", ".join(o for o in others if o != "erdos_1190.variants.lt_one") + "\n")
    ok &= compare("Erdos1190", expected_1190, marked_block(challenge, "Erdos1190", "Challenge.lean"), FC_1190)

    print("\nFC text removed or omitted on the FC side:")
    print("".join(log), end="")
    print("\nRESULT:", "verbatim match" if ok else "MISMATCH")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

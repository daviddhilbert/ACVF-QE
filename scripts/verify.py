#!/usr/bin/env python3
"""Check the local QE proof against the standalone ACVF QE package.

Run with the pinned Lean on PATH and Mathlib's package paths in LEAN_PATH:
    python3 scripts/verify.py

This does not use the repository's machine-specific Lake configuration.
All generated sources, oleans, and logs are confined to .scratch/local-qe-check.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FOCUSED = os.environ.get("LOCAL_QE_FOCUSED") == "1"
BUILD = ROOT / ".scratch" / ("local-qe-check-focused" if FOCUSED else "local-qe-check")
SRC, LIB, LOG = (BUILD / name for name in ("src", "lib", "logs"))
for directory in (SRC, LIB, LOG):
    directory.mkdir(parents=True, exist_ok=True)
(BUILD / "status.txt").write_text("RUNNING\n", encoding="utf-8")

sources = {p.stem: p for p in (ROOT / "Proofs").glob("*.lean")}

texts = {name: path.read_text(encoding="utf-8-sig") for name, path in sources.items()}
if FOCUSED:
    imports = ["ModelTheory.Definability", "ModelTheory.Complexity", "ModelTheory.Substructures",
               "ModelTheory.Bundled", "RingTheory.Valuation.ValuationSubring",
               "GroupTheory.QuotientGroup.Basic", "Tactic.FinCases", "Tactic.Ring"]
    texts["Enc"] = re.sub(r"^import Mathlib$", "\n".join("import Mathlib." + p for p in imports),
                          texts["Enc"], flags=re.M)
    texts["VFField"] = "import Mathlib.Algebra.Field.MinimalAxioms\n" + texts["VFField"]
    texts["VFValued"] = "import Mathlib.RingTheory.Valuation.ValuativeRel.Basic\n" + texts["VFValued"]
dependencies = {
    name: [dep for dep in re.findall(r"^(?:public\s+)?import\s+(\S+)", text, re.M) if dep in sources]
    for name, text in texts.items()
}
ordered, active = [], set()
def visit(name):
    if name in ordered:
        return
    if name in active:
        raise RuntimeError("Cyclic imports at " + name)
    active.add(name)
    for dep in dependencies[name]:
        visit(dep)
    active.remove(name)
    ordered.append(name)
targets = os.environ.get("LOCAL_QE_TARGETS", "").split(",")
for name in (targets if targets != [""] else sorted(sources)):
    visit(name)

version = subprocess.check_output(["lean", "--version"], text=True).strip()
if "4.35.0" not in version:
    raise RuntimeError("Expected the repository's pinned Lean 4.35.0: " + version)
env = os.environ.copy()
env["LEAN_PATH"] = str(LIB) + os.pathsep + env.get("LEAN_PATH", "")
manifest_path = BUILD / "manifest.json"
manifest = json.loads(manifest_path.read_text()) if manifest_path.exists() else {}
fingerprints = {}
report = []
for name in ordered:
    text = texts[name]
    fingerprint = hashlib.sha256((version + text + "".join(
        fingerprints[dep] for dep in dependencies[name])).encode()).hexdigest()
    fingerprints[name] = fingerprint
    source, olean, log = SRC / (name + ".lean"), LIB / (name + ".olean"), LOG / (name + ".log")
    source.write_text(text, encoding="utf-8")
    cached = manifest.get(name) == fingerprint and olean.exists() and log.exists()
    if cached:
        result = 0
    else:
        with log.open("w", encoding="utf-8") as stream:
            result = subprocess.run(["lean", "-R", str(SRC), "-o", str(olean), str(source)],
                                    env=env, stdout=stream, stderr=subprocess.STDOUT).returncode
    output = log.read_text(encoding="utf-8")
    bad_axioms = [a.strip() for block in re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
                  for a in block.split(",") if a.strip() not in
                  {"", "propext", "Classical.choice", "choice", "Quot.sound"}]
    failed = result != 0 or bool(re.search(r"\berror\b", output)) or bool(bad_axioms)
    report.append(f"{name}\t{result}\t{'FAIL' if failed else 'PASS'}\t{'cached' if cached else 'checked'}")
    (BUILD / "results.tsv").write_text("\n".join(report) + "\n", encoding="utf-8")
    print(report[-1], flush=True)
    if failed:
        print(output, file=sys.stderr)
        (BUILD / "status.txt").write_text("1\n", encoding="utf-8")
        sys.exit(1)
    manifest[name] = fingerprint
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")

# Import everything together to detect namespace and dependency collisions.
combined = SRC / "CombinedLocalQE.lean"
headlines = {
    "Theorem23": (
        "JohnsonACF.hasQEb",
        "hasQE_ACVF_val",
        "hasQEb_ACVF_val",
        "ProvedResidueClosure.provedResidueClosure",
        "ProvedACFExtension.markerACFSaturatedEmbeddingExtension",
        "JohnsonValuedExtension.markerNotesProposition45",
        "CountableSaturatedExtension.exists_saturated_elementary_extension",
        "CountableQECriterion.fullQE_of_saturatedExtension",
        "SpecialTransformations.Milestone0.theorem_2_3_quantifier_elimination",
    ),
    "TrivialValuedQE": ("ValPM.hasQE_ACVF_trivial_val", "ValPM.hasQEb_ACVF_trivial_val"),
    "TrivialRVQE": ("SpecialTransformations.TrivialRV.canonical_trivial_rv_qe",),
    "TrivialRVTheory": ("SpecialTransformations.TrivialRV.hasQE",),
}
expected_audits = {name for module, names in headlines.items() if module in ordered for name in names}
audit = "set_option pp.explicit true\nset_option pp.fullNames true\n" + "".join(
    f"#check @{name}\n#print axioms {name}\n" for name in sorted(expected_audits))
combined.write_text("".join("import " + name + "\n" for name in ordered) + audit,
                    encoding="utf-8")
with (LOG / "CombinedLocalQE.log").open("w", encoding="utf-8") as stream:
    result = subprocess.run(["lean", "-R", str(SRC), str(combined)], env=env,
                            stdout=stream, stderr=subprocess.STDOUT).returncode
output = (LOG / "CombinedLocalQE.log").read_text(encoding="utf-8")
audits = re.findall(r"'([^'\n]+)' depends on axioms:\s*\[([^]]*)\]", output)
audits += [(name, "") for name in re.findall(r"'([^'\n]+)' does not depend on any axioms", output)]
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad_axioms = {a.strip() for _, block in audits for a in block.split(",") if a.strip()} - allowed
coverage_ok = len(audits) == len(expected_audits) and {name for name, _ in audits} == expected_audits
failed = result != 0 or bool(re.search(r"\berror\b", output)) or bool(bad_axioms) or not coverage_ok
if not coverage_ok:
    print("Incomplete combined QE headline audit", file=sys.stderr)
if bad_axioms:
    print(f"Unexpected combined QE axioms: {sorted(bad_axioms)}", file=sys.stderr)
status = result if result != 0 else int(failed)
(BUILD / "status.txt").write_text(str(status) + "\n", encoding="utf-8")
if failed:
    print(output, file=sys.stderr)
sys.exit(status)

#!/usr/bin/env python3
"""Audit all local OddMath modules and their private/generated declarations.
Run `lake --wfail build` first. No dependency updates or library-source changes.
Some standalone audit files define colliding root-level local-instance names;
therefore audit the umbrella, then each uncovered module in its own environment.
Evidence and generated import drivers are retained in .verification/axioms/.
"""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import csv
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".verification" / "axioms"
FLAGS = ["-DwarningAsError=true", "-Dbackward.isDefEq.respectTransparency=false",
         "-Dbackward.isDefEq.respectTransparency.types=false"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def inventory() -> dict[str, str]:
    files = [ROOT / "OddMath.lean", *sorted((ROOT / "OddMath").rglob("*.lean")),
             ROOT / "lean-toolchain", ROOT / "lakefile.lean", ROOT / "lake-manifest.json",
             ROOT / "scripts" / "AxiomAudit.lean", Path(__file__)]
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}


def audit(module: str) -> tuple[dict, set[str], list[dict]]:
    prefix = OUT / module
    body = (ROOT / "scripts" / "AxiomAudit.lean").read_text()
    if not body.startswith("import OddMath\n"):
        raise RuntimeError("Unexpected audit template header")
    # Append extensions rather than replacing the final component of a module name.
    driver = Path(str(prefix) + ".lean")
    tsv, module_file, log_file = [Path(str(prefix) + suffix)
                                  for suffix in (".tsv", ".modules", ".log")]
    driver.write_text(f"import {module}\n" + body.removeprefix("import OddMath\n"))
    env = dict(os.environ, ODD_AXIOM_AUDIT_TSV=str(tsv), ODD_AXIOM_AUDIT_MODULES=str(module_file))
    env.pop("ODD_AXIOM_AUDIT_MODULE_COUNT", None)
    command = ["lake", "env", "lean", *FLAGS, str(driver.relative_to(ROOT))]
    with log_file.open("w") as log:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
    receipt = {"module": module, "command": command, "exit_code": result.returncode}
    if result.returncode:
        print(log_file.read_text()[-12000:], file=sys.stderr)
        return receipt, set(), []
    imported = set(module_file.read_text().splitlines())
    if module not in imported:
        raise RuntimeError(f"Requested module absent from environment: {module}")
    with tsv.open() as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    if not rows or len({r["declaration"] for r in rows}) != len(rows):
        raise RuntimeError(f"Empty or duplicated declaration audit: {module}")
    return receipt, imported, rows


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    before = inventory()
    modules = {str(Path(f).with_suffix("")).replace("/", ".")
               for f in before if f == "OddMath.lean" or f.startswith("OddMath/")}
    first = audit("OddMath")
    results = [first]
    if first[0]["exit_code"] == 0:
        uncovered = sorted(modules - first[1])
        with ThreadPoolExecutor(max_workers=2) as pool:
            results.extend(pool.map(audit, uncovered))
    covered = set().union(*(r[1] for r in results))
    unique = {}
    for _, _, rows in results:
        for row in rows:
            key = (row["module"], row["declaration"])
            row["axioms"] = ",".join(sorted(filter(None, row["axioms"].split(","))))
            if key in unique and unique[key] != row:
                raise RuntimeError(f"Inconsistent duplicate declaration: {key}")
            unique[key] = row
    rows = [unique[key] for key in sorted(unique)]
    axioms = sorted({a for row in rows for a in row["axioms"].split(",") if a})
    after = inventory()
    passed = (all(r[0]["exit_code"] == 0 for r in results) and covered == modules
              and before == after and not (set(axioms) - ALLOWED) and bool(rows))
    report = {"passed": passed, "module_count": len(modules), "modules": sorted(modules),
              "covered_modules": sorted(covered), "missing_modules": sorted(modules - covered),
              "unexpected_modules": sorted(covered - modules), "source_sha256": before,
              "sources_unchanged": before == after, "allowed_axioms": sorted(ALLOWED),
              "observed_axioms": axioms, "declaration_count": len(rows),
              "private_count": sum(r["declaration"].startswith("_private.") for r in rows),
              "foreign_namespace_count": sum(not r["declaration"].startswith(("OddMath.", "_private."))
                                             for r in rows),
              "audit_environment_count": len(results), "runs": [r[0] for r in results]}
    with (OUT / "declarations.tsv").open("w") as stream:
        writer = csv.DictWriter(stream, fieldnames=["module", "declaration", "axioms"],
                                delimiter="\t", lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    (OUT / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ("modules", "covered_modules", "source_sha256", "runs")}, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())

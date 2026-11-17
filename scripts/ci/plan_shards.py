#!/usr/bin/env python3
"""Plan a sharded build for CI.

Reads the import graph of `OddMath` and of the non-vacuity checks, determines which modules a
change can force to recompile (the changed modules and everything that imports them), and, when
that set is large, splits its first part into shards that independent runners build in parallel.

Each module is weighted equally (measured build times of single modules hardly correlate with
file size, and equal weights schedule almost as well as measured times). Module `m` gets the
weight of the heaviest import chain ending at `m` within the rebuild set; the modules whose chain
weight is at most `FRACTION` of the longest chain form the first stage. The first stage is cut
into `SHARDS` parts: every top module of the stage, with the part of its imports inside the
stage, goes to the part where it adds the least weight. A runner builds its part; the final job
collects all parts and builds the remaining modules, which form a few long import chains.

Usage: plan_shards.py BASE OUT.json
  BASE  a commit to diff against, or `all` to plan a cold build.
Writes OUT.json ({"sharded": bool, "shards": [[module, ...], ...], ...}) and, when
GITHUB_OUTPUT is set, the outputs `sharded` and `shards` (a JSON list of shard indices).
"""

import json
import os
import re
import subprocess
import sys

SHARDS = 8
FRACTION = 0.8
# Below this many modules to rebuild a single runner is as fast as a sharded build.
MIN_MODULES = 400

IMPORT = re.compile(r"^\s*(?:public\s+)?import\s+(\S+)", re.M)


def modules():
    """Map each local module name to its source path."""
    out = {}
    roots = [("OddMath", "."), ("NonVacuity", "scripts")]
    for lib, src in roots:
        top = os.path.join(src, lib + ".lean")
        if os.path.exists(top):
            out[lib] = top
        for dirpath, _, files in os.walk(os.path.join(src, lib)):
            for name in files:
                if name.endswith(".lean"):
                    path = os.path.join(dirpath, name)
                    rel = os.path.relpath(path, src)[: -len(".lean")]
                    out[rel.replace(os.sep, ".")] = path
    return out


def changed_paths(base):
    diff = subprocess.run(["git", "diff", "--name-only", base, "HEAD"],
                          capture_output=True, text=True, check=True).stdout
    return [p for p in diff.splitlines() if p]


def main():
    base, out_path = sys.argv[1], sys.argv[2]
    mods = modules()
    deps = {}
    for m, path in mods.items():
        with open(path, encoding="utf-8") as f:
            deps[m] = [d for d in IMPORT.findall(f.read()) if d in mods and d != m]
    users = {m: [] for m in mods}
    for m, ds in deps.items():
        for d in ds:
            users[d].append(m)

    cold = base == "all"
    if not cold:
        paths = changed_paths(base)
        cold = any(p in ("lakefile.lean", "lake-manifest.json", "lean-toolchain") for p in paths)
    if cold:
        rebuild = set(mods)
    else:
        by_path = {os.path.normpath(p): m for m, p in mods.items()}
        stack = [by_path[os.path.normpath(p)] for p in paths if os.path.normpath(p) in by_path]
        rebuild = set()
        while stack:
            m = stack.pop()
            if m not in rebuild:
                rebuild.add(m)
                stack.extend(users[m])

    plan = {"sharded": False, "rebuild": len(rebuild), "shards": []}
    if len(rebuild) >= MIN_MODULES:
        # Topological order of the rebuild set.
        indeg = {m: sum(d in rebuild for d in deps[m]) for m in rebuild}
        order = [m for m in rebuild if indeg[m] == 0]
        for m in order:
            for u in users[m]:
                if u in rebuild:
                    indeg[u] -= 1
                    if indeg[u] == 0:
                        order.append(u)
        chain = {}
        for m in order:
            chain[m] = 1 + max((chain[d] for d in deps[m] if d in rebuild), default=0)
        cut = FRACTION * max(chain.values())
        stage = {m for m in rebuild if chain[m] <= cut}

        def inside(m):
            seen, todo = set(), [m]
            while todo:
                x = todo.pop()
                if x in stage and x not in seen:
                    seen.add(x)
                    todo.extend(deps[x])
            return seen

        tops = sorted((m for m in stage if not any(u in stage for u in users[m])))
        closures = {m: inside(m) for m in tops}
        tops.sort(key=lambda m: (-len(closures[m]), m))
        parts = [set() for _ in range(SHARDS)]
        for m in tops:
            best = min(range(SHARDS),
                       key=lambda i: (len(parts[i] | closures[m]), -len(parts[i] & closures[m]), i))
            parts[best] |= closures[m]
        plan["sharded"] = True
        plan["stage"] = len(stage)
        plan["shards"] = [sorted(p) for p in parts if p]

    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(plan, f, indent=0)
    sizes = [len(p) for p in plan["shards"]]
    print(f"{plan['rebuild']} modules to rebuild; sharded: {plan['sharded']}; shard sizes: {sizes}")
    gh_out = os.environ.get("GITHUB_OUTPUT")
    if gh_out:
        with open(gh_out, "a", encoding="utf-8") as f:
            f.write(f"sharded={'true' if plan['sharded'] else 'false'}\n")
            f.write(f"shards={json.dumps(list(range(len(plan['shards']))))}\n")


if __name__ == "__main__":
    main()

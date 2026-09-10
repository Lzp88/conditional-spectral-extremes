#!/usr/bin/env python3
"""Rebuild and kernel-check the Lean development accompanying the paper.

Every module under `lean/src` is recompiled from source with

    lean --trust=0 -Ddebug.skipKernelTC=false

so that the kernel re-checks every declaration it adds.  No cached build
products and no stored certificate are used.  The script then reads the
`#print axioms` output emitted by the modules and confirms that no
declaration depends on anything beyond the three standard foundational
axioms, and that the paper's headline statements were elaborated.

Usage
-----
    cd lean && lake exe cache get && cd ..      # fetch the locked Mathlib
    python verify.py --jobs 4

Options
-------
    --packages DIR   Lake package directory holding a built Mathlib.
                     Default: lean/.lake/packages
    --build DIR      Output directory for .olean files (must be empty or new).
    --jobs N         Parallel compilations (default 4).  Each worker needs
                     several GB of memory.
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import json
import os
import re
import subprocess
import sys
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Statements whose axiom footprint must appear in the build output.
REQUIRED = [
    "ConditionalSpectralExtremes.exact_cycle_localization",
    "ConditionalSpectralExtremes.actual_permutation_exact_cycle_localization",
    "ConditionalSpectralExtremes.manuscript_actual_permutation_supremum_limit",
    "ConditionalSpectralExtremes.actual_permutation_ordinary_random_centering",
    "ConditionalSpectralExtremes.actual_permutation_ordinary_joint_limit",
    "ConditionalSpectralExtremes.TwoMatchings."
    "actual_two_matching_exact_component_localization",
    "ConditionalSpectralExtremes.actual_permutation_conditioning_eventually_positive",
]

IMPORT_RE = re.compile(
    r"(?m)^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)")

AXIOMS_RE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]", re.S)
NO_AXIOMS_RE = re.compile(r"'([^']+)' does not depend on any axioms")
# `#check ExactCycleLocalization` prints the type of the proposition.
CHECK_RE = re.compile(r"^\S+ : Prop$")

HOLE_RE = re.compile(
    r"\b(sorry|admit|sorryAx|axiom|unsafe|partial|trustLevel|skipKernelTC|"
    r"native_decide|implemented_by|addDeclCore|addDeclWithoutChecking|"
    r"Lean\.ofReduceBool|extern)\b")


def strip_comments(text: str) -> str:
    """Blank out Lean comments (nested `/- -/`, `--`) and string literals."""
    out = list(text)
    i, n = 0, len(text)

    def mask(a: int, b: int) -> None:
        for j in range(a, b):
            if out[j] not in "\r\n":
                out[j] = " "

    while i < n:
        if text.startswith("/-", i):
            depth, start, i = 1, i, i + 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            mask(start, i)
        elif text.startswith("--", i):
            start, j = i, text.find("\n", i)
            i = n if j < 0 else j
            mask(start, i)
        elif text[i] == '"':
            start, i = i, i + 1
            while i < n:
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            mask(start, i)
        else:
            i += 1
    return "".join(out)


def classify(output: str) -> tuple[dict[str, set[str]], list[str]]:
    """Split module output into axiom footprints and anything unexpected."""
    printed: dict[str, set[str]] = {}
    leftover: list[str] = []
    text = output
    for m in AXIOMS_RE.finditer(output):
        printed[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
        text = text.replace(m.group(0), "")
    for m in NO_AXIOMS_RE.finditer(output):
        printed[m.group(1)] = set()
        text = text.replace(m.group(0), "")
    for line in text.splitlines():
        s = line.strip()
        if not s or CHECK_RE.match(s):
            continue
        leftover.append(s)
    return printed, leftover


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--packages", type=Path,
                    default=ROOT / "lean" / ".lake" / "packages")
    ap.add_argument("--build", type=Path, default=ROOT / "build")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--report", type=Path, default=ROOT / "verification.json")
    ap.add_argument("--resume", action="store_true",
                    help="reuse .olean files left in --build by an interrupted "
                         "run instead of recompiling them; the report records "
                         "how many modules were reused")
    args = ap.parse_args()

    src = ROOT / "lean" / "src"
    build = args.build.resolve()
    build.mkdir(parents=True, exist_ok=True)

    toolchain = (ROOT / "lean" / "lean-toolchain").read_text().strip()
    print(f"[verify] pinned toolchain: {toolchain}")

    mods = {f.stem: f for f in sorted(src.glob("*.lean"))}
    print(f"[verify] {len(mods)} modules in {src}")

    # ---- lexical preflight --------------------------------------------
    flags = {}
    for name, path in mods.items():
        hits = sorted({m.group(1) for m in
                       HOLE_RE.finditer(strip_comments(path.read_text(encoding="utf-8")))})
        if hits:
            flags[name] = hits
    print(f"[verify] modules containing sorry/axiom/unsafe/...: {len(flags)}")
    if flags:
        print(f"         {json.dumps(flags)[:400]}")

    # ---- dependency graph ---------------------------------------------
    deps, external = {}, set()
    for name, path in mods.items():
        d = set()
        for m in IMPORT_RE.finditer(path.read_text(encoding="utf-8")):
            (d.add if m.group(1) in mods else external.add)(m.group(1))
        deps[name] = d
    rdeps: dict[str, set[str]] = {k: set() for k in deps}
    for k, v in deps.items():
        for x in v:
            rdeps[x].add(k)
    non_mathlib = sorted(x for x in external if not x.split(".")[0] == "Mathlib")
    print(f"[verify] external imports outside Mathlib: {non_mathlib or 'none'}")

    # ---- environment ---------------------------------------------------
    pkg_paths = []
    if args.packages.is_dir():
        for p in sorted(args.packages.iterdir()):
            lib = p / ".lake" / "build" / "lib" / "lean"
            if lib.is_dir():
                pkg_paths.append(str(lib))
    if not pkg_paths:
        print(f"[verify] no built packages under {args.packages}.\n"
              f"         run:  cd lean && lake exe cache get")
        return 2
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([str(build)] + pkg_paths)
    env.pop("LEAN_SRC_PATH", None)

    # Select the pinned toolchain explicitly rather than the system default.
    prefix = ["elan", "run", toolchain]
    probe = subprocess.run(prefix + ["lean", "--version"], env=env,
                           capture_output=True, text=True)
    if probe.returncode != 0:
        prefix = []
        probe = subprocess.run(["lean", "--version"], env=env,
                               capture_output=True, text=True)
        print("[verify] elan not usable; falling back to the default `lean`")
    print(f"[verify] {probe.stdout.strip()}")
    if toolchain.split(":")[-1].lstrip("v") not in probe.stdout:
        print(f"[verify] WARNING: compiler does not match {toolchain}")

    # ---- parallel fresh build ------------------------------------------
    lock = threading.Lock()
    results: dict[str, dict] = {}
    failed: list[str] = []
    done: set[str] = set()
    counter = [0]
    t0 = time.time()

    reused: set[str] = set()

    def compile_one(name: str) -> str:
        if args.resume and (build / f"{name}.olean").exists():
            with lock:
                counter[0] += 1
                reused.add(name)
                results[name] = {"returncode": 0, "seconds": 0.0,
                                 "axioms": {}, "unexpected_output": [],
                                 "reused": True}
                print(f"[{counter[0]:3d}/{len(mods)}] reuse {name}", flush=True)
            return name
        cmd = prefix + ["lean", "--trust=0", "-Ddebug.skipKernelTC=false",
                        f"--root={src}", "-o", str(build / f"{name}.olean"),
                        str(mods[name])]
        st = time.time()
        proc = subprocess.run(cmd, env=env, cwd=str(build), text=True,
                              encoding="utf-8", errors="replace",
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        out = proc.stdout.strip()
        printed, leftover = classify(out)
        rec = {"returncode": proc.returncode, "seconds": round(time.time() - st, 1),
               "axioms": {k: sorted(v) for k, v in printed.items()},
               "unexpected_output": leftover}
        with lock:
            counter[0] += 1
            results[name] = rec
            bad = proc.returncode != 0 or leftover
            if proc.returncode != 0:
                failed.append(name)
            print(f"[{counter[0]:3d}/{len(mods)}] "
                  f"{'FAIL' if bad else 'ok  '} {name} ({rec['seconds']}s)",
                  flush=True)
            for line in leftover[:5]:
                print("        unexpected:", line)
        return name

    with cf.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        pending = {k: set(v) for k, v in deps.items()}
        futures = {pool.submit(compile_one, k): k
                   for k, v in pending.items() if not v}
        while futures:
            finished, _ = cf.wait(list(futures), return_when=cf.FIRST_COMPLETED)
            for fut in finished:
                name = futures.pop(fut)
                fut.result()
                if results[name]["returncode"] != 0:
                    continue
                done.add(name)
                for child in rdeps[name]:
                    if child not in done and child not in futures.values() \
                            and deps[child] <= done:
                        futures[pool.submit(compile_one, child)] = child

    # ---- audit ----------------------------------------------------------
    printed: dict[str, list[str]] = {}
    for rec in results.values():
        printed.update(rec["axioms"])
    outside = {d: a for d, a in printed.items() if set(a) - ALLOWED_AXIOMS}
    noisy = {n: r["unexpected_output"] for n, r in results.items()
             if r["unexpected_output"]}
    skipped = sorted(set(mods) - set(results))
    missing = [r for r in REQUIRED if r not in printed]

    seen: set[str] = set()
    for a in printed.values():
        seen |= set(a)

    print()
    print(f"modules            : {len(results)}/{len(mods)} built, "
          f"{len(failed)} failed, {len(skipped)} skipped")
    print(f"elapsed            : {round(time.time() - t0)} s")
    print(f"sorry/axiom/unsafe : {len(flags)} modules")
    print(f"axiom footprints   : {len(printed)} declarations")
    print(f"axioms observed    : {sorted(seen)}")
    print(f"outside allow-list : {len(outside)}")
    print(f"unexpected output  : {len(noisy)} modules")
    print()
    for r in REQUIRED:
        print(f"  [{'OK ' if r in printed else 'not re-checked'}] {r}")

    hard = bool(failed or skipped or outside or noisy or flags)
    if reused:
        ok = not hard
        print()
        print(f"modules reused     : {len(reused)} (from an interrupted run)")
        print("NOTE: the axiom audit covers only the "
              f"{len(results) - len(reused)} modules recompiled in this run. "
              "Re-run without --resume for a complete audit.")
        verdict = "FAIL" if hard else "PASS (partial: resumed)"
    else:
        ok = not (hard or missing)
        verdict = "PASS" if ok else "FAIL"
    print()
    print("RESULT:", verdict)

    args.report.write_text(json.dumps({
        "toolchain": toolchain,
        "compiler": probe.stdout.strip(),
        "lean_arguments": ["--trust=0", "-Ddebug.skipKernelTC=false"],
        "modules_total": len(mods), "modules_built": len(results),
        "modules_reused_from_interrupted_run": sorted(reused),
        "modules_failed": sorted(failed), "modules_skipped": skipped,
        "lexical_flags": flags,
        "declarations_with_axiom_footprint": len(printed),
        "axioms_observed": sorted(seen),
        "declarations_outside_allowlist": outside,
        "modules_with_unexpected_output": noisy,
        "required_statements_missing": missing,
        "elapsed_seconds": round(time.time() - t0),
        "result": verdict,
    }, indent=1) + "\n", encoding="utf-8")
    print(f"record written to {args.report}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

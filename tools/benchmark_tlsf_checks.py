#!/usr/bin/env python3
"""Compare fresh-process TLSF verification with individual conditional checks.

Builds once, then runs the same executable sequentially. Wall time includes
runtime startup but excludes compilation. CLI phase timers separate the checked
base, TLSF setup, and selected proof. No timing threshold determines success.
"""

import argparse
import datetime
import hashlib
import json
import platform
import resource
import statistics
import subprocess
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def output(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def json_lines(text):
    # HOL tactics may print diagnostics in addition to the command's JSON.
    return [json.loads(line) for line in text.splitlines() if line.startswith("{")]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", choices=["wasm-gc", "native"], default="wasm-gc")
    parser.add_argument("--release", action="store_true")
    parser.add_argument("--repeat", type=int, default=1)
    parser.add_argument("--lemma", action="append", dest="lemmas")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.repeat < 1:
        parser.error("--repeat must be positive")
    lemmas = args.lemmas or ["tlsf_exp_le", "tlsf_find_sound", "tlsf_full_malloc_run"]
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    wanted = 65520 * 1024
    desired = wanted if hard == resource.RLIM_INFINITY else min(wanted, hard)
    if soft < desired:
        try:
            resource.setrlimit(resource.RLIMIT_STACK, (desired, hard))
        except (OSError, ValueError):
            # Managed hosts may forbid even a soft-limit change. Use the
            # existing limit, which suffices for nonrecursive program defs.
            pass
    build = ["moon", "build", "cmd/tlsf", "--target", args.target, "--output-json"]
    if args.release:
        build.append("--release")
    built = subprocess.run(build, cwd=ROOT, text=True, capture_output=True, check=True)
    artifacts = [r for r in json_lines(built.stdout) if r.get("$message_type") == "artifact"]
    artifact = Path(next(r["path"] for r in artifacts if r["package"].endswith("/cmd/tlsf")))
    command = ["moonrun", str(artifact), "--"] if args.target == "wasm-gc" else [str(artifact)]
    report = {
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "target": args.target,
        "mode": "release" if args.release else "debug",
        "stack_limits_bytes": list(resource.getrlimit(resource.RLIMIT_STACK)),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "source_head": output("git", "rev-parse", "HEAD"),
        "hol_head": output("git", "-C", "../hol-light.mbt", "rev-parse", "HEAD"),
        "moon": output("moon", "version"),
        "moonrun": output("moonrun", "--version"),
        "moonc": output("moonc", "-v"),
        "artifact_sha256": hashlib.sha256(artifact.read_bytes()).hexdigest(),
        "runs": [],
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)

    def save():
        args.out.write_text(json.dumps(report, indent=2) + "\n")

    for repeat in range(args.repeat):
        for selection in [["verify"], *[["check", lemma] for lemma in lemmas]]:
            print(f"Run {repeat + 1}: {' '.join(selection)}", flush=True)
            start = time.perf_counter()
            result = subprocess.run(command + selection, cwd=ROOT, text=True, capture_output=True)
            wall = time.perf_counter() - start
            rows = json_lines(result.stdout)
            expected = "VERIFIED" if selection == ["verify"] else "CONDITIONAL PASS"
            if result.returncode or not any(r.get("status") == expected for r in rows):
                raise RuntimeError(f"Failed {selection}:\n{result.stdout}\n{result.stderr}")
            report["runs"].append({
                "repeat": repeat + 1, "selection": selection,
                "wall_seconds": wall, "events": rows,
            })
            save()
            print(f"  {wall:.3f}s", flush=True)
    full = statistics.median(r["wall_seconds"] for r in report["runs"] if r["selection"] == ["verify"])
    report["summary"] = {"full_median_seconds": full, "lemmas": {}}
    for lemma in lemmas:
        seconds = statistics.median(
            r["wall_seconds"] for r in report["runs"] if r["selection"] == ["check", lemma]
        )
        report["summary"]["lemmas"][lemma] = {
            "cold_median_seconds": seconds, "speedup": full / seconds,
        }
    save()
    print(json.dumps(report["summary"], indent=2))


if __name__ == "__main__":
    main()

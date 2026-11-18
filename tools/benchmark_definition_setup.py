"""Compare two frozen wasm-gc TLSF executables in fresh, sequential processes.

Build and copy the baseline before editing, then build and copy the candidate
in the same mode. Compilation is excluded. Alternate order between repeated
conditional checks; also run full proof replay for both variants. No timing
threshold determines correctness.
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

from benchmark_tlsf_checks import ROOT, json_lines, output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--baseline-revision", required=True)
    parser.add_argument("--mode", choices=["debug", "release"], default="debug")
    parser.add_argument("--repeat", type=int, default=2)
    parser.add_argument("--verify-repeat", type=int, default=1)
    parser.add_argument("--lemma", default="tlsf_public_free_run")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.repeat < 1 or args.verify_repeat < 1:
        parser.error("repeat counts must be positive")
    artifacts = {"baseline": args.baseline.resolve(), "candidate": args.candidate.resolve()}
    report = {
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "target": "wasm-gc", "mode": args.mode,
        "platform": platform.platform(), "machine": platform.machine(),
        "stack_limits_bytes": list(resource.getrlimit(resource.RLIMIT_STACK)),
        "baseline_revision": args.baseline_revision,
        "candidate_parent_revision": output("git", "rev-parse", "HEAD"),
        "hol_revision": output("git", "-C", "../hol-light.mbt", "rev-parse", "HEAD"),
        "moon": output("moon", "version"), "moonc": output("moonc", "-v"),
        "moonrun": output("moonrun", "--version"),
        "artifacts": {
            name: {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
            for name, path in artifacts.items()
        },
        "candidate_source_sha256": {
            name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in ["logic/defs.mbt", "logic/definition.mbt"]
        },
        "method": "Fresh processes, sequential runs, compilation excluded; check order alternates. Full replay has its own sample count.",
        "runs": [],
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)

    def save():
        args.out.write_text(json.dumps(report, indent=2) + "\n")

    for selection, count in [(["check", args.lemma], args.repeat), (["verify"], args.verify_repeat)]:
        for repeat in range(count):
            order = ["baseline", "candidate"] if repeat % 2 == 0 else ["candidate", "baseline"]
            for variant in order:
                print(f"{variant} {repeat + 1}: {' '.join(selection)}", flush=True)
                start = time.perf_counter()
                result = subprocess.run(
                    ["moonrun", str(artifacts[variant]), "--", *selection],
                    cwd=ROOT, capture_output=True, text=True,
                )
                wall = time.perf_counter() - start
                rows = json_lines(result.stdout)
                expected = "VERIFIED" if selection == ["verify"] else "CONDITIONAL PASS"
                valid = result.returncode == 0 and any(r.get("status") == expected for r in rows)
                report["runs"].append({
                    "variant": variant, "repeat": repeat + 1, "selection": selection,
                    "wall_seconds": wall, "events": rows, "returncode": result.returncode,
                })
                save()
                if not valid:
                    raise RuntimeError(f"Failed {variant} {selection}:\n{result.stdout}\n{result.stderr}")
                print(f"  {wall:.3f}s", flush=True)
    # Timing differences must not hide a changed result or premise boundary.
    for workload, status in [("check", "CONDITIONAL PASS"), ("verify", "VERIFIED")]:
        results = [
            {key: value for key, value in row.items() if key != "ms"}
            for run in report["runs"] if run["selection"][0] == workload
            for row in run["events"] if row.get("status") == status
        ]
        if not all(row == results[0] for row in results):
            raise RuntimeError(f"{workload} results differ between runs: {results}")
    report["validation"] = {"identical_check_results_and_full_replay_audits": True}
    summary = {}
    for workload in ["check", "verify"]:
        variants = {}
        for variant in artifacts:
            runs = [r for r in report["runs"] if r["variant"] == variant and r["selection"][0] == workload]
            phases = {row["phase"] for run in runs for row in run["events"] if "phase" in row}
            variants[variant] = {
                "samples": len(runs),
                "wall_median_seconds": statistics.median(r["wall_seconds"] for r in runs),
                "phase_median_seconds": {
                    phase: statistics.median(
                        row["ms"] / 1000 for run in runs for row in run["events"] if row.get("phase") == phase
                    ) for phase in sorted(phases)
                },
            }
        baseline = variants["baseline"]["wall_median_seconds"]
        candidate = variants["candidate"]["wall_median_seconds"]
        summary[workload] = {
            **variants, "wall_seconds_saved": baseline - candidate,
            "wall_speedup": baseline / candidate,
        }
    report["summary"] = summary
    save()
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()

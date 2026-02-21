#!/usr/bin/env python3
import argparse
import shutil
import statistics
import subprocess
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "target" / "release"
VM_BIN = TARGET / "vm"
VM_IC_BIN = TARGET / "vm_ic"
VM_NO_IC_BIN = TARGET / "vm_no_ic"


def run(cmd):
    subprocess.run(cmd, cwd=ROOT, check=True)


def build_binaries():
    run(["cargo", "build", "-p", "vm", "--release"])
    shutil.copy2(VM_BIN, VM_IC_BIN)

    run(["cargo", "build", "-p", "vm", "--release", "--no-default-features"])
    shutil.copy2(VM_BIN, VM_NO_IC_BIN)


def measure(binary: Path, runs: int, workload: str) -> list[float]:
    cmd = [
        str(binary),
        "core/init.ktt",
        "core/math.ktt",
        "core/collections.ktt",
        workload,
    ]
    samples = []
    for _ in range(runs):
        start = time.perf_counter()
        subprocess.run(cmd, cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
        samples.append(time.perf_counter() - start)
    return samples


def summarize(name: str, samples: list[float]):
    mean = statistics.mean(samples)
    stdev = statistics.pstdev(samples) if len(samples) > 1 else 0.0
    print(f"{name:>10}: mean={mean:.6f}s stdev={stdev:.6f}s samples={samples}")


def main() -> int:
    parser = argparse.ArgumentParser(description="Compare VM with/without IC cache")
    parser.add_argument("--runs", type=int, default=5)
    parser.add_argument(
        "--workload",
        default="tests/linked_list_chasing.ktt",
        help="workload .ktt path",
    )
    args = parser.parse_args()

    if args.runs < 1:
        print("--runs must be >= 1", file=sys.stderr)
        return 2

    workload_path = ROOT / args.workload
    if not workload_path.exists():
        print(f"workload not found: {workload_path}", file=sys.stderr)
        return 2

    print("Building vm (with ic-cache feature)...")
    build_binaries()

    print(f"Running {args.runs} samples each...")
    ic_samples = measure(VM_IC_BIN, args.runs, args.workload)
    no_ic_samples = measure(VM_NO_IC_BIN, args.runs, args.workload)

    summarize("with_ic", ic_samples)
    summarize("without_ic", no_ic_samples)

    ic_mean = statistics.mean(ic_samples)
    no_ic_mean = statistics.mean(no_ic_samples)
    print(f"speedup (without/with): {no_ic_mean / ic_mean:.4f}x")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

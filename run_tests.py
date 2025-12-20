import os
import subprocess
import sys
import glob
import difflib
from typing import List, Optional
from dataclasses import dataclass
from enum import Enum

TEST_DIR = "tests"
CORE_INIT = "core/init.ktt"
BUILD_CMD = ["cargo", "build", "--release"]
RUN_CMD = ["cargo", "run", "--release", "--quiet", "--", CORE_INIT] 

class Color:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'

class TestStatus(Enum):
    PASSED = 1
    FAILED = 2
    SKIPPED = 3
    ERROR = 4 

@dataclass
class TestResult:
    filename: str
    status: TestStatus
    expected: Optional[str] = None
    actual: Optional[str] = None
    error_message: Optional[str] = None

def build_project() -> bool:
    print(f"{Color.HEADER}Compiling project (release mode)...{Color.ENDC}")
    try:
        result = subprocess.run(BUILD_CMD, check=False)
        if result.returncode == 0:
            print(f"{Color.OKGREEN}Build successful.{Color.ENDC}\n")
            return True
        else:
            print(f"{Color.FAIL}Build failed. Aborting tests.{Color.ENDC}")
            return False
    except FileNotFoundError:
        print(f"{Color.FAIL}Error: 'cargo' not found in PATH.{Color.ENDC}")
        return False

def print_colored_diff(expected: str, actual: str) -> None:
    expected_lines = expected.splitlines()
    actual_lines = actual.splitlines()
    
    diff = difflib.ndiff(expected_lines, actual_lines)
    
    print(f"{Color.BOLD}Diff (Expected vs Actual):{Color.ENDC}")
    for line in diff:
        if line.startswith('-'):
            print(f"{Color.FAIL}{line}{Color.ENDC}")
        elif line.startswith('+'):
            print(f"{Color.OKGREEN}{line}{Color.ENDC}")
        elif line.startswith('?'):
            continue
        else:
            print(line)

def parse_expected_output(filepath: str) -> Optional[str]:
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            lines: List[str] = f.readlines()
    except UnicodeDecodeError:
        print(f"{Color.WARNING}Could not read {filepath}. Skipping.{Color.ENDC}")
        return None

    if not lines:
        return None

    first_line = lines[0].strip()

    if first_line.startswith("// unimplemented"):
        return None

    if not first_line.startswith("// expect:"):
        return None

    expected_lines: List[str] = []
    
    for line in lines[1:]:
        stripped = line.strip()
        if stripped.startswith("//"):
            content = stripped[2:].lstrip() 
            expected_lines.append(content)
        else:
            break
            
    return "\n".join(expected_lines)

def run_test_file(filepath: str, expected_output: str) -> TestResult:
    cmd = RUN_CMD + [filepath]
    
    try:
        result = subprocess.run(
            cmd, 
            capture_output=True, 
            text=True, 
            check=False 
        )
    except Exception as e:
        return TestResult(filepath, TestStatus.ERROR, error_message=str(e))

    if result.returncode != 0:
        return TestResult(
            filepath, 
            TestStatus.ERROR, 
            error_message=f"Exit Code {result.returncode}\nStderr: {result.stderr}"
        )

    actual_clean = result.stdout.strip()
    expected_clean = expected_output.strip()

    if actual_clean == expected_clean:
        return TestResult(filepath, TestStatus.PASSED)
    else:
        return TestResult(
            filepath, 
            TestStatus.FAILED, 
            expected=expected_clean, 
            actual=actual_clean
        )

def main() -> None:
    if not build_project():
        sys.exit(1)

    print(f"{Color.HEADER}Starting Test Runner...{Color.ENDC}")
    test_files: List[str] = sorted(glob.glob(os.path.join(TEST_DIR, "*")))
    results: List[TestResult] = []
    
    for filepath in test_files:
        if os.path.isdir(filepath):
            continue
            
        expected = parse_expected_output(filepath)
        
        if expected is None:
            results.append(TestResult(filepath, TestStatus.SKIPPED))
            continue
            
        print(f"Running {os.path.basename(filepath)}...", end="\r")
        result = run_test_file(filepath, expected)
        results.append(result)
        
        if result.status != TestStatus.PASSED:
             print(f"{Color.FAIL}X{Color.ENDC} {os.path.basename(filepath)}   ")
        else:
             print(f"{Color.OKGREEN}✓{Color.ENDC} {os.path.basename(filepath)}   ")

    print("\n" + "="*40)
    passed = sum(1 for r in results if r.status == TestStatus.PASSED)
    failed = sum(1 for r in results if r.status == TestStatus.FAILED)
    errors = sum(1 for r in results if r.status == TestStatus.ERROR)
    skipped = sum(1 for r in results if r.status == TestStatus.SKIPPED)
    
    print(f"Total: {len(results)} | {Color.OKGREEN}Passed: {passed}{Color.ENDC} | {Color.FAIL}Failed: {failed}{Color.ENDC} | Errors: {errors} | Skipped: {skipped}")
    
    if failed > 0 or errors > 0:
        print("\n" + "="*40)
        print(f"{Color.FAIL}FAILURES & ERRORS:{Color.ENDC}")
        
        for res in results:
            if res.status == TestStatus.FAILED:
                print(f"\n{Color.BOLD}Test:{Color.ENDC} {res.filename}")
                if res.expected is not None and res.actual is not None:
                    print_colored_diff(res.expected, res.actual)
                print("-" * 20)
            elif res.status == TestStatus.ERROR:
                print(f"\n{Color.BOLD}Error in:{Color.ENDC} {res.filename}")
                print(f"{Color.FAIL}{res.error_message}{Color.ENDC}")
                print("-" * 20)
        
        sys.exit(1)
    
    sys.exit(0)

if __name__ == "__main__":
    main()

"""Rebuild the matching CNFs and check the archived LRAT certificates."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "matching_certificates"


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checker", default="lrat-trim")
    parser.add_argument("cases", nargs="*", help="manifest case names (defaults to all)")
    args = parser.parse_args()
    manifest = json.loads((ARCHIVE / "manifest.json").read_text())
    with tempfile.TemporaryDirectory() as temporary:
        cnf = Path(temporary) / "instance.cnf"
        proof = Path(temporary) / "proof.lrat"
        for name in args.cases or manifest["instances"]:
            case = manifest["instances"][name]
            arguments = [str(cnf) if x == "CNF" else x for x in case["arguments"]]
            subprocess.run([sys.executable, ROOT / manifest["generator"], *arguments], check=True)
            with gzip.open(ARCHIVE / case["proof"], "rb") as src, proof.open("wb") as dest:
                shutil.copyfileobj(src, dest)
            if digest(cnf) != case["cnf_sha256"] or digest(proof) != case["uncompressed_proof_sha256"]:
                sys.exit(f"{name}: checksum mismatch")
            run = subprocess.run([args.checker, cnf, proof], capture_output=True, text=True)
            if run.returncode != 20 or "s VERIFIED" not in run.stdout.splitlines():
                sys.exit(f"{name}: verification failed\n{run.stdout}\n{run.stderr}")
            print(f"{name} verified", flush=True)


if __name__ == "__main__":
    main()

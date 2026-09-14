"""Command-line browsing of the Lean-produced report."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import subprocess
from .client import load_report, build_report

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Browse Lean experimental theory comparisons")
    parser.add_argument("--report", type=Path, help="Read a report snapshot; does not recheck proofs")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("list", help="List available experiments and models")
    compare = sub.add_parser("compare", help="Compare selected experiment/model pairs")
    compare.add_argument("scenarios", nargs="*")
    compare.add_argument("--models", nargs="+")
    compare.add_argument("--format", choices=["markdown", "json"], default="markdown")
    html = sub.add_parser("html", help="Write an expandable comparison matrix")
    html.add_argument("output", type=Path)
    sub.add_parser("profiles", help="Show 16 syntactic profiles; existence is not implied")
    verify = sub.add_parser("verify", help="Build a trusted local Lean checkout and read its results")
    verify.add_argument("repo", type=Path, nargs="?", default=Path.cwd())
    args = parser.parse_args(argv)
    try:
        report = build_report(args.repo) if args.command == "verify" else load_report(args.report)
        if args.command in ("list", "verify"):
            print(report.provenance)
            for s in report.data["scenarios"]:
                print(f'{s["id"]}: {s["title"]}')
            print("\nModels: " + ", ".join(m["id"] for m in report.data["models"]))
        elif args.command == "compare":
            s = args.scenarios or None
            if args.format == "json":
                print(json.dumps(report.compare(s, args.models), indent=2))
            else:
                print(report.markdown(s, args.models), end="")
        elif args.command == "html":
            args.output.write_text(report.html(), encoding="utf-8")
            print(args.output)
        elif args.command == "profiles":
            print(report.data["profile_notice"])
            print(json.dumps(report.data["binary_profiles"], indent=2))
        return 0
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        parser.exit(2, f"ontology-separation: {exc}\n")

if __name__ == "__main__":
    raise SystemExit(main())

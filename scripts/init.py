#!/usr/bin/env python3
"""Initialise a fresh fork of the automated-proofs template for a new project.

Usage:
    python scripts/init.py <ProjectName>

Example:
    python scripts/init.py SGDConvergence

What this does:
  1. Renames the Lean library from 'SimplicialLatentGeometry' to <ProjectName> everywhere:
       lakefile.toml, SimplicialLatentGeometry.lean → <ProjectName>.lean, SimplicialLatentGeometry/ → <ProjectName>/
  2. Seeds project scaffolding:
       my_theorems/, help_from_aristotle/proof_decisions_log.md, results/, reports/
  3. Creates a .env template if one does not exist.
  4. Squashes the entire git history to a single 'Initial commit' so your project
     starts with a clean slate (no JEPA history from the template).

Run once, immediately after cloning the template. Do not run again on an existing project.
"""

import os
import re
import sys
import shutil
import pathlib
import subprocess
import textwrap

ROOT = pathlib.Path(__file__).parent.parent.resolve()
OLD_NAME = "SimplicialLatentGeometry"


def die(msg: str) -> None:
    print(f"error: {msg}", file=sys.stderr)
    sys.exit(1)


def run(cmd: list[str], check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, check=check, capture_output=True, text=True)


def replace_in_file(path: pathlib.Path, old: str, new: str) -> bool:
    """Replace all occurrences of old with new in a text file. Returns True if changed."""
    try:
        text = path.read_text()
    except (UnicodeDecodeError, PermissionError):
        return False
    if old not in text:
        return False
    path.write_text(text.replace(old, new))
    return True


def validate_name(name: str) -> None:
    if not re.fullmatch(r"[A-Z][A-Za-z0-9_]*", name):
        die(
            f"'{name}' is not a valid Lean module name.\n"
            "  Must start with an uppercase letter and contain only letters, digits, underscores.\n"
            "  Examples: SGDConvergence, LinearJEPA, MatrixBounds"
        )
    if name == OLD_NAME:
        die(f"Project name cannot be '{OLD_NAME}' — that is the template name.")


def rename_library(new_name: str) -> None:
    print(f"\n[1/4] Renaming library '{OLD_NAME}' → '{new_name}'")

    # Rename the entry-point .lean file
    old_entry = ROOT / f"{OLD_NAME}.lean"
    new_entry = ROOT / f"{new_name}.lean"
    if old_entry.exists():
        old_entry.rename(new_entry)
        print(f"  renamed {old_entry.name} → {new_entry.name}")

    # Rename the library directory
    old_dir = ROOT / OLD_NAME
    new_dir = ROOT / new_name
    if old_dir.exists():
        old_dir.rename(new_dir)
        print(f"  renamed {OLD_NAME}/ → {new_name}/")

    # Update references in all text files at the root and in scripts/
    candidates = (
        list(ROOT.glob("*.toml"))
        + list(ROOT.glob("*.lean"))
        + list(ROOT.glob("*.md"))
        + list((ROOT / new_name).glob("*.lean"))
        + list((ROOT / "scripts").glob("*.py"))
        + list((ROOT / ".github").rglob("*.yml")) if (ROOT / ".github").exists() else []
    )
    # Also update CLAUDE.md if present
    if (ROOT / "CLAUDE.md").exists():
        candidates.append(ROOT / "CLAUDE.md")

    changed = []
    for f in candidates:
        if replace_in_file(f, OLD_NAME, new_name):
            changed.append(f.relative_to(ROOT))
    if changed:
        print(f"  updated references in: {', '.join(str(p) for p in changed)}")


def seed_project_dirs() -> None:
    print("\n[2/4] Seeding project directories")

    dirs = ["my_theorems", "results", "reports"]
    for d in dirs:
        p = ROOT / d
        p.mkdir(exist_ok=True)
        gitkeep = p / ".gitkeep"
        if not any(p.iterdir()) or not gitkeep.exists():
            # directory is empty or has no gitkeep — leave it, just ensure it exists
            pass
        print(f"  {d}/ ready")

    # help_from_aristotle/ with a fresh decisions log
    hfa = ROOT / "help_from_aristotle"
    hfa.mkdir(exist_ok=True)
    log = hfa / "proof_decisions_log.md"
    if not log.exists():
        log.write_text(textwrap.dedent("""\
            # Proof Decisions Log

            Chronological record of proof decisions, bugs found, and Aristotle outcomes.
            Add an entry for every significant decision: definition changes, hypothesis additions,
            lemma splits, and Aristotle job results.

            ---

            ## Initial skeleton (add date and commit hash)

            <!-- Describe the theorem, proof structure chosen, and any helper files created. -->
        """))
        print("  help_from_aristotle/proof_decisions_log.md created")
    else:
        print("  help_from_aristotle/proof_decisions_log.md already exists, skipping")


def create_env_template() -> None:
    print("\n[3/4] Checking .env")
    env = ROOT / ".env"
    if env.exists():
        print("  .env already exists, skipping")
    else:
        env.write_text("ARISTOTLE_API_KEY=arstl_...\n")
        print("  .env template created — add your API key")


def squash_history(new_name: str) -> None:
    print("\n[4/4] Squashing git history")

    # Check we're in a git repo
    result = run(["git", "rev-parse", "--git-dir"], check=False)
    if result.returncode != 0:
        print("  not a git repository — skipping history squash")
        return

    # Check for uncommitted changes
    status = run(["git", "status", "--porcelain"])
    if status.stdout.strip():
        print("  uncommitted changes detected — staging all changes first")
        run(["git", "add", "-A"])

    # Commit the current state (the rename + seed changes)
    run(["git", "add", "-A"])
    commit_result = run(
        ["git", "commit", "--allow-empty", "-m", f"init: {new_name} project from template"],
        check=False,
    )
    if commit_result.returncode != 0 and "nothing to commit" not in commit_result.stdout:
        print(f"  git commit output: {commit_result.stderr.strip()}")

    # Squash all commits into one
    # Strategy: use git commit-tree to create a new root commit from the current tree
    tree = run(["git", "write-tree"]).stdout.strip()
    new_commit = run(
        ["git", "commit-tree", tree, "-m", f"Initial commit — {new_name}"],
    ).stdout.strip()
    run(["git", "update-ref", "HEAD", new_commit])
    print(f"  squashed to single commit {new_commit[:8]}: 'Initial commit — {new_name}'")
    print("  (remote history is unchanged until you force-push — do that after reviewing)")


def main() -> None:
    args = sys.argv[1:]
    if not args or args[0] in ("-h", "--help"):
        print(__doc__)
        sys.exit(0)

    new_name = args[0]
    validate_name(new_name)

    print(f"Initialising template as project '{new_name}'")
    print(f"Working directory: {ROOT}")

    # Guard: don't run if there's already a non-template library directory
    existing = ROOT / new_name
    if existing.exists() and new_name != OLD_NAME:
        die(f"Directory '{new_name}/' already exists. Remove it or choose a different name.")

    rename_library(new_name)
    seed_project_dirs()
    create_env_template()
    squash_history(new_name)

    print(f"""
Done. Next steps:
  1. Add your Aristotle API key to .env
  2. Place your theorem paper in my_theorems/
  3. Run: /new-theorem my_theorems/<paper>.md
  4. When ready to submit: python scripts/submit.py my_theorems/<paper>.md "<prompt>"
""")


if __name__ == "__main__":
    main()

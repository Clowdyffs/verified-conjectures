#!/usr/bin/env python3
"""Index and consistency checks for this collection. Standard library only.

    python3 scripts/collection.py index            regenerate results.json and the README table
    python3 scripts/collection.py check            check every entry (run by CI)
    python3 scripts/collection.py check --release  also refuse placeholders left before publishing
    python3 scripts/collection.py slugs            list entry slugs, oldest solve date first

The checks are structural. They never replace running ./verify.sh, which is the
actual mathematical replay.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

KINDS = {"proof", "disproof", "partial"}
STATUSES = {"verified", "ready", "announced", "in-paper", "withdrawn"}
LEVELS = {"lean-complete", "lean-partial", "computed", "written"}
REQUIRED_FIELDS = ("title", "problem", "statement", "source", "posed", "kind", "status",
                   "verification", "solved", "solved_commit", "novelty_checked")
LEAN_FIELDS = ("lean", "lean_module", "lean_tree", "lean_root_blob", "toolchain")
REQUIRED_FILES = ("README.md", "PROOF.md", "AUDIT.md", "verify.sh", "metadata.json")
PRIVATE_FILES = ("ANNOUNCE.md", "paper.tex")
STANDARD_AXIOMS = ("propext", "Classical.choice", "Quot.sound")

# Constructs that would let a Lean file prove something without a full kernel
# check, or hide part of the file from the checker. Matched outside comments.
FORBIDDEN_LEAN = {
    r"\bsorry\b": "sorry",
    r"\badmit\b": "admit",
    r"\bnative_decide\b": "native_decide (adds Lean.ofReduceBool)",
    r"\bdecide\s*\+native\b": "decide +native (adds Lean.ofReduceBool)",
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?axiom\b": "custom axiom",
    r"\bimplemented_by\b": "implemented_by",
    r"@\[\s*extern\b": "extern",
    r"\bunsafe\b": "unsafe",
    r"skipKernelTC|debug\.skip": "option that skips kernel checking",
    r"^\s*#exit\b": "#exit (truncates the file)",
}


# ---------------------------------------------------------------- front matter

def parse_front_matter(text: str) -> dict:
    """Parse the flat `key: value` YAML subset used by entry READMEs."""
    lines = text.splitlines()
    if not lines or lines[0].strip() != "---":
        raise ValueError("README.md must start with a --- front-matter block")
    data: dict = {}
    for line in lines[1:]:
        if line.strip() == "---":
            return data
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        key, sep, rest = line.partition(":")
        if not sep:
            raise ValueError(f"unparsable front-matter line: {line!r}")
        rest = rest.strip()
        if rest.startswith('"'):
            value, _ = json.JSONDecoder().raw_decode(rest)
        else:
            value = re.sub(r"\s+#.*$", "", rest).strip()
            value = None if value in ("", "null", "~") else value
        data[key.strip()] = value
    raise ValueError("front-matter block is not closed")


# ------------------------------------------------------------ git object hashes

def git_blob_hash(data: bytes) -> str:
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def git_tree_hash(path: Path) -> str:
    """The hash `git rev-parse HEAD:<path>` reports, computed from the files on disk."""
    entries = []
    for child in path.iterdir():
        if child.name in (".git", ".lake"):
            continue
        if child.is_dir():
            entries.append((child.name + "/", b"40000", child.name, git_tree_hash(child)))
        else:
            mode = b"100755" if os.access(child, os.X_OK) else b"100644"
            entries.append((child.name, mode, child.name, git_blob_hash(child.read_bytes())))
    body = b"".join(mode + b" " + name.encode() + b"\0" + bytes.fromhex(digest)
                    for _, mode, name, digest in sorted(entries))
    return hashlib.sha1(b"tree %d\0" % len(body) + body).hexdigest()


# --------------------------------------------------------------------- entries

def load_entries(root: Path = ROOT) -> list[dict]:
    """Read results/<slug>/metadata.json, or README front matter in the development repository."""
    entries = []
    for folder in sorted(p for p in (root / "results").iterdir() if p.is_dir()):
        meta_file = folder / "metadata.json"
        if meta_file.is_file():
            meta = json.loads(meta_file.read_text(encoding="utf-8"))
        elif (folder / "README.md").is_file():
            meta = parse_front_matter((folder / "README.md").read_text(encoding="utf-8"))
        else:
            continue
        meta["slug"] = folder.name
        entries.append(meta)
    entries.sort(key=lambda e: (e.get("solved") or "9999", e["slug"]))
    return entries


def metadata_json(entry: dict) -> str:
    return json.dumps({k: v for k, v in entry.items() if k != "slug"}, ensure_ascii=False, indent=2) + "\n"


def module_paths(entry: dict, root: Path = ROOT) -> tuple[Path, Path]:
    name = entry["lean_module"].removeprefix("Conjectures.")
    return root / "lean" / "Conjectures" / name, root / "lean" / "Conjectures" / f"{name}.lean"


def find_declaration(entry: dict, root: Path = ROOT) -> tuple[Path, int] | None:
    """Locate the final theorem's source line, for a clickable link."""
    module_dir, module_root = module_paths(entry, root)
    short = entry["lean"].rsplit(".", 1)[-1]
    pattern = re.compile(rf"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\s+{re.escape(short)}\b", re.M)
    for path in [module_root, *sorted(module_dir.rglob("*.lean"))]:
        if path.is_file():
            match = pattern.search(path.read_text(encoding="utf-8"))
            if match:
                return path, path.read_text(encoding="utf-8").count("\n", 0, match.start()) + 1
    return None


def mathlib_rev(root: Path = ROOT) -> str | None:
    manifest = root / "lean" / "lake-manifest.json"
    if manifest.is_file():
        for dep in json.loads(manifest.read_text()).get("packages", []):
            if dep.get("name") == "mathlib":
                return dep.get("rev")
    return None


# ----------------------------------------------------------------------- index

ANSWER = {"proof": "True", "disproof": "False", "partial": "Partial"}
LEVEL = {"lean-complete": "Lean, complete", "lean-partial": "Lean, partial",
         "computed": "Exact computation", "written": "Written proof"}
LEVEL_LONG = {"lean-complete": "the Lean kernel checks the exact statement",
              "lean-partial": "Lean checks part of the argument; the entry names the rest",
              "computed": "two independent exact computations, no Lean",
              "written": "written proof only"}


def md_escape(text: str) -> str:
    return str(text).replace("|", "\\|")


def link_identifiers(text: str) -> str:
    """Turn doi:... and arXiv:... identifiers into links."""
    text = re.sub(r"doi:(10\.\d{4,9}/[^\s,;]+?)(?=[.,;]?(?:\s|$))",
                  lambda m: f"[doi:{m[1]}](https://doi.org/{m[1]})", text)
    return re.sub(r"arXiv:(\d{4}\.\d{4,5}(?:v\d+)?)",
                  lambda m: f"[arXiv:{m[1]}](https://arxiv.org/abs/{m[1]})", text)


def entry_links(e: dict) -> str:
    base = f"results/{e['slug']}"
    links = [f"[Proof]({base}/PROOF.md)"]
    if e.get("lean_module"):
        module_dir, _ = module_paths(e, Path("."))
        links.append(f"[Lean statement]({module_dir.as_posix()}/Statement.lean)")
    links += [f"[Audit]({base}/AUDIT.md)", f"[Replay]({base}/verify.sh)"]
    return " · ".join(links)


def render_table(entries: list[dict]) -> str:
    sections = [("Solved", [e for e in entries if e["kind"] in ("proof", "disproof")]),
                ("Partial results", [e for e in entries if e["kind"] == "partial"])]
    out = []
    for heading, rows in sections:
        if not rows:
            continue
        out += [f"### {heading}", "",
                "| Problem | Result | Answer | Checked by | Solved (UTC) | Details |",
                "| :--- | :--- | :---: | :--- | :---: | :--- |"]
        for e in rows:
            answer = f"**{ANSWER[e['kind']]}**"
            problem = f"**[{md_escape(e['problem'])}](results/{e['slug']}/)**"
            title = md_escape(e["title"])
            posed = "" if str(e["posed"]) in e["problem"] else f"Posed {e['posed']} · "
            if e["status"] == "withdrawn":
                problem, title, answer = f"~~{problem}~~", f"Withdrawn. {title}", "Withdrawn"
            out.append(f"| {problem}<br><sub>{posed}{md_escape(e['statement'])}</sub> "
                       f"| {title} | {answer} | {LEVEL[e['verification']]} | {e['solved']} | {entry_links(e)} |")
        out.append("")
    if not out:
        out = ["No results yet.", ""]
    return "\n".join(out).rstrip() + "\n"


def render_glance(e: dict, root: Path = ROOT) -> str:
    """The 'At a glance' panel inserted into each entry README, with links relative to it."""
    up = "../.."
    rows = [("Answer", f"**{ANSWER[e['kind']]}** ({e['kind']})"),
            ("Source", link_identifiers(md_escape(e["source"]))),
            ("Posed", e["posed"]),
            ("Verification", f"`{e['verification']}`: {LEVEL_LONG[e['verification']]}")]
    if e.get("lean_module"):
        module_dir, _ = module_paths(e, Path(up))
        found = find_declaration(e, root)
        if found:
            path, line = found
            rel = f"{up}/{path.relative_to(root).as_posix()}"
            rows.append(("Lean theorem", f"[`{e['lean']}`]({rel}#L{line})"))
        else:
            rows.append(("Lean theorem", f"`{e['lean']}`"))
        rows.append(("Formal statement", f"[`Statement.lean`]({module_dir.as_posix()}/Statement.lean)"))
        rev = mathlib_rev(root)
        tool = e["toolchain"].split(":", 1)[-1]
        mathlib = f", mathlib [`{rev[:10]}`](https://github.com/leanprover-community/mathlib4/tree/{rev})" if rev else ""
        rows.append(("Toolchain", f"Lean {tool}{mathlib}"))
    rows.append(("Replay", f"[`verify.sh`](verify.sh), run as `results/{e['slug']}/verify.sh`"))
    solved = f"{e['solved']} (UTC)"
    if e.get("solved_commit"):
        solved += f", development commit `{e['solved_commit'][:12]}`"
    rows.append(("Solved", solved))
    if e.get("lean_tree"):
        rows.append(("Lean source hash", f"`{e['lean_tree']}`, the git tree of `lean/Conjectures/"
                     f"{e['lean_module'].removeprefix('Conjectures.')}` at the solve commit"))
    rows.append(("Literature check", f"{e['novelty_checked']}, see [AUDIT.md](AUDIT.md)"))
    review = "unrefereed, internal review only"
    rows.append(("Status", f"`{e['status']}`, {review}"))
    if e.get("announced"):
        rows.append(("Announced", md_escape(e["announced"])))
    if e.get("arxiv"):
        rows.append(("arXiv", f"[{e['arxiv']}](https://arxiv.org/abs/{e['arxiv']})"))
    lines = ["## At a glance", "", "| | |", "| :--- | :--- |"]
    lines += [f"| **{k}** | {v} |" for k, v in rows]
    return "\n".join(lines) + "\n"


GLANCE = ("<!-- glance:start -->", "<!-- glance:end -->")


def splice(text: str, markers: tuple[str, str], body: str) -> str:
    start, end = markers
    head, _, rest = text.partition(start)
    _, _, tail = rest.partition(end)
    return f"{head}{start}\n{body}{end}{tail}"


def index_json(entries: list[dict]) -> str:
    keep = ("slug", "problem", "title", "statement", "source", "posed", "kind", "status",
            "verification", "lean", "lean_module", "lean_tree", "lean_root_blob", "toolchain",
            "solved", "solved_commit", "novelty_checked", "announced", "arxiv")
    rows = [{k: e.get(k) for k in keep} for e in entries]
    for row in rows:
        row["path"] = f"results/{row['slug']}/"
        row["verify"] = f"results/{row['slug']}/verify.sh"
    return json.dumps({"results": rows}, ensure_ascii=False, indent=2) + "\n"


def write_index(root: Path = ROOT) -> None:
    entries = load_entries(root)
    (root / "results.json").write_text(index_json(entries), encoding="utf-8")
    readme = root / "README.md"
    readme.write_text(splice(readme.read_text(encoding="utf-8"), ("<!-- results:start -->", "<!-- results:end -->"),
                             render_table(entries)), encoding="utf-8")
    for e in entries:
        entry_readme = root / "results" / e["slug"] / "README.md"
        text = entry_readme.read_text(encoding="utf-8")
        if GLANCE[0] in text:
            entry_readme.write_text(splice(text, GLANCE, render_glance(e, root)), encoding="utf-8")


# ---------------------------------------------------------------------- checks

def strip_lean_comments(src: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and src.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


LINK = re.compile(r"(?<!!)\[[^\]]*\]\(([^)\s]+)(?:\s+\"[^\"]*\")?\)")


def check_links(path: Path, root: Path, errors: list[str]) -> None:
    text = re.sub(r"```.*?```", "", path.read_text(encoding="utf-8"), flags=re.S)
    for target in LINK.findall(text):
        if re.match(r"^[a-z][a-z0-9+.-]*:", target) or target.startswith("#"):
            continue
        local = (path.parent / target.split("#", 1)[0]).resolve()
        if not local.exists() or root.resolve() not in (local, *local.parents):
            errors.append(f"{path.relative_to(root)}: broken link {target}")


def check(root: Path = ROOT, release: bool = False) -> int:
    errors: list[str] = []
    notes: list[str] = []
    try:
        entries = load_entries(root)
    except ValueError as exc:
        print(f"FAIL {exc}")
        return 1
    toolchain_file = root / "lean" / "lean-toolchain"
    toolchain = toolchain_file.read_text().strip() if toolchain_file.exists() else None
    lean_modules = set()
    today = dt.datetime.now(dt.timezone.utc).date()

    for e in entries:
        slug, where = e["slug"], f"results/{e['slug']}"
        for field in REQUIRED_FIELDS:
            if not e.get(field):
                errors.append(f"{where}: missing front-matter field {field}")
        if e.get("kind") not in KINDS:
            errors.append(f"{where}: kind {e.get('kind')!r} not in {sorted(KINDS)}")
        if e.get("status") not in STATUSES:
            errors.append(f"{where}: status {e.get('status')!r} is not publishable")
        if e.get("verification") not in LEVELS:
            errors.append(f"{where}: verification {e.get('verification')!r} not in {sorted(LEVELS)}")
        if e.get("kind") in ("proof", "disproof") and e.get("verification") != "lean-complete" \
                and e.get("status") != "withdrawn":
            notes.append(f"{where}: solved result below lean-complete; the README must say so")
        for name in REQUIRED_FILES:
            if not (root / where / name).is_file():
                errors.append(f"{where}: missing {name}")
        for name in PRIVATE_FILES:
            if (root / where / name).exists():
                errors.append(f"{where}: private draft {name} must not be published")
        verify = root / where / "verify.sh"
        if verify.is_file() and not os.access(verify, os.X_OK):
            errors.append(f"{where}: verify.sh is not executable")
        if str(e.get("verification", "")).startswith("lean"):
            for field in LEAN_FIELDS:
                if not e.get(field):
                    errors.append(f"{where}: missing front-matter field {field}")
            if e.get("lean_module"):
                module_dir, module_root = module_paths(e, root)
                lean_modules.add(e["lean_module"])
                if not (module_dir / "Statement.lean").is_file():
                    errors.append(f"{where}: {module_dir.relative_to(root)}/Statement.lean missing")
                elif e.get("lean_tree") and git_tree_hash(module_dir) != e["lean_tree"]:
                    errors.append(f"{where}: Lean sources differ from the solve commit "
                                  f"(tree {git_tree_hash(module_dir)} != {e['lean_tree']}); "
                                  "re-verify and log the change in HISTORY.md")
                if module_root.is_file() and e.get("lean_root_blob") and \
                        git_blob_hash(module_root.read_bytes()) != e["lean_root_blob"]:
                    errors.append(f"{where}: {module_root.relative_to(root)} differs from the solve commit")
            if toolchain and e.get("toolchain") and e["toolchain"] != toolchain:
                errors.append(f"{where}: toolchain {e['toolchain']} != lean/lean-toolchain {toolchain}")
        if e.get("novelty_checked") and e.get("status") in ("verified", "ready"):
            age = (today - dt.date.fromisoformat(e["novelty_checked"])).days
            if age > 7:
                notes.append(f"{where}: literature check is {age} days old; recheck before announcing")

    # Lean hygiene across every published Lean file.
    for lean_file in sorted((root / "lean").rglob("*.lean")):
        if ".lake" in lean_file.parts:
            continue
        code = strip_lean_comments(lean_file.read_text(encoding="utf-8"))
        for pattern, label in FORBIDDEN_LEAN.items():
            for match in re.finditer(pattern, code, flags=re.M):
                line = code.count("\n", 0, match.start()) + 1
                errors.append(f"{lean_file.relative_to(root)}:{line}: forbidden {label}")

    lakefile = root / "lean" / "lakefile.toml"
    if lakefile.exists():
        targets = set(re.findall(r'"([^"]+)"', (re.search(r"defaultTargets\s*=\s*\[([^\]]*)\]",
                      lakefile.read_text()) or [None, ""])[1]))
        if targets != lean_modules:
            errors.append(f"lean/lakefile.toml defaultTargets {sorted(targets)} != entry modules {sorted(lean_modules)}")

    # Index in sync.
    if (root / "results.json").read_text(encoding="utf-8") != index_json(entries):
        errors.append("results.json is stale: run python3 scripts/collection.py index")
    if render_table(entries) not in (root / "README.md").read_text(encoding="utf-8"):
        errors.append("README.md results table is stale: run python3 scripts/collection.py index")
    for e in entries:
        text = (root / "results" / e["slug"] / "README.md").read_text(encoding="utf-8")
        if text.startswith("---"):
            errors.append(f"results/{e['slug']}/README.md: front matter must move to metadata.json")
        if not (root / "results" / e["slug"] / "metadata.json").is_file():
            errors.append(f"results/{e['slug']}: missing metadata.json")
        if GLANCE[0] not in text:
            errors.append(f"results/{e['slug']}/README.md: missing the At a glance block")
        elif render_glance(e, root) not in text:
            errors.append(f"results/{e['slug']}/README.md: At a glance block is stale: run python3 scripts/collection.py index")

    # Links in every Markdown file.
    for md in sorted(root.rglob("*.md")):
        if not {".git", ".lake"} & set(md.parts):
            check_links(md, root, errors)

    if release:
        for path in sorted(root.rglob("*")):
            if path.is_file() and not {".git", ".lake"} & set(path.parts) and path.suffix in (
                    ".md", ".cff", ".toml", ".json", ".sh", ".py", ".lean", ".yml", "") \
                    and path.name != "collection.py":
                if "TODO(user)" in path.read_text(encoding="utf-8", errors="replace"):
                    errors.append(f"{path.relative_to(root)}: placeholder TODO(user) left")

    for note in notes:
        print(f"note  {note}")
    for error in errors:
        print(f"FAIL  {error}")
    print(f"{len(entries)} entries, {len(errors)} problems" + (" (release check)" if release else ""))
    return 1 if errors else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("index")
    sub.add_parser("slugs")
    c = sub.add_parser("check")
    c.add_argument("--release", action="store_true")
    args = parser.parse_args()
    if args.command == "index":
        write_index()
        return 0
    if args.command == "slugs":
        for e in load_entries():
            if e["status"] != "withdrawn":
                print(e["slug"])
        return 0
    return check(release=args.release)


if __name__ == "__main__":
    sys.exit(main())

"""Check declaration coverage and pinned GitHub snippet ranges using stdlib only."""

from pathlib import Path
import re
import subprocess

project = Path(__file__).resolve().parent
root = project.parent.parent
main = (project / "main.tex").read_text()
revision = re.search(r"/blob/([0-9a-f]{40})", main).group(1)
text = "\n".join(p.read_text() for p in sorted(project.glob("*.tex")))
references = re.findall(
    r"\\lean\{([^}]+)\}\{(\d+)\}\{(\d+)\}\{([^}]+)\}", text
)
# Index by module once: repeatedly resolving paths inside the declaration
# loop made the growing commentary checker needlessly quadratic.
source_ranges = {}
for name, start, end, _ in references:
    source_ranges.setdefault(name, []).append((int(start), int(end)))
errors = []
declarations = 0
# Validate exactly the immutable publication. Untracked proof work is not part
# of that revision and must not be presented as published or documented.
versioned_sources = subprocess.check_output(
    ["git", "ls-tree", "-r", "--name-only", revision, "--", "Hypernets"],
    cwd=root, text=True,
).splitlines()
for path in sorted(root / name for name in versioned_sources if name.endswith(".lean")):
    relative = path.relative_to(root).as_posix()
    pinned = subprocess.run(
        ["git", "show", f"{revision}:{relative}"],
        cwd=root,
        check=True,
        text=True,
        capture_output=True,
    ).stdout
    if path.read_text() != pinned:
        errors.append(f"Working source differs from pinned revision: {relative}")
    for number, line in enumerate(pinned.splitlines(), 1):
        if re.match(r"^(?:@\[[^\n]*?\]\s*)?(?:noncomputable\s+)?(?:structure|inductive|def|abbrev|theorem|example)\b", line):
            declarations += 1
            module = path.relative_to(root / "Hypernets").with_suffix("").as_posix()
            if not any(start <= number <= end for start, end in source_ranges.get(module, [])):
                errors.append(f"Uncovered declaration: {relative}:{number}: {line}")

for name, start, end, label in references:
    relative = f"Hypernets/{name}.lean"
    if relative not in versioned_sources:
        errors.append(f"Source-fragment target is absent from pinned revision: {relative}")
    path = root / "Hypernets" / f"{name}.lean"
    if not path.exists() or not 1 <= int(start) <= int(end) <= len(path.read_text().splitlines()):
        errors.append(f"Invalid range: {name}:{start}-{end}: {label}")

# Glossary entries must resolve to unique in-document definition destinations.
glossary = re.findall(r"\\glossaryentry\{([^}]+)\}\{([^}]+)\}", text)
term_destinations = re.findall(r"\\label\{term:([a-z0-9-]+)\}", text)
term_destinations += re.findall(r"\\termdef\{([a-z0-9-]+)\}", text)
for key, title in glossary:
    if term_destinations.count(key) != 1:
        errors.append(f"Glossary destination is missing or ambiguous: {title}: {key}")
if [title.casefold() for _, title in glossary] != sorted(title.casefold() for _, title in glossary):
    errors.append("Technical terms are not in alphabetical order")

if errors:
    raise SystemExit("\n".join(errors))
print(f"Verified {declarations} declarations and {len(references)} source-fragment links.")
print(f"All source files match pinned revision {revision}.")

print(f"Verified {len(glossary)} glossary entries and {len(set(term_destinations))} internal definition destinations.")

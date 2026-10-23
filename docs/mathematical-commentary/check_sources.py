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
errors = []
declarations = 0
for path in sorted((root / "Hypernets").rglob("*.lean")):
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
            if not any(
                name == path.relative_to(root / "Hypernets").with_suffix("").as_posix() and int(start) <= number <= int(end)
                for name, start, end, _ in references
            ):
                errors.append(f"Uncovered declaration: {relative}:{number}: {line}")

for name, start, end, label in references:
    path = root / "Hypernets" / f"{name}.lean"
    if not path.exists() or not 1 <= int(start) <= int(end) <= len(path.read_text().splitlines()):
        errors.append(f"Invalid range: {name}:{start}-{end}: {label}")

if errors:
    raise SystemExit("\n".join(errors))
print(f"Verified {declarations} declarations and {len(references)} source-fragment links.")
print(f"All source files match pinned revision {revision}.")

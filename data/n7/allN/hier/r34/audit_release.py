"""Audit frozen release paths and redact any candidate sensitive values in the output."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
from urllib.parse import unquote, urlsplit
import gzip
import os
import re
import subprocess
import sys

ROOT = Path(sys.argv[1])
OUT = Path(sys.argv[2])
TEXT_EXTENSIONS = {".md", ".tex", ".bib", ".json", ".py", ".lean", ".cff", ".txt", ".sh",
                   ".toml", ".out", ".sha256", ".cpp", ".gitignore"}
PATTERNS = {
    "machine_path": re.compile(rb'(?<![\w:])/((private/)?var/folders/|Users/|home/|root/|Volumes/|mnt/|workspace/)[^ \t\r\n)"\x60]+'),
    "scratch_path": re.compile(rb'(?<![\w:])/(private/)?tmp/[^ \t\r\n)"\x60]+'),
    "email": re.compile(rb'(?<![\w.])[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}(?![\w.])'),
    "credential": re.compile(rb'-----BEGIN (?:RSA |EC |OPENSSH |DSA )?PRIVATE KEY-----|(?:AKIA|ASIA)[A-Z0-9]{16}|gh[pousr]_[A-Za-z0-9]{25,}|github_pat_[A-Za-z0-9_]{25,}|(?:AWS_SECRET_ACCESS_KEY|API_KEY|ACCESS_TOKEN)\s*=\s*[^\s$({]{16,}'),
}
assert PATTERNS["machine_path"].search(b"example /Users/tester/scratch")
assert PATTERNS["credential"].search(b"example -----BEGIN OPENSSH PRIVATE KEY-----")
assert PATTERNS["email"].search(b"example person@example.net")

paths = [
    p for p in sorted(ROOT.rglob("*"))
    if ".git" not in p.relative_to(ROOT).parts and p.is_file()
]

def local_exists(relative):
    if relative.startswith("/") or relative.startswith("~"):
        return False
    normalized = os.path.normpath(relative)
    return not normalized.startswith("../") and (ROOT / normalized).exists()


manifest = {}
for row in (ROOT / "FILES.sha256").read_text().splitlines():
    expected, name = row.split("  ", 1)
    assert local_exists(name), name
    manifest[name] = expected
listed = set(manifest)
actual = {str(p.relative_to(ROOT)) for p in paths} - {"FILES.sha256"}
bad = [p for p, expected in manifest.items() if sha256((ROOT / p).read_bytes()).hexdigest() != expected]
print(f"FILES.sha256: {len(manifest)} entries, {len(bad)} differing, "
      f"extra={sorted(actual-listed)}, unshipped={sorted(listed-actual)}")
print("Manifest mismatches:", bad)
(OUT / "release-files-opened.txt").write_text("FILES.sha256\n" + "\n".join(sorted(actual)) + "\n")

link_pattern = re.compile(r"(?<!!)\[[^\]]*\]\(([^)\s]+)\)")
checked_links = 0
for file in paths:
    if file.suffix != ".md":
        continue
    current = file.relative_to(ROOT)
    for line, paragraph in enumerate(file.read_text().splitlines(), 1):
        for match in link_pattern.finditer(paragraph):
            parts = urlsplit(match.group(1))
            if parts.scheme or parts.netloc or not parts.path:
                continue
            link = unquote(parts.path)
            checked_links += 1
            if not local_exists(str(current.parent / link)):
                print(f"Unresolved Markdown link {current}:{line}: {link}")
print(f"Explicit local Markdown links checked: {checked_links}")

for file in paths:
    current = file.relative_to(ROOT)
    if file.suffix == ".gz":
        with gzip.open(file, "rb") as compressed:
            data = compressed.read()
    elif file.suffix in TEXT_EXTENSIONS or file.name in {
        "lean-toolchain", ".gitignore", "LICENSE", "LICENSE-CC-BY-4.0",
    }:
        data = file.read_bytes()
    elif file.suffix == ".pdf":
        data = subprocess.run(["pdftotext", "-layout", str(file), "-"], check=True,
                              capture_output=True).stdout
    else:
        print(f"Text categories skip {current}")
        continue
    for category, pattern in PATTERNS.items():
        matches = [data.count(b"\n", 0, match.start()) + 1 for match in pattern.finditer(data)]
        if matches:
            print(f"{category}: {current}, matches={len(matches)}, lines={matches[:20]}")

git = ["git", "--no-pager", "-c", "core.fsmonitor=false", "-C", str(ROOT)]
env = dict(os.environ, GIT_OPTIONAL_LOCKS="0", GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL="/dev/null")
git_format = subprocess.check_output(
    git + ["log", "--all", "--no-show-signature", "--format=%H%x09%ae%x09%ce"], env=env, text=True)
email_domains = Counter()
for row in git_format.splitlines():
    _, author, committer = row.split("\t")
    for address in (author, committer):
        email_domains[address.split("@")[-1] if "@" in address else "(no domain)"] += 1
print(f"Git metadata: {len(git_format.splitlines())} reachable commit(s); email domains {dict(email_domains)}")
for row in subprocess.check_output(
    git + ["config", "--local", "--get-regexp", r"^remote\..*\.url$"],
    env=env, text=True,
).splitlines():
    key, url = row.split(maxsplit=1)
    parsed = urlsplit(url)
    print(f"Git {key}: scheme={parsed.scheme}, host={parsed.hostname}, "
          f"userinfo={(parsed.username is not None or parsed.password is not None)}")

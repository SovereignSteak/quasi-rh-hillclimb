"""Render the upstream verification table from a retained tracker catalogue snapshot."""
from decimal import Decimal, localcontext
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
BEGIN = "<!-- tracker-verification-table:start -->"
END = "<!-- tracker-verification-table:end -->"


def table(catalogue):
    lines = [
        "| Contributor | Source | Boundary θ (approx.) | Lean verification status |",
        "|---|---|---:|---|",
    ]
    for row in catalogue["records"]:
        if row["status"] != "framework-verified":
            raise ValueError(f"Unexpected catalogue status: {row['id']}")
        authors = ", ".join(author["name"] for author in row["authors"])
        with localcontext() as context:
            context.prec = 50
            value = Decimal(row["theta"]["numerator"]) / Decimal(row["theta"]["denominator"])
            boundary = f"{value:.12f}".rstrip("0").rstrip(".")
        if row.get("pr"):
            source = f"[Tracker #{row['pr']}](https://github.com/{row['repository']}/pull/{row['pr']})"
        else:
            source = f"[Checked source]({row['solution_url']})"
        certificate = "https://gtimg.github.io/QuasiRiemannTracker/" + row["certificate_url"]
        lines.append(f"| {authors} | {source} | {boundary} | [Tracker verified]({certificate}) |")
    return "\n".join(lines)


if __name__ == "__main__":
    snapshot = ROOT / "verification/readme-progress/tracker-catalogue.json"
    catalogue = json.loads(snapshot.read_text())
    readme = ROOT / "README.md"
    text = readme.read_text()
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        raise ValueError("Expected exactly one generated tracker table")
    before, rest = text.split(BEGIN)
    _, after = rest.split(END)
    readme.write_text(before + BEGIN + "\n\n" + table(catalogue) + "\n\n" + END + after)
    print(f"Rendered {len(catalogue['records'])} contributor verification rows from {snapshot}")

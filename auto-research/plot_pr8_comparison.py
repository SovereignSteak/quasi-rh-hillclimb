"""Render a source-backed comparison; full proof status comes only from a replay receipt."""
import argparse
import csv
import json
import os
import zipfile
from datetime import datetime
from fractions import Fraction
from pathlib import Path
from zoneinfo import ZoneInfo

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--evidence", type=Path, default=ROOT / "verification/pr8-independent")
parser.add_argument("--submission", type=Path, default=ROOT / "submissions/hailey-collet-1252270103")
parser.add_argument("--replay", type=Path)
parser.add_argument("--output", type=Path, default=ROOT / "graphs/pr8-comparison")
args = parser.parse_args()
os.environ.setdefault("MPLCONFIGDIR", str(args.evidence / "matplotlib-cache"))
import matplotlib
matplotlib.use("Agg")
import matplotlib.dates as mdates
import matplotlib.pyplot as plt
from matplotlib.ticker import FormatStrFormatter

catalogue = json.loads((args.evidence / "tracker-catalogue.json").read_text())
summary = json.loads((args.submission / "verification/summary.json").read_text())
pr = json.loads((args.evidence / "pr8.json").read_text())
tracker_pr = json.loads((args.evidence / "tracker-pr69.json").read_text())
target = Fraction(summary["result"]["theta"])
# Preserve the original plotted proposals and their historical timestamps.
with (ROOT / "graphs/timeline.csv").open() as stream:
    conditional = [dict(row, pr=(2 if "Sudarsh" in row["contributor"] else
                                6 if "PR #68" in row["contributor"] else 1),
                        timestamp_source="original timeline.csv (UTC)")
                   for row in csv.DictReader(stream) if row["status"].startswith("conditional")]
conditional += json.loads((ROOT / "graphs/conditional-pr-refinements.json").read_text())
assert all(row["status"] == "conditional, not Lean-verified" for row in conditional)
assert len({(r["time_utc"], r["contributor"], r["theta_exact"]) for r in conditional}) == len(conditional)

records = [r for r in catalogue["records"] if r["status"] == "framework-verified"]
fraction = lambda r: Fraction(int(r["theta"]["numerator"]), int(r["theta"]["denominator"]))
best = min(records, key=fraction)
baseline = next(r for r in records if r["id"] == "openai-baseline")
base = fraction(baseline)
assert target < fraction(best), "The submission is no longer the strongest compared boundary"
assert tracker_pr["headRefOid"] == summary["result"]["source_commit"]
verified = False
receipt = None
if args.replay:
    receipt = json.loads(args.replay.read_text())
    identity = json.loads((args.evidence / "run-identity.json").read_text())
    compilation = json.loads((args.evidence / "compilation-audit.json").read_text())
    assert identity["source_commit"] == compilation["source_commit"] == summary["result"]["source_commit"]
    verified = (receipt.get("status") == "passed"
                and receipt.get("compiled_modules") == summary["completed"]["source_modules"]
                and receipt.get("axiom_audit_passed") is True
                and receipt.get("sources_unchanged") is True
                and receipt.get("endpoint", {}).get("exit_code") == 0
                and receipt.get("kernel-replay", {}).get("exit_code") == 0)

tz = ZoneInfo("America/New_York")
date = lambda s: datetime.fromisoformat(s.replace("Z", "+00:00")).astimezone(tz)
stamp = lambda r: date(r.get("timeline_at") or r.get("submitted_at") or r["first_verified_at"])
events = sorted((r for r in records if fraction(r) <= base), key=stamp)
frontier, incumbent = [], None
for record in events:
    value = fraction(record)
    if incumbent is None or value < incumbent:
        frontier.append(record)
        incumbent = value
with zipfile.ZipFile(args.submission / "lean-sources.zip") as archive:
    metadata = json.loads(archive.read("metadata.json"))
author = ", ".join(a["name"] for a in metadata["authors"])
candidate_time = date(pr["createdAt"])
retrieved_at = json.loads((args.evidence / "retrieval.json").read_text())["retrieved_at"]
checked_label = date(retrieved_at).strftime("%b %d, %Y %H:%M %Z")
gain = fraction(best) - target
relative_gain = gain / (base - fraction(best))
INK, MUTED, BLUE, GREEN, AMBER, BG = "#17243a", "#53647b", "#2864b5", "#077b61", "#ad601c", "#f8fafc"
accent = GREEN if verified else AMBER
plt.rcParams.update({"font.family": "DejaVu Sans", "text.color": INK,
                     "axes.labelcolor": MUTED, "xtick.color": MUTED, "ytick.color": MUTED,
                     "font.size": 11, "svg.fonttype": "none"})
fig = plt.figure(figsize=(20, 20), facecolor=BG)
fig.text(.06, .96, "Quasi-Riemann Hypothesis: progress in the zero-free boundary", fontsize=25, weight="bold")
fig.text(.06, .935, "All-moduli Dirichlet nonvanishing for Re(s) > θ, excluding the principal pole. Lower θ is stronger.", fontsize=12, color=MUTED)
fig.text(.06, .885, f"θ = {float(target):.10f}", fontsize=36, weight="bold", color=accent)
fig.text(.06, .855, f"{author} · hillclimb PR #{pr['url'].split('/')[-1]} · {summary['result']['theta']}", fontsize=12)
status = "Fresh native Lean compilation + kernel replay passed" if verified else "Lowest submitted boundary · independent Lean replay pending"
fig.text(.06, .825, status, fontsize=12, color=accent, weight="bold")
fig.text(.66, .9, f"{float(relative_gain):.1%}", fontsize=32, weight="bold", color=accent)
fig.text(.66, .875, "more improvement beyond 7/8", fontsize=12)
fig.text(.66, .855, "than the accepted tracker record", fontsize=12, color=MUTED)
fig.text(.66, .825, f"Boundary reduction: {float(gain):.10f}", fontsize=11, color=MUTED)

ax = fig.add_axes([.08, .38, .46, .39], facecolor=BG)
times, values = [stamp(r) for r in frontier], [float(fraction(r)) for r in frontier]
ax.step(times + [candidate_time], values + [values[-1]], where="post", color=BLUE, lw=2.4)
ax.scatter(times, values, s=26, color=BLUE, zorder=3)
ax.plot([candidate_time, candidate_time], [values[-1], float(target)], color=accent, ls="--", lw=2)
ax.scatter([candidate_time], [float(target)], s=95, marker="D", color=accent if verified else BG, edgecolor=accent, lw=2, zorder=4)
conditional_time = lambda row: date(row["time_utc"].replace(" ", "T") + ("Z" if not row["time_utc"].endswith("Z") else ""))
conditional_groups = {number: [r for r in conditional if r["pr"] == number]
                      for number in sorted({r["pr"] for r in conditional})}
conditional_endpoints = []
for number, group in conditional_groups.items():
    ordered = sorted(group, key=lambda r: (conditional_time(r), -Fraction(r["theta_exact"])))
    ax.plot([conditional_time(r) for r in ordered],
            [float(Fraction(r["theta_exact"])) for r in ordered],
            color=AMBER, lw=1.5, ls="--", marker="_", markevery=[len(ordered)-1],
            markersize=9, markeredgewidth=1.5, zorder=4)
    conditional_endpoints.append(min(group, key=lambda r: Fraction(r["theta_exact"])))
ax.set_title("Tracker progress and conditional PR contributions", loc="left", pad=16, fontsize=12, weight="bold")
ax.set_ylabel("Zero-free boundary θ")
ax.yaxis.set_major_formatter(FormatStrFormatter("%.5f"))
ax.xaxis.set_major_locator(mdates.AutoDateLocator(minticks=4, maxticks=6, tz=tz))
ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d", tz=tz))
ax.margins(x=.05, y=.13)

# Keep labels in boundary order in their own column. Even vertical spacing
# separates the crowded recent points while retaining a leader to every point.
fig.text(.59, .785, "Contributor · source PR · boundary θ", fontsize=12, weight="bold")
points = [
    (stamp(r), fraction(r), ", ".join(a["name"] for a in r["authors"]),
     f"#{r['pr']}" if r.get("pr") else "", BLUE, r["id"] == best["id"])
    for r in frontier
]
points.append((candidate_time, target, author,
               f"PR #{pr['url'].split('/')[-1]} (this repo)", accent, True))
for row in conditional_endpoints:
    points.append((conditional_time(row), Fraction(row["theta_exact"]),
                   row["contributor"].split(" · ")[0],
                   f"repo #{row['pr']} · conditional", AMBER, True))
points.sort(key=lambda p: p[1], reverse=True)
contributor_labels = []
for index, (time, boundary, name, source, color, highlight) in enumerate(points):
    label_y = .757 - index * (.363 / max(1, len(points) - 1))
    value = f"{float(boundary):.12f}".rstrip("0").rstrip(".")
    label = " · ".join(part for part in (name, source, value) if part)
    annotation = ax.annotate(
        label, (time, float(boundary)), xycoords="data",
        xytext=(.59, label_y), textcoords="figure fraction",
        ha="left", va="center", fontsize=12,
        color=color if highlight else INK,
        weight="bold" if highlight else "normal", annotation_clip=False,
        arrowprops=dict(arrowstyle="-", color=color if highlight else MUTED,
                        lw=.7, alpha=.8, shrinkA=5, shrinkB=3,
                        relpos=(0, .5), connectionstyle="arc3,rad=0"),
    )
    contributor_labels.append(annotation)

bx = fig.add_axes([.08, .16, .85, .14], facecolor=BG)
recent = sorted(records, key=fraction)[:3][::-1]
labels = [", ".join(a["name"] for a in r["authors"]) + f" · #{r['pr']}" for r in recent] + [author + " · PR #8"]
gains = [float((base - fraction(r)) * 10**6) for r in recent] + [float((base - target) * 10**6)]
bars = bx.barh(range(len(gains)), gains, color=[BLUE]*len(recent)+[accent], height=.42)
bx.invert_yaxis()
bx.set_yticks([])
bx.set_xlim(0, max(gains)*1.12)
for i, (label, value, bar) in enumerate(zip(labels, gains, bars)):
    bx.text(0, i-.31, label, fontsize=10, weight="bold" if i == len(gains)-1 else "normal")
    bx.text(value+2, i, f"{value:.2f}", va="center", fontsize=10)
bx.set_ylim(len(gains)-.3, -.8)
bx.set_xlabel("Improvement beyond 7/8 (× 10⁻⁶)", labelpad=10, fontsize=10)
bx.set_title("Recent accepted bounds vs PR #8", loc="left", pad=16, fontsize=12, weight="bold")
for a in (ax, bx):
    a.grid(axis="y" if a is ax else "x", color="#dce4ed", linewidth=.7)
    a.set_axisbelow(True)
    a.tick_params(length=0, pad=8)
    for spine in a.spines.values():
        spine.set_visible(False)
foot = ("Blue: accepted tracker records. " + ("Green: independent native Lean verification." if verified else "Amber: submitted proof, replay pending.") +
        " Orange dashed: one line per conditional PR; not Lean-verified.")
fig.text(.06, .085, "Tracker Comparator/NanoDa/con-ron acceptance for PR #8 remains pending.", fontsize=9, color=MUTED)

fig.text(.06, .1, foot, fontsize=9, color=MUTED)
fig.text(.06, .06, f"Compared {checked_label} · {len(records)} accepted tracker entries, PR #8 and {len(conditional)} conditional PR points. Timeline dates shown in America/New_York.\n"
         "Sources: GTimG/QuasiRiemannTracker live catalogue; rohanarun/quasi-rh-hillclimb PRs #1–3, #6, #8; original timeline.csv; frozen source package.", fontsize=9, color=MUTED, linespacing=1.7)
fig.text(.06, .025, "This is a comparison of the cited sources, not a claim of a worldwide record or independent verification of the entire manuscript.", fontsize=9, color=MUTED)
# Measure the rendered labels, shrink long entries only as needed, and ensure
# the expanded contributor list stays on the canvas without overlapping.
from matplotlib.text import Text
fig.canvas.draw()
renderer = fig.canvas.get_renderer()
for label in contributor_labels:
    box = Text.get_window_extent(label, renderer)
    available = fig.bbox.width * .98 - box.x0
    if box.width > available:
        label.set_fontsize(label.get_fontsize() * available / box.width)
fig.canvas.draw()
renderer = fig.canvas.get_renderer()
boxes = [Text.get_window_extent(label, renderer) for label in contributor_labels]
assert all(0 <= b.x0 < b.x1 <= fig.bbox.width and 0 <= b.y0 < b.y1 <= fig.bbox.height for b in boxes)
assert all(not a.overlaps(b) for i, a in enumerate(boxes) for b in boxes[i+1:])
assert all(label.arrow_patch is not None for label in contributor_labels)
args.output.parent.mkdir(parents=True, exist_ok=True)
for suffix in ("png", "svg"):
    fig.savefig(args.output.with_suffix("."+suffix), dpi=200, facecolor=BG)
    if suffix == "svg":
        svg = args.output.with_suffix(".svg")
        svg.write_text("\n".join(line.rstrip() for line in svg.read_text().splitlines()) + "\n")
args.output.with_suffix(".json").write_text(json.dumps({"candidate_theta": str(target), "accepted_best_theta": str(fraction(best)),
    "difference_exact": str(gain), "relative_gain_beyond_baseline_exact": str(relative_gain),
    "conditional_points": conditional, "independent_native_lean_passed": verified, "tracker_acceptance": False,
    "catalogue_as_of": catalogue["as_of"], "retrieved_at": retrieved_at, "source_commit": summary["result"]["source_commit"]}, indent=2)+"\n")
print(args.output.with_suffix(".png"))

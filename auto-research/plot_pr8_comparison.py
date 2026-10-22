"""Render a source-backed comparison; full proof status comes only from a replay receipt."""
import argparse
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
fig = plt.figure(figsize=(16, 10), facecolor=BG)
fig.text(.06, .94, "Current best boundary in the cited results" if verified else "The strongest boundary in this comparison", fontsize=25, weight="bold")
fig.text(.06, .902, "All-moduli Dirichlet nonvanishing for Re(s) > θ, excluding the principal pole. Lower θ is stronger.", fontsize=12, color=MUTED)
fig.text(.06, .826, f"θ = {float(target):.10f}", fontsize=36, weight="bold", color=accent)
fig.text(.06, .784, f"{author} · hillclimb PR #{pr['url'].split('/')[-1]} · {summary['result']['theta']}", fontsize=12)
status = "Fresh native Lean compilation + kernel replay passed" if verified else "Lowest submitted boundary · independent Lean replay pending"
fig.text(.06, .747, status, fontsize=12, color=accent, weight="bold")
fig.text(.66, .843, f"{float(relative_gain):.1%}", fontsize=32, weight="bold", color=accent)
fig.text(.66, .807, "more improvement beyond 7/8", fontsize=12)
fig.text(.66, .778, "than the accepted tracker record", fontsize=12, color=MUTED)
fig.text(.66, .743, f"Boundary reduction: {float(gain):.10f}", fontsize=11, color=MUTED)

ax = fig.add_axes([.08, .23, .48, .43], facecolor=BG)
times, values = [stamp(r) for r in frontier], [float(fraction(r)) for r in frontier]
ax.step(times + [candidate_time], values + [values[-1]], where="post", color=BLUE, lw=2.4)
ax.scatter(times, values, s=26, color=BLUE, zorder=3)
ax.plot([candidate_time, candidate_time], [values[-1], float(target)], color=accent, ls="--", lw=2)
ax.scatter([candidate_time], [float(target)], s=95, marker="D", color=accent if verified else BG, edgecolor=accent, lw=2, zorder=4)
ax.annotate(f"{author}\n{float(target):.10f}", (candidate_time, float(target)), xytext=(-12, 7), textcoords="offset points", ha="right", fontsize=11, weight="bold", color=accent)
ax.annotate(f"Accepted tracker best\n{float(fraction(best)):.7f}", (times[-1], values[-1]), xytext=(-12, 32), textcoords="offset points", ha="right", color=BLUE, fontsize=10)
ax.set_title("Progress in the accepted tracker catalogue", loc="left", pad=16, fontsize=12, weight="bold")
ax.set_ylabel("Zero-free boundary θ")
ax.yaxis.set_major_formatter(FormatStrFormatter("%.5f"))
ax.xaxis.set_major_locator(mdates.AutoDateLocator(minticks=4, maxticks=6, tz=tz))
ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d", tz=tz))
ax.margins(x=.05, y=.13)

bx = fig.add_axes([.68, .23, .25, .43], facecolor=BG)
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
        " Tracker Comparator/NanoDa/con-ron acceptance for PR #8 remains pending.")
fig.text(.06, .145, foot, fontsize=9, color=MUTED)
fig.text(.06, .086, f"Compared {checked_label} · {len(records)} accepted tracker entries plus PR #8. Timeline dates shown in America/New_York.\n"
         "Sources: GTimG/QuasiRiemannTracker live catalogue; rohanarun/quasi-rh-hillclimb PR #8 and frozen source package.", fontsize=9, color=MUTED, linespacing=1.7)
fig.text(.06, .040, "This is a comparison of the cited sources, not a claim of a worldwide record or independent verification of the entire manuscript.", fontsize=9, color=MUTED)
args.output.parent.mkdir(parents=True, exist_ok=True)
for suffix in ("png", "svg"):
    fig.savefig(args.output.with_suffix("."+suffix), dpi=200, facecolor=BG)
args.output.with_suffix(".json").write_text(json.dumps({"candidate_theta": str(target), "accepted_best_theta": str(fraction(best)),
    "difference_exact": str(gain), "relative_gain_beyond_baseline_exact": str(relative_gain),
    "independent_native_lean_passed": verified, "tracker_acceptance": False,
    "catalogue_as_of": catalogue["as_of"], "retrieved_at": retrieved_at, "source_commit": summary["result"]["source_commit"]}, indent=2)+"\n")
print(args.output.with_suffix(".png"))

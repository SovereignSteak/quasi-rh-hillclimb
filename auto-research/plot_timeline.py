"""Timeline of the best quasi-RH boundary, from OpenAI's 7/8 preprint to the current
QuasiRiemannTracker record, plus this repo's conditional nested-level results.
Writes graphs/timeline.png and graphs/timeline.csv.

Sources: the tracker's submissions/*/metadata.json and its admission-records branch
(theta_exact and first verification time of each admitted record). Only records that
improved on the best bound at the time are plotted. Every point is labeled with its
contributor; the crowded Oct 13-20 stretch is labeled in a column with leader lines.
"""
import csv
import os
from datetime import datetime
from fractions import Fraction as Fr

import matplotlib
matplotlib.use("Agg")
import matplotlib.dates as mdates
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker

SURF, INK, INK2, MUTED, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#8a8984", "#e6e5e0"
BLUE, ORANGE, ORANGE_TEXT = "#2a78d6", "#eb6834", "#b5461a"   # validated pair; darker orange for text
plt.rcParams.update({"font.family": ["Inter", "DejaVu Sans"], "font.size": 11,
                     "text.color": INK, "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2})

# (time UTC, contributor, theta, short theta label)
RECORDS = [
    ("2026-09-30 12:00", "OpenAI (preprint)", Fr(7, 8), "7/8"),
    ("2026-10-08 00:00", "Argonaut Math", Fr(3499999, 4000000), "0.87499975"),
    ("2026-10-08 16:18", "Baiying Liu", Fr(874957069799168740018340006959, 10**30), "0.8749571"),
    ("2026-10-09 11:37", "Tim Gehrunger / ProofCouncil", Fr(874957019421, 10**12), "0.8749570"),
    ("2026-10-10 13:35", "Akash Levy", Fr(10499, 12000), "10499/12000"),
    ("2026-10-10 16:09", "Hailey Collet", Fr(683505193, 781250000), "0.8748866"),
    ("2026-10-13 06:44", "nielstron", Fr(87487, 100000), "0.87487"),
    ("2026-10-13 13:04", "Kari Roegnvaldsson", Fr(4374347, 5000000), "0.8748694"),
    ("2026-10-13 14:41", "Kari Roegnvaldsson", Fr(87486797, 10**8), "0.87486797"),
    ("2026-10-13 18:43", "Hailey Collet", Fr(874861, 10**6), "0.874861"),
    ("2026-10-14 10:07", "Zhongpai Gao", Fr(4374299, 5000000), "0.8748598"),
    ("2026-10-14 22:53", "timbalud", Fr(8748559, 10**7), "0.8748559"),
    ("2026-10-15 03:53", "DaysSky", Fr(437423, 500000), "0.874846"),
    ("2026-10-15 05:29", "Zhongpai Gao", Fr(21871, 25000), "0.87484"),
    ("2026-10-16 16:03", "Zhongpai Gao", Fr(218709, 250000), "0.874836"),
    ("2026-10-17 11:32", "Zhongpai Gao", Fr(87483, 100000), "0.87483"),
    ("2026-10-20 00:51", "Sil", Fr(874828524351, 10**12), "0.8748285"),
    ("2026-10-20 01:49", "ArviFoxy (PR #67)", Fr(174963413, 200000000), "0.874817065"),
    ("2026-10-20 23:14", "Zhongpai Gao · PR #68 (verified record)", Fr(8748087, 10**7), "0.8748087"),
]
CONDITIONAL = [   # only results that beat every earlier bound (Lean or conditional); label: gain vs the Lean record when posted
    ("2026-10-20 15:07", "rohanarun · 3 levels (conditional)", Fr(874812431, 10**9), "≤ 0.874812431  (−4.6·10⁻⁶)"),
    ("2026-10-20 15:39", "rohanarun · 4 levels (conditional)", Fr(437405141, 500000000), "≤ 0.874810282  (−6.8·10⁻⁶)"),
    ("2026-10-20 17:18", "Sudarsh3301 · 6 levels (conditional)", Fr(874809989, 10**9), "≤ 0.874809989  (−7.1·10⁻⁶)"),
    ("2026-10-21 11:59", "rohanarun · 6 stages on PR #68 (cond.)", Fr(874807999, 10**9), "≤ 0.874807999  (−7.0·10⁻⁷)"),
    ("2026-10-21 13:58", "rohanarun · 6 stages, PR #68's own β (cond.)", Fr(874807887, 10**9), "≤ 0.874807887  (−8.1·10⁻⁷)"),
]
# Complete Lean proof submitted, independent tracker verification still pending (tracker PR #69, hillclimb PR #8)
PENDING = [
    ("2026-10-21 19:58", "Hailey Collet · CURRENT LEADER (Lean, verification pending)", Fr(8747729897, 10**10),
     "0.8747729897  (−3.6·10⁻⁵)"),
]
PURPLE, PURPLE_TEXT = "#7b4fc9", "#5b2fa8"


def ts(s):
    return datetime.strptime(s, "%Y-%m-%d %H:%M")


t = [ts(r[0]) for r in RECORDS]
y = [float(r[2]) for r in RECORDS]
tc = [ts(r[0]) for r in CONDITIONAL]
yc = [float(r[2]) for r in CONDITIONAL]
tp = [ts(r[0]) for r in PENDING]
yp = [float(r[2]) for r in PENDING]

fig = plt.figure(figsize=(15, 11), facecolor=SURF)
fig.text(0.05, 0.955, "Quasi-RH: the zero-free boundary θ over time", fontsize=17, weight="bold")
fig.text(0.05, 0.912, "Best all-moduli Dirichlet boundary (zero-free for Re s > θ). Lower is better. "
         "Blue: Lean-verified records. Purple: complete Lean proof submitted, independent verification pending.\n"
         "Orange: conditional, not Lean-verified. Brackets: gain vs the Lean record when posted.",
         fontsize=11, color=INK2)
ax = fig.add_axes([0.075, 0.47, 0.62, 0.43], facecolor=SURF)     # full history
zx = fig.add_axes([0.075, 0.16, 0.50, 0.22], facecolor=SURF)     # Oct 20-22 zoom, upper band
zb = fig.add_axes([0.075, 0.075, 0.50, 0.06], facecolor=SURF)     # lower band (broken y axis)

ZOOM_FROM = datetime(2026, 10, 19, 18)
end = datetime(2026, 10, 22, 6)
# Overall best bound so far (Lean or conditional). Blue = held by a Lean record, dashed orange =
# held by a conditional result. Every dot sits on a corner of this one line.
events = sorted([(tt, yy, "lean") for tt, yy in zip(t, y)] + [(tt, yy, "cond") for tt, yy in zip(tc, yc)]
                + [(tt, yy, "pending") for tt, yy in zip(tp, yp)])
segs, best, holder = [], None, None      # (x0, x1, y_level, conditional) horizontal pieces + vertical drops
for k, (tt, yy, cond) in enumerate(events):
    if best is not None and yy >= best:
        continue
    segs.append(("v", tt, best, yy, cond))
    best, holder = yy, cond
    nxt = next((e[0] for e in events[k + 1:] if e[1] < best), end)
    segs.append(("h", tt, nxt, best, cond))

for a_ in (ax, zx, zb):
    for s in segs:
        st = {"cond": dict(color=ORANGE, lw=1.8, ls=(0, (3, 2))), "lean": dict(color=BLUE, lw=2),
              "pending": dict(color=PURPLE, lw=1.8, ls=(0, (1, 1.5)))}[s[4]]
        if s[0] == "h":
            a_.plot([s[1], s[2]], [s[3], s[3]], zorder=2, solid_capstyle="butt", **st)
        elif s[2] is not None:
            a_.plot([s[1], s[1]], [s[2], s[3]], zorder=2, **st)
    a_.scatter(t, y, s=46, color=BLUE, edgecolor=SURF, linewidth=2, zorder=3)
    a_.scatter(tc, yc, s=70, facecolor=SURF, edgecolor=ORANGE, linewidth=2.2, zorder=4)
    a_.scatter(tp, yp, s=80, marker="D", facecolor=SURF, edgecolor=PURPLE, linewidth=2.2, zorder=4)
    a_.grid(axis="y", color=GRID, lw=0.8)
    a_.set_axisbelow(True)
    for s in ("left", "right", "top"):
        a_.spines[s].set_visible(False)
    a_.spines["bottom"].set_color(GRID)
    a_.tick_params(length=0)


def column(a_, pts, x, top, bottom, fs=9.5):
    """Label column with leader lines; pts sorted by theta (monotone in time, so no crossings)."""
    pts = sorted(pts, key=lambda r: -r[1])
    stp = (top - bottom) / max(len(pts) - 1, 1)
    for k, (tx, yy, label, cond) in enumerate(pts):
        a_.annotate(label, (tx, yy), xytext=(x, top - k * stp), textcoords="data", ha="left", va="center",
                    annotation_clip=False, fontsize=fs,
                    color={"cond": ORANGE_TEXT, "pending": PURPLE_TEXT}.get(cond, INK),
                    weight="normal" if cond in (False, "lean") else "bold",
                    arrowprops=dict(arrowstyle="-", color={"cond": ORANGE, "pending": PURPLE}.get(cond, MUTED),
                                    lw=0.7, shrinkA=3, shrinkB=4,
                                    relpos=(0, 0.5)))


# top panel: early labels beside the points, Oct 13-17 in a column
EARLY = {0: (10, -16, "left"), 1: (-12, 14, "right"), 2: (-12, 0, "right"),
         3: (12, 14, "left"), 4: (-12, 0, "right"), 5: (-12, -12, "right")}
for i, (dx, dy, ha) in EARLY.items():
    ax.annotate(f"{RECORDS[i][1]}  {RECORDS[i][3]}", (t[i], y[i]), xytext=(dx, dy),
                textcoords="offset points", ha=ha, va="center", fontsize=9.5, color=INK,
                arrowprops=dict(arrowstyle="-", color=MUTED, lw=0.7, shrinkA=0, shrinkB=4))
mid = [(t[i], y[i], f"{RECORDS[i][1]}  {RECORDS[i][3]}", False) for i in range(6, len(RECORDS)) if t[i] < ZOOM_FROM]
column(ax, mid, datetime(2026, 10, 22, 12), 0.874905, 0.874835)
ZY0, ZY1 = 0.874768, 0.874832
ax.add_patch(plt.Rectangle((mdates.date2num(ZOOM_FROM), ZY0), mdates.date2num(end) - mdates.date2num(ZOOM_FROM),
                           ZY1 - ZY0, fill=False, ec=MUTED, lw=0.9, ls=(0, (2, 2)), zorder=1))
ax.annotate("Oct 20–22: zoomed below", (ZOOM_FROM, ZY0), xytext=(-8, 0), textcoords="offset points",
            ha="right", va="center", fontsize=9, color=MUTED)
ax.set_ylim(0.874760, 0.875025)
ax.yaxis.set_major_formatter(mticker.FormatStrFormatter("%.5f"))
ax.set_xlim(datetime(2026, 9, 29), end)
ax.set_xticks([datetime(2026, 9, 30)] + [datetime(2026, 10, d) for d in (3, 6, 9, 12, 15, 18, 21)])
ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
ax.set_ylabel("θ")

# bottom panel: the last two days
recent = [(t[i], y[i], f"{RECORDS[i][1]}  {RECORDS[i][3]}", False) for i in range(len(RECORDS)) if t[i] >= ZOOM_FROM]
recent += [(tc[k], yc[k], f"{CONDITIONAL[k][1]}  {CONDITIONAL[k][3]}", "cond") for k in range(len(CONDITIONAL))]
column(zx, recent, end + (end - ZOOM_FROM) * 0.04, 0.874829, 0.874806)
low = [(tp[k], yp[k], f"{PENDING[k][1]}  {PENDING[k][3]}", "pending") for k in range(len(PENDING))]
column(zb, low, end + (end - ZOOM_FROM) * 0.04, yp[0], yp[0])
for a_ in (zx, zb):
    a_.set_xlim(ZOOM_FROM, end)
    a_.yaxis.set_major_formatter(mticker.FormatStrFormatter("%.6f"))
zx.set_ylim(0.874805, ZY1)
zb.set_ylim(0.874770, 0.874776)
zb.set_yticks([0.874770, 0.874775])
zx.set_xticks([])
zb.xaxis.set_major_locator(mdates.HourLocator(byhour=[0, 12]))
zb.xaxis.set_major_formatter(mdates.DateFormatter("%b %d, %H:%M"))
zx.spines["bottom"].set_visible(False)
for a_, yv in ((zx, 0.0), (zb, 1.0)):     # break marks on the y axis
    a_.plot([-0.012, 0.012], [yv - 0.03, yv + 0.03] if a_ is zx else [yv - 0.12, yv + 0.12],
            transform=a_.transAxes, color=MUTED, lw=1, clip_on=False)
zx.set_ylabel("θ")
zx.set_title("Oct 20–22 (UTC)", fontsize=11, color=INK2, loc="left", pad=8)

fig.text(0.05, 0.015, "Sources: QuasiRiemannTracker submissions and admission records (first verification times); "
         "OpenAI preprint dated Sep 30, 2026.\n"
         "Only bounds that beat every earlier bound at the time are shown. Conditional results: "
         "github.com/rohanarun/quasi-rh-hillclimb (depth3/PROOF.md). Pending: tracker PR #69, hillclimb PR #8.", fontsize=8.5, color=MUTED)

out_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "graphs")
os.makedirs(out_dir, exist_ok=True)
fig.savefig(os.path.join(out_dir, "timeline.png"), dpi=200, facecolor=SURF)
with open(os.path.join(out_dir, "timeline.csv"), "w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["time_utc", "contributor", "theta_exact", "theta_decimal", "status"])
    for r in RECORDS:
        w.writerow([r[0], r[1], str(r[2]), f"{float(r[2]):.12f}", "Lean-verified record"])
    for r in CONDITIONAL:
        w.writerow([r[0], r[1], str(r[2]), f"{float(r[2]):.12f}", "conditional, not Lean-verified"])
    for r in PENDING:
        w.writerow([r[0], r[1], str(r[2]), f"{float(r[2]):.12f}", "Lean proof submitted, verification pending"])
print("wrote graphs/timeline.png and graphs/timeline.csv")

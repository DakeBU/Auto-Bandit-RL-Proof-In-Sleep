#!/usr/bin/env python3
"""Render ABRL Lean route roadmap diagrams as PNG assets.

The diagrams are intentionally static and spacious.  They are documentation
artifacts for humans and prompt packets for agents, not proof certificates.
"""

from __future__ import annotations

import json
import textwrap
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch


ROOT = Path(__file__).resolve().parents[1]
ROADMAP = ROOT / "research-wiki" / "theory-tree" / "lean-route-roadmap.json"
ASSETS = ROOT / "docs" / "assets"

INK = "#24313f"
MUTED = "#65758a"
BLUE = "#1f5f99"
GREEN = "#2f7d5c"
RED = "#b54747"
AMBER = "#b7791f"
GRAY = "#edf2f7"
LINE = "#9aa9b8"
PALE_BLUE = "#e8f1fb"
PALE_GREEN = "#e9f6ef"
PALE_RED = "#fdeaea"
PALE_AMBER = "#fff4da"


def load() -> dict:
    return json.loads(ROADMAP.read_text(encoding="utf-8"))


def wrap(text: str, width: int = 26) -> str:
    return "\n".join(textwrap.wrap(text, width=width, break_long_words=False))


def add_box(ax, x, y, w, h, text, *, fc=GRAY, ec=LINE, color=INK, fontsize=10, weight="normal"):
    patch = FancyBboxPatch(
        (x, y),
        w,
        h,
        boxstyle="round,pad=0.018,rounding_size=0.035",
        facecolor=fc,
        edgecolor=ec,
        linewidth=1.3,
    )
    ax.add_patch(patch)
    ax.text(
        x + w / 2,
        y + h / 2,
        text,
        ha="center",
        va="center",
        fontsize=fontsize,
        color=color,
        fontweight=weight,
        linespacing=1.18,
    )
    return patch


def arrow(ax, start, end, *, color=LINE, rad=0.0):
    ax.add_patch(
        FancyArrowPatch(
            start,
            end,
            arrowstyle="-|>",
            mutation_scale=12,
            linewidth=1.25,
            color=color,
            shrinkA=8,
            shrinkB=8,
            connectionstyle=f"arc3,rad={rad}",
        )
    )


def base_canvas(title: str, subtitle: str, filename: str, *, size=(16, 9)):
    fig, ax = plt.subplots(figsize=size, dpi=180)
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis("off")
    ax.text(0.035, 0.955, title, fontsize=21, fontweight="bold", color=INK, va="top")
    ax.text(0.035, 0.905, subtitle, fontsize=10.5, color=MUTED, va="top")
    ax.plot([0.035, 0.965], [0.875, 0.875], color="#d7dee8", lw=1.2)
    path = ASSETS / filename
    return fig, ax, path


def save(fig, path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.16)
    plt.close(fig)
    print(path.relative_to(ROOT))


def route_by_id(data: dict, route_id: str) -> dict:
    for route in data["routes"]:
        if route["id"] == route_id:
            return route
    raise KeyError(route_id)


def draw_global(data: dict):
    fig, ax, path = base_canvas(
        "ABRL Lean Tree: Shared Roots And Route Families",
        "All theorem routes start from reusable Mathlib-ready leaves; proof weapons only guide planning.",
        "lean_tree_global.png",
        size=(18, 10),
    )
    spine_y = [0.75, 0.61, 0.47, 0.33, 0.19]
    spine_colors = [PALE_BLUE, PALE_GREEN, PALE_AMBER, PALE_RED, "#eef0ff"]
    for i, spine in enumerate(data["shared_spines"]):
        y = spine_y[i]
        add_box(ax, 0.05, y, 0.28, 0.09, wrap(spine["title"], 30), fc=spine_colors[i], ec=[BLUE, GREEN, AMBER, RED, "#6264a7"][i], fontsize=9.5, weight="bold")
        compiled = "\n".join(spine["compiled_modules"][:3])
        add_box(ax, 0.37, y, 0.23, 0.09, wrap(compiled, 28), fc="white", ec=LINE, fontsize=7.6)
        downstream = "\n".join(spine["downstream_routes"][:4])
        add_box(ax, 0.65, y, 0.28, 0.09, wrap(downstream, 32), fc="white", ec=LINE, fontsize=7.4)
        arrow(ax, (0.33, y + 0.045), (0.37, y + 0.045))
        arrow(ax, (0.60, y + 0.045), (0.65, y + 0.045))
    add_box(ax, 0.05, 0.05, 0.88, 0.065, "Reviewer invariant: one leaf, exact statement, explicit contracts, stable proof route, no uncompiled dependency.", fc="#f7fafc", ec=INK, fontsize=10.5, weight="bold")
    save(fig, path)


def draw_route(data: dict, route_id: str, filename: str, title: str, subtitle: str, *, color=BLUE, fill=PALE_BLUE):
    route = route_by_id(data, route_id)
    fig, ax, path = base_canvas(title, subtitle, filename, size=(18, 10))
    layers = route.get("layers", [])
    left = 0.045
    top = 0.78
    col_w = 0.20
    gap = 0.035
    for i, layer in enumerate(layers):
        x = left + i * (col_w + gap)
        add_box(ax, x, top, col_w, 0.06, wrap(layer["name"], 24), fc=fill, ec=color, fontsize=10.5, weight="bold")
        y = top - 0.11
        for node in layer.get("nodes", [])[:6]:
            add_box(ax, x, y, col_w, 0.062, wrap(node, 24), fc="white", ec=LINE, fontsize=8.4)
            y -= 0.084
        if i < len(layers) - 1:
            arrow(ax, (x + col_w, top + 0.03), (x + col_w + gap, top + 0.03), color=color)
    compiled = "\n".join(f"- {item}" for item in route.get("compiled_local_core", [])[:6])
    leaves = "\n".join(f"- {item}" for item in route.get("next_mathlib_ready_leaves", [])[:6])
    add_box(ax, 0.045, 0.08, 0.42, 0.17, "Compiled core\n" + wrap(compiled, 56), fc="#f8fbff", ec=color, fontsize=7.6)
    add_box(ax, 0.505, 0.08, 0.42, 0.17, "Next Mathlib-ready leaves\n" + wrap(leaves, 56), fc="#fffdfa", ec=AMBER, fontsize=7.6)
    ax.text(0.05, 0.025, "Reviewer gate: " + route.get("reviewer_gate", ""), fontsize=8.8, color=RED)
    save(fig, path)


def draw_cluster(data: dict, route_ids: list[str], filename: str, title: str, subtitle: str):
    fig, ax, path = base_canvas(title, subtitle, filename, size=(18, 10))
    positions = [
        (0.055, 0.62),
        (0.375, 0.62),
        (0.695, 0.62),
        (0.055, 0.31),
        (0.375, 0.31),
        (0.695, 0.31),
    ]
    for idx, route_id in enumerate(route_ids):
        route = route_by_id(data, route_id)
        x, y = positions[idx]
        add_box(ax, x, y + 0.18, 0.25, 0.07, route["id"].replace("ROUTE-", ""), fc=PALE_BLUE if idx % 2 == 0 else PALE_GREEN, ec=BLUE if idx % 2 == 0 else GREEN, fontsize=8.7, weight="bold")
        leaves = route.get("next_mathlib_ready_leaves", [])[:4]
        text = route["title"] + "\n\n" + "\n".join(f"- {leaf}" for leaf in leaves)
        add_box(ax, x, y, 0.25, 0.17, wrap(text, 36), fc="white", ec=LINE, fontsize=7.4)
    add_box(
        ax,
        0.08,
        0.08,
        0.84,
        0.075,
        wrap(
            "Shared reviewer rule: watchlist routes may guide memory and theorem-card planning, but lower agents receive only exact compiled/import-target leaves.",
            112,
        ),
        fc="#f7fafc",
        ec=INK,
        fontsize=9.2,
        weight="bold",
    )
    save(fig, path)


def draw_agent_loop(data: dict):
    fig, ax, path = base_canvas(
        "ABRL Hierarchical Sleep-Run Loop",
        "Upper proposes routes; middle turns them into leaf packets; lower proves one leaf; reviewer controls drift and memory.",
        "agent_screen_loop.png",
        size=(16, 9),
    )
    boxes = {
        "upper": (0.08, 0.60, "Upper\nroute population\nproof-weapon ideas"),
        "middle": (0.38, 0.60, "Middle\nsource grounding\nleaf packets"),
        "lower": (0.68, 0.60, "Lower\none Lean leaf\nor blocker"),
        "reviewer": (0.38, 0.30, "Reviewer\nno drift\ncontracts visible"),
        "memory": (0.08, 0.30, "Memory\ncards, failures\ncompiled decls"),
        "check": (0.68, 0.30, "Gate\nlake build\nTests, scans")
    }
    for name, (x, y, text) in boxes.items():
        fc = {"upper": PALE_BLUE, "middle": PALE_GREEN, "lower": PALE_AMBER, "reviewer": PALE_RED, "memory": "white", "check": "white"}[name]
        ec = {"upper": BLUE, "middle": GREEN, "lower": AMBER, "reviewer": RED, "memory": LINE, "check": INK}[name]
        add_box(ax, x, y, 0.22, 0.13, text, fc=fc, ec=ec, fontsize=10.5, weight="bold")
    arrow(ax, (0.30, 0.665), (0.38, 0.665), color=BLUE)
    arrow(ax, (0.60, 0.665), (0.68, 0.665), color=GREEN)
    arrow(ax, (0.79, 0.60), (0.79, 0.43), color=AMBER)
    arrow(ax, (0.68, 0.365), (0.60, 0.365), color=INK)
    arrow(ax, (0.49, 0.43), (0.49, 0.60), color=RED)
    arrow(ax, (0.38, 0.365), (0.30, 0.365), color=RED)
    arrow(ax, (0.19, 0.43), (0.19, 0.60), color=LINE)
    add_box(ax, 0.08, 0.11, 0.82, 0.08, "Screen loop command surface: route-plan -> blueprint-refresh -> memory-refresh -> sleep-run --execute -> check -> reviewer compression.", fc="#f7fafc", ec=INK, fontsize=10.2, weight="bold")
    save(fig, path)


def main() -> int:
    data = load()
    draw_global(data)
    draw_route(
        data,
        "ROUTE-ETC-FINITE-STOCHASTIC",
        "lean_tree_etc.png",
        "ETC Formalization Route",
        "Deterministic counts, wrong-commit probability, bounded reward source, and regret assembly.",
        color=GREEN,
        fill=PALE_GREEN,
    )
    draw_route(
        data,
        "ROUTE-UCB1-FINITE-STOCHASTIC",
        "lean_tree_ucb.png",
        "UCB1 Formalization Route",
        "What exists now is bad-event summability; the UCB index and logarithmic count proof are the next leaves.",
        color=BLUE,
        fill=PALE_BLUE,
    )
    draw_route(
        data,
        "ROUTE-TSALLIS-INF-FTRL",
        "lean_tree_tsallis_ftrl.png",
        "Tsallis-INF / FTRL Route",
        "The regularizer surface exists; convexity, stability, and self-bounding remain the Mathlib-ready leaves.",
        color=AMBER,
        fill=PALE_AMBER,
    )
    draw_cluster(
        data,
        [
            "ROUTE-THOMPSON-BAYES",
            "ROUTE-LINEAR-OFUL",
            "ROUTE-RL-UCBVI",
            "ROUTE-BWK-RESOURCE",
            "ROUTE-PREFERENCE-DUELING",
            "ROUTE-LLM-FEDERATED-NEURAL",
        ],
        "lean_tree_contextual_rl_watchlist.png",
        "Contextual, Bayesian, RL, Resource, Preference, And Modern Routes",
        "These routes share kernels, filtrations, posterior/trajectory laws, and finite bookkeeping before final theorem work.",
    )
    draw_agent_loop(data)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

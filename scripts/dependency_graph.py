#!/usr/bin/env python3
"""Draw the dependency graph of the SgLVResilience Lean files.

Scans SgLVResilience/*.lean for theorem/def/structure declarations and, inside each
declaration's source, for references to the other declarations of this project.
Mathlib names are ignored. An edge A -> B means the source of A mentions B.

Usage (from the repository root, needs Graphviz `dot`):
    python3 scripts/dependency_graph.py
Writes
  docs/dependency-graph.dot, docs/dependency-graph.svg, docs/dependency-graph-dark.svg
      static proof-structure graph for the README (definitions and hypotheses omitted);
  docs/index.html
      interactive page served by GitHub Pages, built from
      scripts/dependency_graph_template.html. Graphviz sizes the boxes with the fonts it finds,
      so install Inter and JetBrains Mono first for a tidy result.
"""
import json
import glob
import html
import os
import re
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "SgLVResilience")
OUT = os.path.join(ROOT, "docs")

# Results that appear in the paper, with their numbering there.
PAPER = {
    "hasFDerivAt_drift": "(2.13) Jacobian",
    "linearization_isLittleO": "(2.11)–(2.13)",
    "linearization_unique": "(2.12)–(2.13) unique",
    "jac_diag_ne_printed": "(2.13) diagonal",
    "vec_momentRHS": "(2.19) ⇔ (2.21)",
    "hasDerivAt_vec": "(2.21)",
    "trace_momentRHS": "W′(t)",
    "hasDerivAt_W": "W′(t)",
    "rIns_eq": "R_ins",
    "rAve_eq": "R_ave",
    "rInf_eq_zero": "R_∞ = 0",
    "TwoSpecies.noiseCov_posDef_iff'": "Σ pos. def.",
    "TwoSpecies.jac_two": "(3.5)",
    "TwoSpecies.msMatrix_two": "S (Sec. 3.1)",
    "TwoSpecies.msForcing_two": "T (Sec. 3.1)",
    "TwoSpecies.mutualistic_drift_pos": "mutualism",
    "TwoSpecies.tightness": "(3.4)",
    "zeroFlux": "π stationary",
    "integrableOn_statDensity_iff": "π exists",
    "integral_id_gammaMeasure": "Gamma mean",
    "TwoSpecies.lyap₁_μ₁": "λ₁(μ₁)",
    "TwoSpecies.lyap₂_μ₁": "λ₂(μ₁)",
    "TwoSpecies.lyap₁_μ₂": "λ₁(μ₂)",
    "TwoSpecies.lyap₂_μ₂": "λ₂(μ₂)",
    "TwoSpecies.assumption4_C2i": "C2(i)",
    "TwoSpecies.assumption4_C3i": "C3(i)",
    "TwoSpecies.assumption4_C4i": "C4(i)",
}
FILES = ["Boundary", "TwoSpecies", "Resilience", "Moments", "Basic"]  # top-to-bottom cluster order
# Short descriptions shown under definitions in the interactive page.
HYP = {
    "percap": "fᵢ",
    "drift": "hᵢ",
    "jac": "∂h/∂x",
    "jacCLM": "∂h/∂x",
    "noiseCov": "Σ = ΓΓᵀ",
    "momentRHS": "(2.19)",
    "msMatrix": "S",
    "msForcing": "T",
    "rIns": "R_ins",
    "rAve": "R_ave",
    "rC": "R_c",
    "rInf": "R_∞",
    "spectralAbscissa": "α(S)",
    "TwoSpecies": "model (3.1)",
    "statDensity": "x^{k-1}e^{-rx}",
    "TwoSpecies.lyap₁": "λ₁(μ)",
    "TwoSpecies.lyap₂": "λ₂(μ)",
}
SOURCE_URL = "https://github.com/magbenji/sglv-resilience-lean/blob/main/SgLVResilience/"

THEMES = {
    "light": dict(bg="#ffffff", fg="#1d2126", muted="#5d646d", line="#d6d8d2", edge="#7d848c",
                  node="#eef0ec", paper="#8a5a12", paper_fill="#f6ead2"),
    "dark": dict(bg="#0d1117", fg="#e6e8ea", muted="#9aa2ab", line="#353b42", edge="#8a929b",
                 node="#262b31", paper="#e4b464", paper_fill="#3a2d17"),
}

DECL = re.compile(r"^(?:private |protected |noncomputable )*(theorem|lemma|def|structure|abbrev)\s+([^\s({\[:]+)", re.M)
NS = re.compile(r"^(namespace|end)\s+(\S+)", re.M)


def strip_comments(s):
    s = re.sub(r"/-.*?-/", lambda m: re.sub(r"[^\n]", " ", m.group(0)), s, flags=re.S)
    return re.sub(r"--[^\n]*", "", s)


def scan():
    decls = []
    for path in sorted(glob.glob(os.path.join(SRC, "*.lean"))):
        fname = os.path.basename(path)[:-5]
        s = strip_comments(open(path, encoding="utf-8").read())
        ms = list(DECL.finditer(s))
        for i, m in enumerate(ms):
            stack = []
            for n in NS.finditer(s[: m.start()]):
                if n.group(1) == "namespace":
                    stack.append(n.group(2))
                elif stack and stack[-1] == n.group(2):
                    stack.pop()
            prefix = [x for x in stack if x != "SgLVResilience"]
            end = ms[i + 1].start() if i + 1 < len(ms) else len(s)
            decls.append(dict(name=".".join(prefix + [m.group(2)]), ns=".".join(prefix), file=fname, kind=m.group(1),
                              line=s[: m.start()].count("\n") + 1, body=s[m.end():end]))
    names = {d["name"] for d in decls}
    short = {}
    for n in names:
        short.setdefault(n.split(".")[-1], set()).add(n)
    for d in decls:
        deps = set()
        for t in re.findall(r"[^\W\d][\w'.₀-₉]*", d["body"]):
            if t in names:
                deps.add(t)
            # unqualified names inside a nested namespace (e.g. `Example21`)
            for q in {t, t.split(".")[0]}:
                if d["ns"] and f'{d["ns"]}.{q}' in names:
                    deps.add(f'{d["ns"]}.{q}')
            parts = t.split(".")
            if len(parts) > 1 and parts[0] in names:
                deps.add(parts[0])
            for j, p in enumerate(parts):
                for n in short.get(p, ()):
                    if j > 0 or "." not in n:
                        deps.add(n)
        for p in re.findall(r"\.([^\W\d][\w'₀-₉]*)", d["body"]):
            deps.update(short.get(p, ()))
        deps.discard(d["name"])
        d["deps"] = sorted(deps)
    return decls


def to_dot(decls, th):
    is_def = {d["name"]: d["kind"] in ("structure", "def", "abbrev") for d in decls}
    edges = [(d["name"], t) for d in decls if not is_def[d["name"]]
             for t in d["deps"] if not is_def[t]]
    linked = {a for a, _ in edges} | {b for _, b in edges}
    # The static graph leaves out helper lemmas that neither use nor are used by another lemma.
    shown = {d["name"] for d in decls
             if not is_def[d["name"]] and (d["name"] in PAPER or d["name"] in linked)}
    has_in = {b for a, b in edges if a in shown and b in shown}
    out = [
        "digraph SgLVResilience {",
        f'  rankdir=TB; newrank=true; nodesep=0.25; ranksep=0.45; bgcolor="{th["bg"]}"; pad=0.2;',
        f'  node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=11, margin="0.12,0.05",'
        f' color="{th["edge"]}", fillcolor="{th["node"]}", fontcolor="{th["fg"]}"];',
        f'  edge [color="{th["edge"]}", arrowsize=0.6];',
    ]
    tops = {}
    for f in FILES:
        out.append(f'  subgraph cluster_{f} {{ label="{f}.lean"; labeljust=l; style=rounded; '
                   f'color="{th["line"]}"; fontname="Courier"; fontsize=11; fontcolor="{th["muted"]}";')
        tops[f] = []
        for d in decls:
            n = d["name"]
            if d["file"] != f or n not in shown:
                continue
            if n not in has_in:
                tops[f].append(n)
            lab = f'<<FONT FACE="Courier">{html.escape(n)}</FONT>'
            extra = ""
            if n in PAPER:
                lab += f'<BR/><FONT POINT-SIZE="9">{PAPER[n]}</FONT>'
                extra = f', color="{th["paper"]}", fillcolor="{th["paper_fill"]}", penwidth=1.6'
            out.append(f'    "{n}" [label={lab}>{extra}];')
        out.append("  }")
    for a, b in edges:
        if a in shown and b in shown:
            out.append(f'  "{a}" -> "{b}";')
    # layout only: wrap each file's top-level results into rows of 4 and stack the files
    W = 4
    has_out = {a for a, b in edges if a in shown and b in shown}
    prev_sinks = []
    for f in FILES:
        t = tops[f]
        for i in range(len(t) - W):
            out.append(f'  "{t[i]}" -> "{t[i + W]}" [style=invis];')
        for snk in prev_sinks:
            for n in t[:W]:
                out.append(f'  "{snk}" -> "{n}" [style=invis];')
        mine = [d["name"] for d in decls if d["file"] == f and d["name"] in shown]
        if mine:
            prev_sinks = [n for n in mine if n not in has_out]
    out.append("}")
    return "\n".join(out) + "\n"


def interactive_svg(decls, with_defs):
    """SVG whose colours come from CSS classes, so the page can theme it."""
    is_def = {d["name"]: d["kind"] in ("structure", "def", "abbrev") for d in decls}

    def cls(n):
        return "paper" if n in PAPER else ("defn" if is_def[n] else "lemma")

    out = [
        "digraph G {",
        '  rankdir=TB; newrank=true; nodesep=0.25; ranksep=0.45; bgcolor="transparent"; fontname="Inter";',
        '  node [shape=box, style="rounded,filled", fontname="Inter", margin="0.12,0.05", penwidth=1.2];',
        "  edge [arrowsize=0.6, penwidth=1.0];",
    ]
    for f in FILES:
        out.append(f'  subgraph cluster_{f} {{ label="{f}.lean"; fontname="JetBrains Mono"; fontsize=11; '
                   'labeljust=l; style="rounded"; penwidth=1;')
        for d in decls:
            n = d["name"]
            if d["file"] != f or (is_def[n] and not with_defs):
                continue
            lab = f'<<FONT FACE="JetBrains Mono, monospace" POINT-SIZE="11">{html.escape(n)}</FONT>'
            sub = PAPER.get(n) or HYP.get(n)
            if sub:
                lab += f'<BR/><FONT POINT-SIZE="9">{html.escape(sub)}</FONT>'
            out.append(f'    "{n}" [id="n-{n}", class="{cls(n)}", label={lab}>];')
        out.append("  }")
    for d in decls:
        for t in d["deps"]:
            if is_def[t] or is_def[d["name"]]:
                if with_defs:
                    out.append(f'  "{d["name"]}" -> "{t}" [id="e-{d["name"]}--{t}", class="dedge", style=dashed];')
            else:
                out.append(f'  "{d["name"]}" -> "{t}" [id="e-{d["name"]}--{t}", class="pedge"];')
    out.append("}")
    svg = subprocess.run(["dot", "-Tsvg"], input="\n".join(out), capture_output=True, text=True, check=True).stdout
    svg = svg[svg.index("<svg"):]
    svg = re.sub(r'<svg width="[^"]*" height="[^"]*"', '<svg role="img" aria-label="Dependency graph" class="graph"', svg, count=1)
    svg = re.sub(r"<!--.*?-->\n?", "", svg, flags=re.S)
    return re.sub(r"<title>[^<]*</title>", "", svg)


def write_html(decls):
    for d in decls:
        d["usedby"] = sorted(x["name"] for x in decls if d["name"] in x["deps"])
    rows = []
    for f in reversed(FILES):
        rows.append(f'<tr class="file"><td colspan="5">SgLVResilience/{f}.lean</td></tr>')
        for d in sorted((d for d in decls if d["file"] == f), key=lambda d: d["line"]):
            n = d["name"]
            ref = f'<span class="ref">{PAPER[n]}</span>' if n in PAPER else ""
            rows.append(
                f'<tr><td class="n">{html.escape(n)}{ref}</td><td>{d["kind"]}</td>'
                f'<td class="l"><a href="{SOURCE_URL}{f}.lean#L{d["line"]}" target="_blank" rel="noopener">{d["line"]}</a></td>'
                f'<td class="d">{html.escape(", ".join(d["deps"])) or "—"}</td>'
                f'<td class="d">{html.escape(", ".join(d["usedby"])) or "—"}</td></tr>')
    data = [{k: d[k] for k in ("name", "file", "kind", "line", "deps", "usedby")} for d in decls]
    page = open(os.path.join(ROOT, "scripts", "dependency_graph_template.html"), encoding="utf-8").read()
    for key, val in (("__PROOFS__", interactive_svg(decls, False)), ("__FULL__", interactive_svg(decls, True)),
                     ("__ROWS__", "\n".join(rows)), ("__DATA__", json.dumps(data, ensure_ascii=False)),
                     ("__PAPER__", json.dumps(PAPER)), ("__GH__", SOURCE_URL)):
        page = page.replace(key, val)
    open(os.path.join(OUT, "index.html"), "w", encoding="utf-8").write(page)


def main():
    decls = scan()
    os.makedirs(OUT, exist_ok=True)
    for theme, suffix in (("light", ""), ("dark", "-dark")):
        dot = to_dot(decls, THEMES[theme])
        if theme == "light":
            open(os.path.join(OUT, "dependency-graph.dot"), "w", encoding="utf-8").write(dot)
        svg = subprocess.run(["dot", "-Tsvg"], input=dot, capture_output=True, text=True, check=True).stdout
        open(os.path.join(OUT, f"dependency-graph{suffix}.svg"), "w", encoding="utf-8").write(svg)
    write_html(decls)
    open(os.path.join(OUT, ".nojekyll"), "w").close()
    print(f"{len(decls)} declarations; wrote docs/dependency-graph.dot, .svg, -dark.svg and docs/index.html")


if __name__ == "__main__":
    main()

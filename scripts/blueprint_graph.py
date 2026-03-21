#!/usr/bin/env python3
"""Generate a skeletal leanblueprint from selected Lean files/modules."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import site
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
GENERATED_DIR = REPO_ROOT / "blueprint" / "src" / "generated"

DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|scoped)\s+)*(?:(?:noncomputable)\s+)?"
    r"(def|lemma|theorem|structure|instance)\s+([A-Za-z0-9_'.«»]+)"
)
NONCOMP_DEF_RE = re.compile(
    r"^\s*(?:(?:private|protected|scoped)\s+)*noncomputable\s+def\s+([A-Za-z0-9_'.«»]+)"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.']+)\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_.']+))?\s*$")


@dataclass
class DeclInfo:
    name: str
    kind: str
    module: str
    file: Path
    line: int


def tex_escape(text: str) -> str:
    return (
        text.replace("\\", r"\textbackslash{}")
        .replace("_", r"\_")
        .replace("&", r"\&")
        .replace("%", r"\%")
        .replace("#", r"\#")
        .replace("{", r"\{")
        .replace("}", r"\}")
    )


def sanitize_label(kind: str, name: str) -> str:
    prefix = {
        "def": "def",
        "noncomputable def": "def",
        "lemma": "lem",
        "theorem": "thm",
        "structure": "str",
        "instance": "inst",
    }.get(kind, "decl")
    safe = re.sub(r"[^A-Za-z0-9]+", "-", name).strip("-")
    return f"{prefix}:{safe}"


def strip_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if depth == 0 and text.startswith("--", i):
          while i < len(text) and text[i] != "\n":
              i += 1
          continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        ch = text[i]
        out.append("\n" if depth > 0 and ch == "\n" else (ch if depth == 0 else " "))
        i += 1
    return "".join(out)


def resolve_target(target: str) -> tuple[str, Path]:
    maybe_path = (REPO_ROOT / target).resolve() if not Path(target).is_absolute() else Path(target)
    if maybe_path.exists():
        path = maybe_path
        rel = path.relative_to(REPO_ROOT)
        if rel.suffix != ".lean":
            raise SystemExit(f"target is not a Lean file: {target}")
        module = ".".join(rel.with_suffix("").parts)
        return module, path
    module = target
    path = REPO_ROOT / Path(*module.split(".")).with_suffix(".lean")
    if not path.exists():
        raise SystemExit(f"cannot resolve target as module or file: {target}")
    return module, path


def parse_declarations(module: str, path: Path) -> list[DeclInfo]:
    text = strip_comments(path.read_text())
    ns_stack: list[str] = []
    decls: list[DeclInfo] = []
    for line_no, line in enumerate(text.splitlines(), start=1):
        if m := NAMESPACE_RE.match(line):
            ns_stack.extend(m.group(1).split("."))
            continue
        if m := END_RE.match(line):
            if m.group(1):
                parts = m.group(1).split(".")
                if ns_stack[-len(parts):] == parts:
                    del ns_stack[-len(parts):]
            continue
        kind = None
        raw_name = None
        if m := NONCOMP_DEF_RE.match(line):
            kind = "noncomputable def"
            raw_name = m.group(1)
        elif m := DECL_RE.match(line):
            kind = m.group(1)
            raw_name = m.group(2)
        if kind is None or raw_name is None:
            continue
        if raw_name == ":":
            continue
        if "." in raw_name:
            fq_name = raw_name
        elif ns_stack:
            fq_name = ".".join(ns_stack + [raw_name])
        else:
            fq_name = raw_name
        decls.append(DeclInfo(name=fq_name, kind=kind, module=module, file=path, line=line_no))
    return decls


def lean_name_literal(name: str) -> str:
    components = ", ".join(f"`{part}" for part in name.split("."))
    return f"Name.fromComponents [{components}]"


def run_extract(modules: list[str], decl_names: list[str]) -> list[dict]:
    import_lines = "\n".join(f"import {module}" for module in modules)
    decl_name_exprs = ", ".join(lean_name_literal(name) for name in decl_names)
    source = f"""{import_lines}
import Lean.Elab.Command
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.Name

open Lean Core Elab Command

structure DeclDump where
  name : String
  module : String
  statementDeps : Array String
  bodyDeps : Array String
  directSorry : Bool
deriving ToJson

private def constType : ConstantInfo → Expr
  | .axiomInfo v => v.type
  | .defnInfo v => v.type
  | .thmInfo v => v.type
  | .opaqueInfo v => v.type
  | .quotInfo v => v.type
  | .ctorInfo v => v.type
  | .recInfo v => v.type
  | .inductInfo v => v.type

private def constValue? : ConstantInfo → Option Expr
  | .axiomInfo _ => none
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | .quotInfo _ => none
  | .ctorInfo _ => none
  | .recInfo _ => none
  | .inductInfo _ => none

private def uniqueStrings (xs : Array String) : Array String :=
  let (_, out) := xs.foldl
    (fun (acc : Std.HashSet String × Array String) x =>
      if acc.1.contains x then acc else (acc.1.insert x, acc.2.push x))
    ({{}}, #[])
  out

private def depsOfExpr (self : Name) (e : Expr) : Array String :=
  uniqueStrings <| (e.getUsedConstants.filterMap fun n =>
    if n == self then none else some n.toString)

private def dumpDecl (n : Name) (ci : ConstantInfo) :
    CoreM (Option DeclDump) := do
  let some mod ← findModuleOf? n | return none
  let ty := constType ci
  let statementDeps := depsOfExpr n ty
  let bodyDeps := uniqueStrings <|
    match constValue? ci with
    | none => #[]
    | some v => (depsOfExpr n v).filter fun dep => !statementDeps.contains dep
  let directSorry :=
    ty.getUsedConstants.contains ``sorryAx ||
      match constValue? ci with
      | none => false
      | some v => v.getUsedConstants.contains ``sorryAx
  return some {{
    name := n.toString
    module := mod.toString
    statementDeps
    bodyDeps
    directSorry
  }}

private def collectDecls (targetDecls : Array Name) : CoreM (Array DeclDump) := do
  let env ← getEnv
  targetDecls.foldlM (init := #[]) fun acc n => do
    let some ci := env.find? n | return acc
    match ← dumpDecl n ci with
    | some decl => return acc.push decl
    | none => return acc

elab "#blueprint_graph_extract" : command => do
  let targetDecls : Array Name := #[{decl_name_exprs}]
  let decls ← liftCoreM <| collectDecls targetDecls
  liftIO <| IO.println (Json.compress (toJson decls))

#blueprint_graph_extract
"""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=REPO_ROOT / "scripts", delete=False) as tmp:
        tmp.write(source)
        tmp_path = Path(tmp.name)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp_path.relative_to(REPO_ROOT))],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    finally:
        tmp_path.unlink(missing_ok=True)
    if proc.returncode != 0:
        raise SystemExit(proc.stderr.strip() or proc.stdout.strip() or "temporary extractor failed")
    return json.loads(proc.stdout)


def blueprint_usepackage_options(*, nonreduced: bool) -> str:
    options = ["dep_graph"]
    if nonreduced:
        options.append("nonreducedgraph")
    options.append("thms=definition+lemma+theorem")
    return ",".join(options)


def ensure_blueprint_scaffold(*, nonreduced: bool) -> None:
    (REPO_ROOT / "blueprint" / "src" / "macros").mkdir(parents=True, exist_ok=True)
    GENERATED_DIR.mkdir(parents=True, exist_ok=True)
    template_root = Path(tool_path("leanblueprint")).resolve().parent.parent / "lib" / "python" / "site-packages" / "leanblueprint" / "templates"
    if not template_root.exists():
        template_root = Path(site.getusersitepackages()) / "leanblueprint" / "templates"
    scaffold = {
        REPO_ROOT / "blueprint" / "src" / "content.tex":
            "% Autogenerated wrapper; edit around this if desired.\n\\input{generated/generated_content}\n",
        REPO_ROOT / "blueprint" / "src" / "print.tex":
            "\\documentclass{article}\n"
            "\\usepackage{amsthm}\n"
            f"\\usepackage[{blueprint_usepackage_options(nonreduced=nonreduced)}]{{blueprint}}\n"
            "\\input{macros/common}\n"
            "\\input{macros/print}\n"
            "\\title{Autogenerated Dependency Blueprint}\n"
            "\\author{}\n"
            "\\begin{document}\n"
            "\\maketitle\n"
            "\\input{content}\n"
            "\\end{document}\n",
        REPO_ROOT / "blueprint" / "src" / "web.tex":
            "\\documentclass{article}\n"
            "\\usepackage{amsthm}\n"
            f"\\usepackage[{blueprint_usepackage_options(nonreduced=nonreduced)}]{{blueprint}}\n"
            "\\input{macros/common}\n"
            "\\input{macros/web}\n"
            "\\begin{document}\n"
            "\\input{content}\n"
            "\\end{document}\n",
        REPO_ROOT / "blueprint" / "src" / "macros" / "common.tex":
            "% Shared blueprint macros and theorem environments.\n"
            "\\newtheorem{theorem}{Theorem}\n"
            "\\newtheorem{proposition}[theorem]{Proposition}\n"
            "\\newtheorem{lemma}[theorem]{Lemma}\n"
            "\\newtheorem{corollary}[theorem]{Corollary}\n\n"
            "\\theoremstyle{definition}\n"
            "\\newtheorem{definition}[theorem]{Definition}\n",
        REPO_ROOT / "blueprint" / "src" / "macros" / "print.tex":
            "% Print-only blueprint macros.\n"
            "\\newcommand{\\lean}[1]{}\n"
            "\\newcommand{\\discussion}[1]{}\n"
            "\\newcommand{\\leanok}{}\n"
            "\\newcommand{\\mathlibok}{}\n"
            "\\newcommand{\\notready}{}\n\n"
            "\\ExplSyntaxOn\n"
            "\\NewDocumentCommand{\\uses}{m}\n"
            " {\\clist_map_inline:nn{#1}{\\vphantom{\\ref{##1}}}\\ignorespaces}\n"
            "\\NewDocumentCommand{\\proves}{m}\n"
            " {\\clist_map_inline:nn{#1}{\\vphantom{\\ref{##1}}}\\ignorespaces}\n"
            "\\ExplSyntaxOff\n",
        REPO_ROOT / "blueprint" / "src" / "macros" / "web.tex":
            "% Web-specific blueprint macros.\n",
    }
    for path, content in scaffold.items():
        if path.name in {"content.tex", "print.tex", "web.tex", "common.tex"}:
            path.write_text(content)
        elif not path.exists():
            path.write_text(content)

    template_copies = {
        template_root / "blueprint.sty": REPO_ROOT / "blueprint" / "src" / "blueprint.sty",
        template_root / "latexmkrc": REPO_ROOT / "blueprint" / "src" / "latexmkrc",
        template_root / "extra_styles.css": REPO_ROOT / "blueprint" / "src" / "extra_styles.css",
    }
    for src, dst in template_copies.items():
        if src.exists():
            dst.write_text(src.read_text())

    plastex_cfg = REPO_ROOT / "blueprint" / "src" / "plastex.cfg"
    plastex_cfg.write_text(
        "[general]\n"
        "renderer=HTML5\n"
        "copy-theme-extras=yes\n"
        "plugins=plastexdepgraph leanblueprint\n\n"
        "[document]\n"
        "toc-depth=3\n"
        "toc-non-files=True\n\n"
        "[files]\n"
        "directory=../web/\n"
        "split-level=0\n\n"
        "[html5]\n"
        "localtoc-level=0\n"
        "extra-css=extra_styles.css\n"
        "mathjax-dollars=False\n"
    )


def direct_dependency_names(extracted: dict, selected: set[str]) -> list[str]:
    deps = list(extracted["statementDeps"]) + list(extracted["bodyDeps"])
    seen: set[str] = set()
    out: list[str] = []
    for dep in deps:
        if dep in selected and dep not in seen:
            seen.add(dep)
            out.append(dep)
    return out


def project_dependencies(
    decls: list[DeclInfo], extracted: dict[str, dict], *, ignore_lemmas: bool
) -> dict[str, list[str]]:
    all_names = {decl.name for decl in decls}
    kept = [decl for decl in decls if not (ignore_lemmas and decl.kind == "lemma")]
    kept_names = {decl.name for decl in kept}
    kind_by_name = {decl.name: decl.kind for decl in decls}
    direct_predecessors = {
        decl.name: direct_dependency_names(extracted[decl.name], all_names)
        for decl in decls
        if decl.name in extracted
    }
    if not ignore_lemmas:
        return {
            decl.name: [dep for dep in direct_predecessors[decl.name] if dep in kept_names]
            for decl in kept
        }

    projected: dict[str, list[str]] = {}
    for decl in kept:
        seen_omitted: set[str] = set()
        out: list[str] = []
        seen_out: set[str] = set()
        stack = list(reversed(direct_predecessors[decl.name]))
        while stack:
            dep = stack.pop()
            if dep in kept_names:
                if dep not in seen_out:
                    seen_out.add(dep)
                    out.append(dep)
                continue
            if kind_by_name.get(dep) != "lemma" or dep in seen_omitted:
                continue
            seen_omitted.add(dep)
            for parent in reversed(direct_predecessors.get(dep, [])):
                stack.append(parent)
        projected[decl.name] = out
    return projected


def emit_decl_tex(decl: DeclInfo, dep_names: list[str], labels: dict[str, str], extracted: dict) -> str:
    env_name = {
        "def": "definition",
        "noncomputable def": "definition",
        "lemma": "lemma",
        "theorem": "theorem",
        "structure": "definition",
        "instance": "definition",
    }[decl.kind]
    title_prefix = decl.kind
    title = tex_escape(f"{title_prefix}: {decl.name}")
    label = labels[decl.name]
    deps = [labels[d] for d in dep_names]
    status = " [SORRY]" if extracted["directSorry"] else ""
    parts = [
        f"\\begin{{{env_name}}}[{title}{status}]",
        f"\\label{{{label}}}",
        f"\\lean{{{decl.name}}}",
    ]
    if deps:
        parts.append(f"\\uses{{{','.join(deps)}}}")
    parts.append(
        f"Autogenerated skeleton for \\texttt{{{tex_escape(decl.name)}}} "
        f"from \\texttt{{{tex_escape(decl.module)}}}."
    )
    parts.append(f"\\end{{{env_name}}}")
    return "\n".join(parts)

def write_blueprint(
    targets: list[tuple[str, Path]],
    decls: list[DeclInfo],
    extracted_rows: list[dict],
    *,
    nonreduced: bool,
    ignore_lemmas: bool,
) -> None:
    ensure_blueprint_scaffold(nonreduced=nonreduced)
    extracted = {row["name"]: row for row in extracted_rows}
    decls = [d for d in decls if d.name in extracted]
    decls_to_emit = [d for d in decls if not (ignore_lemmas and d.kind == "lemma")]
    labels = {d.name: sanitize_label(d.kind, d.name) for d in decls_to_emit}
    projected_deps = project_dependencies(decls, extracted, ignore_lemmas=ignore_lemmas)

    by_module: dict[str, list[DeclInfo]] = {}
    for decl in decls_to_emit:
        by_module.setdefault(decl.module, []).append(decl)

    index_lines = ["% Autogenerated file. Do not edit directly."]
    for module, _ in targets:
        module_file = GENERATED_DIR / f"{module.replace('.', '_')}.tex"
        index_lines.append(f"\\input{{generated/{module_file.stem}}}")
        module_lines = [
            "% Autogenerated file. Do not edit directly.",
            f"\\section{{{tex_escape(module)}}}",
        ]
        for decl in by_module.get(module, []):
            module_lines.append(emit_decl_tex(decl, projected_deps.get(decl.name, []), labels, extracted[decl.name]))
            module_lines.append("")
        module_file.write_text("\n".join(module_lines).rstrip() + "\n")
    (GENERATED_DIR / "generated_content.tex").write_text("\n".join(index_lines) + "\n")


def user_bin_path() -> Path:
    return Path(site.USER_BASE) / "bin"


def tool_path(name: str) -> str:
    user_tool = user_bin_path() / name
    if user_tool.exists():
        return str(user_tool)
    found = shutil.which(name)
    if found is not None:
        return found
    raise SystemExit(f"required tool not found: {name}")


def tool_env() -> dict[str, str]:
    env = dict(os.environ)
    user_bin = str(user_bin_path())
    env["PATH"] = user_bin if "PATH" not in env else f"{user_bin}:{env['PATH']}"
    return env


def run_leanblueprint_web() -> None:
    proc = subprocess.run(
        [tool_path("leanblueprint"), "web"],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
        env=tool_env(),
    )
    if proc.returncode != 0:
        raise SystemExit(proc.stderr.strip() or proc.stdout.strip() or "leanblueprint web failed")


def extract_dot_from_web() -> Path:
    html_path = REPO_ROOT / "blueprint" / "web" / "dep_graph_document.html"
    html = html_path.read_text()
    m = re.search(r"renderDot\(`(strict digraph .*?)`\)", html, re.S)
    if m is None:
        raise SystemExit(f"DOT graph not found in {html_path}")
    dot_path = html_path.with_suffix(".dot")
    dot_path.write_text(m.group(1))
    return dot_path


NODE_STYLE_BY_PREFIX = {
    "def:": {"shape": "box", "color": "black", "style": '"rounded,filled"', "fillcolor": "#d9ead3"},
    "str:": {"shape": "box", "color": "black", "style": '"rounded,filled"', "fillcolor": "#e8f0ff"},
    "inst:": {"shape": "box", "color": "black", "style": '"rounded,filled"', "fillcolor": "#e8f0ff"},
    "lem:": {"shape": "ellipse", "color": "black", "style": "filled", "fillcolor": "#fff2cc"},
    "thm:": {"shape": "ellipse", "color": "black", "style": "filled", "fillcolor": "#f4cccc"},
}


def classify_node_prefix(node_id: str) -> str | None:
    for prefix in NODE_STYLE_BY_PREFIX:
        if node_id.startswith(prefix):
            return prefix
    return None


def label_to_lean_name_map() -> dict[str, str]:
    mapping: dict[str, str] = {}
    for tex_path in GENERATED_DIR.glob("*.tex"):
        if tex_path.name == "generated_content.tex":
            continue
        lines = tex_path.read_text().splitlines()
        pending_label: str | None = None
        for line in lines:
            m_label = re.match(r"\\label\{([^}]+)\}", line.strip())
            if m_label:
                pending_label = m_label.group(1)
                continue
            m_lean = re.match(r"\\lean\{([^}]+)\}", line.strip())
            if m_lean and pending_label is not None:
                mapping[pending_label] = m_lean.group(1)
                pending_label = None
    return mapping


def restyle_dot(dot_path: Path, *, ignore_lemmas: bool) -> None:
    text = dot_path.read_text()
    display_name_map = label_to_lean_name_map()
    parts = text.split(";")
    rewritten: list[str] = []
    for part in parts:
        stripped = part.strip()
        if "->" in stripped:
            match = re.fullmatch(r'"([^"]+)"\s*->\s*"([^"]+)"(?:\s*\[(.*)\])?', stripped)
            if match is None:
                rewritten.append(part)
                continue
            source_id, target_id, attrs = match.group(1), match.group(2), match.group(3)
            attr_map: dict[str, str] = {}
            if attrs is not None:
                for key, value in re.findall(r'([A-Za-z_][A-Za-z0-9_]*)=("[^"]*"|[^,\]]+)', attrs):
                    attr_map[key] = value.strip()
            attr_map.pop("style", None)
            attr_text = ""
            if attr_map:
                ordered_keys = ["style", "color", "penwidth", "arrowsize", "minlen"]
                ordered = [f'{key}={attr_map[key]}' for key in ordered_keys if key in attr_map]
                ordered.extend(f"{key}={value}" for key, value in attr_map.items() if key not in ordered_keys)
                attr_text = f' [{", ".join(ordered)}]'
            prefix_text = part[: len(part) - len(part.lstrip())]
            suffix_text = part[len(part.rstrip()):]
            rewritten.append(f'{prefix_text}"{source_id}" -> "{target_id}"{attr_text}{suffix_text}')
            continue
        match = re.fullmatch(r'"([^"]+)"\s*\[(.*)\]', stripped)
        if match is None:
            rewritten.append(part)
            continue
        node_id = match.group(1)
        prefix = classify_node_prefix(node_id)
        if prefix is None:
            rewritten.append(part)
            continue
        attrs = match.group(2)
        style = NODE_STYLE_BY_PREFIX[prefix]
        attr_map: dict[str, str] = {}
        for key, value in re.findall(r'([A-Za-z_][A-Za-z0-9_]*)=("[^"]*"|[^,\]]+)', attrs):
            attr_map[key] = value.strip()
        attr_map["label"] = f'"{display_name_map.get(node_id, node_id)}"'
        attr_map["shape"] = style["shape"]
        attr_map["color"] = style["color"]
        attr_map["style"] = style["style"]
        if style["fillcolor"] is None:
            attr_map.pop("fillcolor", None)
        else:
            attr_map["fillcolor"] = f'"{style["fillcolor"]}"'
        ordered_keys = ["label", "shape", "style", "color", "fillcolor", "penwidth"]
        ordered = [f'{key}={attr_map[key]}' for key in ordered_keys if key in attr_map]
        ordered.extend(f"{key}={value}" for key, value in attr_map.items() if key not in ordered_keys)
        prefix_text = part[: len(part) - len(part.lstrip())]
        suffix_text = part[len(part.rstrip()):]
        rewritten.append(f'{prefix_text}"{node_id}"\t[{",\t\t".join(ordered)}]{suffix_text}')
    text = ";".join(rewritten)
    text = text.rstrip()
    if text.endswith("}"):
        text = text[:-1] + "}"
    dot_path.write_text(text)


def render_svg(dot_path: Path) -> Path:
    svg_path = dot_path.with_suffix(".svg")
    proc = subprocess.run(
        [tool_path("dot"), "-Tsvg", str(dot_path), "-o", str(svg_path)],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        raise SystemExit(proc.stderr.strip() or proc.stdout.strip() or "dot render failed")
    return svg_path


def add_svg_legend(svg_path: Path, *, ignore_lemmas: bool) -> None:
    text = svg_path.read_text(errors="ignore")
    view_box_match = re.search(r'viewBox="([^"]+)"', text)
    width_match = re.search(r'width="([^"]+)pt"', text)
    height_match = re.search(r'height="([^"]+)pt"', text)
    if view_box_match is None or width_match is None or height_match is None:
        return

    min_x, min_y, view_w, view_h = [float(x) for x in view_box_match.group(1).split()]
    width_pt = float(width_match.group(1))
    height_pt = float(height_match.group(1))

    legend_margin_top = 24.0
    legend_height = 54.0
    legend_y = min_y + view_h + legend_margin_top
    baseline_y = legend_y + 26.0
    x = min_x + 20.0
    parts: list[str] = ['<g id="custom_legend">']

    def add_rect(label: str, fill: str, w: float) -> None:
        nonlocal x
        parts.append(
            f'<g><rect x="{x:.2f}" y="{legend_y + 6:.2f}" width="{w:.2f}" height="28.00" '
            f'rx="10" ry="10" fill="{fill}" stroke="black" stroke-width="1.8"/>'
            f'<text xml:space="preserve" text-anchor="middle" x="{x + w / 2:.2f}" y="{baseline_y:.2f}" '
            f'font-family="Times,serif" font-size="14.00">{label}</text></g>'
        )
        x += w + 18.0

    def add_ellipse(label: str, fill: str, rx: float) -> None:
        nonlocal x
        cx = x + rx
        parts.append(
            f'<g><ellipse cx="{cx:.2f}" cy="{legend_y + 20:.2f}" rx="{rx:.2f}" ry="18.00" '
            f'fill="{fill}" stroke="black" stroke-width="1.8"/>'
            f'<text xml:space="preserve" text-anchor="middle" x="{cx:.2f}" y="{baseline_y:.2f}" '
            f'font-family="Times,serif" font-size="14.00">{label}</text></g>'
        )
        x += 2 * rx + 18.0

    add_rect("definition", "#d9ead3", 92.0)
    add_rect("structure", "#e8f0ff", 86.0)
    if not ignore_lemmas:
        add_ellipse("lemma", "#fff2cc", 46.0)
    add_ellipse("theorem", "#f4cccc", 58.0)

    label_x = x + 4.0
    parts.append(
        f'<text xml:space="preserve" text-anchor="start" x="{label_x:.2f}" y="{baseline_y:.2f}" '
        f'font-family="Times,serif" font-size="14.00">dependency</text>'
    )
    line_start_x = label_x + 88.0
    line_end_x = line_start_x + 84.0
    line_y = legend_y + 20.0
    parts.append(
        f'<line x1="{line_start_x:.2f}" y1="{line_y:.2f}" x2="{line_end_x:.2f}" y2="{line_y:.2f}" '
        f'stroke="black" stroke-width="1.8"/>'
    )
    parts.append(
        f'<polygon fill="black" stroke="black" points="'
        f'{line_end_x - 12:.2f},{line_y - 8:.2f} {line_end_x:.2f},{line_y:.2f} {line_end_x - 12:.2f},{line_y + 8:.2f} '
        f'{line_end_x - 9:.2f},{line_y:.2f}"/>'
    )
    parts.append('</g>')

    new_view_h = view_h + legend_margin_top + legend_height
    new_height_pt = height_pt * (new_view_h / view_h)
    text = re.sub(r'viewBox="[^"]+"', f'viewBox="{min_x:.2f} {min_y:.2f} {view_w:.2f} {new_view_h:.2f}"', text, count=1)
    text = re.sub(r'height="[^"]+pt"', f'height="{new_height_pt:.2f}pt"', text, count=1)
    text = text.replace("</svg>", "".join(parts) + "</svg>")
    svg_path.write_text(text)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="+", help="Lean module names or .lean file paths")
    parser.add_argument(
        "--render-svg",
        action="store_true",
        help="After generating the blueprint, run leanblueprint web and emit dep_graph_document.svg",
    )
    parser.add_argument(
        "--nonreduced",
        action="store_true",
        help="Keep all direct dependency edges instead of transitively reducing the graph",
    )
    parser.add_argument(
        "--ignore-lemmas",
        action="store_true",
        help="Exclude lemma declarations from the generated blueprint and graph",
    )
    args = parser.parse_args()

    resolved = [resolve_target(t) for t in args.targets]
    decls: list[DeclInfo] = []
    for module, path in resolved:
        decls.extend(parse_declarations(module, path))
    extracted = run_extract([module for module, _ in resolved], [decl.name for decl in decls])
    write_blueprint(resolved, decls, extracted, nonreduced=args.nonreduced, ignore_lemmas=args.ignore_lemmas)
    print("Generated blueprint skeleton under blueprint/src/generated/")
    if args.render_svg:
        run_leanblueprint_web()
        dot_path = extract_dot_from_web()
        restyle_dot(dot_path, ignore_lemmas=args.ignore_lemmas)
        svg_path = render_svg(dot_path)
        add_svg_legend(svg_path, ignore_lemmas=args.ignore_lemmas)
        print(f"Rendered dependency graph SVG at {svg_path.relative_to(REPO_ROOT)}")


if __name__ == "__main__":
    main()

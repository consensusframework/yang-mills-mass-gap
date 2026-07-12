#!/usr/bin/env python3
"""kernel_xray.py — parser VERSIONADO do raio-X de dependências.

Lê o log bruto do `lake build` (com a saída dos Audit_*.lean) e produz
KERNEL_XRAY.{json,csv,md} em docs/audit/.

WHITELIST EXPLÍCITA de fundamentos do Lean (NÃO são axiomas científicos):
  propext, Classical.choice, Quot.sound
A comparação usa o NOME COMPLETO. (Bug histórico corrigido: uma versão
anterior comparava apenas o último componente, contando Classical.choice
e Quot.sound como científicos — relatório público dizia 2/126 enquanto o
número correto era 60/126.)
"""
import re,sys,json,csv,collections

FOUNDATION = {"propext", "Classical.choice", "Quot.sound"}

def parse(log_text):
    log_text = re.sub(r"^\S*\d{4}-\d\d-\d\dT[0-9:.]+Z ", "", log_text, flags=re.M)
    deps = {}
    for m in re.finditer(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", log_text):
        deps[m.group(1)] = sorted(x.strip() for x in m.group(2).split(",") if x.strip())
    for m in re.finditer(r"'([\w.]+)' does not depend on any axioms", log_text):
        deps[m.group(1)] = []
    return deps

def classify(deps):
    rows = []
    for name, axs in sorted(deps.items()):
        sci = [a for a in axs if a not in FOUNDATION]
        cls = "FOUNDATION_ONLY" if not sci else "SCIENTIFIC_AXIOM_DEPENDENT"
        rows.append({"name": name, "class": cls,
                     "scientific_axioms": ";".join(sci),
                     "all_axioms": ";".join(axs)})
    return rows

def main(log_path, outdir):
    deps = parse(open(log_path, encoding="utf-8", errors="replace").read())
    rows = classify(deps)
    if not rows:
        print("PARSE_ERROR: nenhum #print axioms encontrado"); sys.exit(2)
    clean = [r for r in rows if r["class"] == "FOUNDATION_ONLY"]
    sci_map = collections.defaultdict(list)
    for r in rows:
        for a in r["scientific_axioms"].split(";"):
            if a: sci_map[a].append(r["name"])
    json.dump(rows, open(f"{outdir}/KERNEL_XRAY.json", "w"), indent=1)
    with open(f"{outdir}/KERNEL_XRAY.csv", "w", newline="") as fo:
        w = csv.DictWriter(fo, fieldnames=list(rows[0].keys()))
        w.writeheader(); [w.writerow(r) for r in rows]
    md = ["# KERNEL_XRAY.md — gerado por scripts/kernel_xray.py (NÃO editar à mão)","",
          f"Fonte: log bruto do CI (artifact `kernel-xray-raw-log`).",
          f"Whitelist de fundamentos: {sorted(FOUNDATION)}","",
          f"## Placar do kernel",
          f"- Radiografados: {len(rows)}",
          f"- **FOUNDATION_ONLY: {len(clean)}**",
          f"- SCIENTIFIC_AXIOM_DEPENDENT: {len(rows)-len(clean)}","",
          "## Axiomas científicos por nº de dependentes",""]
    for a, ts in sorted(sci_map.items(), key=lambda x: -len(x[1])):
        md.append(f"- `{a}` ← {len(ts)}")
    md += ["", "## FOUNDATION_ONLY (nominal)", ""]
    md += [f"- `{r['name']}`" for r in clean]
    open(f"{outdir}/KERNEL_XRAY.md", "w").write("\n".join(md))
    print(f"radiografados={len(rows)} foundation_only={len(clean)} sci={len(rows)-len(clean)}")

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "docs/audit")

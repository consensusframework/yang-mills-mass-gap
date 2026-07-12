# REPRODUCIBILITY.md — como verificar tudo do zero

## Build (qualquer máquina, ~30-60 min com cache)
1. Instalar elan: `curl -sSL https://elan.lean-lang.org/elan-init.sh | sh`
2. Para cada fase (Phase1, Phase2, Phase3):
   `cd PhaseK && lake update && lake exe cache get && lake build`
   Toolchain pinada: leanprover/lean4:v4.15.0; Mathlib rev v4.15.0.
3. Verde = todos os teoremas verificados pelo kernel. Não há passos
   manuais nem binários pré-compilados do projeto.

## CI (sem máquina local)
.github/workflows/lean-ci.yml roda os 3 builds em cada push à main.
O job build-phase2 também executa o raio-X (#print axioms de todos os
teoremas) e publica artifacts: kernel_raw.log + KERNEL_XRAY.{md,json,csv}.

## Regeneração dos relatórios de auditoria
- Raio-X: `python3 scripts/kernel_xray.py <log_bruto> docs/audit`
  (whitelist de fundamentos no próprio script; snapshot do log em
  docs/audit/kernel_raw_snapshot.log).
- Censo estrutural: metodologia descrita em docs/audit/*_SUMMARY.md;
  scripts inline no histórico do git (branches audit-zero*).

## Âncoras de versão
- 17ª pedra: merge f112cf6fa762 • 18ª: 1c62dd7 • raio-X: 64e63db.
- Run verde público de referência: actions/runs/29167921404.

## O que NÃO é reproduzível por build
Interpretação física e escopo (docs/*, VERIFICATION_STATUS.md) — por
isso vão a revisão comunitária (Zulip). O kernel verifica provas, não
significados.

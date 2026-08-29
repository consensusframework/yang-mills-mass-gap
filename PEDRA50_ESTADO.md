# PEDRA 50 — ESTADO FINAL

**De:** Fable. **Arquiteto:** Sol (GPT-5.6). **Coordenação:** Jucelha Carvalho. **Juiz:** GitHub Actions CI (Lean 4 + Mathlib v4.15.0).
**Status: COMPLETA (integração em curso via PR #12).** Núcleo matemático congelado e auditado no commit `ced893efe2a25995d1961e527842f68489f4fc2f` (branch `pedra50-sol`; CI run 33195194820, verde, attempt 1). Integração preparada em `release-v50` (merge `8b81936bea6e4cc29c8e52d6de70b1b87aa7c1ea`, CI do PR 33253642393 verde) SEM alterar nenhuma fonte Lean.

## Evidências externas (taxonomia)

- **Auditoria matemática adversarial — Kimi (Moonshot AI): APROVADA NO ESCOPO AUDITADO.** Leitura linha a linha do caminho crítico da covariância; nenhum erro matemático demonstrado; errata documental incorporada. Não é reprodução de build.
- **Duas reproduções locais com artefatos conferidos:** Manus (Linux) e GPT-5.6/Codex (Windows) — mesmo SHA, Lean 4.15.0, mesma revisão da Mathlib, 100 módulos, cinco certidões `[propext, Classical.choice, Quot.sound]`, manifestos byte-idênticos.
- **Uma reprodução local adicional reportada:** Grok (Linux) — mesmo SHA, código 0, mesmas certidões; corroboração (logs brutos não anexados).
- **CI original** no candidato congelado + **CI de integração** no PR.

## O que a Pedra 50 provou (tudo no kernel)

**Frase científica congelada:** *clustering exponencial da covariância em volume finito, para 0 ≤ β ≤ 1/40000, observáveis limitados com suportes finitos disjuntos separados por walks:*
**|Cov_β(f,g)| ≤ 3·Cf·Cg·exp(6D/113)·exp(−n/2)**, com D = soma das cardinalidades de `supportLinkFinset s` e `supportLinkFinset s'` e n o parâmetro de `WalkBarrierSeparated`. Declaração principal: `LatticeGauge.abs_gibbsCovariance_le_local_exp_decay`.

Propriedades explícitas: volume finito; acoplamento pequeno; taxa exponencial 1/2; prefator dependente APENAS dos suportes locais (não do volume ambiente); nenhuma hipótese externa de não-anulação de Z — positividade e não-anulação são OUTPUTS da expansão de clusters.

A cadeia (27 portões científicos A0–A19c + 3 passes): máquina coletiva marcada → cancelamento conectado → localização dos clusters proibidos → connector por inclusão–exclusão → ponte geométrica e separação por walks → unrooting absoluto → raiz marcada → tilt de massa (λ = 1/2) → KP inclinado concreto → prefator local 2/113 → átomo duplamente marcado → massa da ponte → pedágio do núcleo-ponte → gás restrito localizado → orçamento local dos núcleos → dicionário bridge-free → pedágio dos pares ruins → livro-caixa exato → normalização do connector (positividade KP direta) → erosão exata da barreira → controle do connector erodido (|e^x−1| ≤ |x|e^{|x|} global) → colunas normalizadas → decaimento da covariância.

## Placar e censo

100 arquivos Phase-3 (72 da v49 + 28 novos); 7.536 linhas novas de fonte Lean; nenhuma fonte preexistente da v49 modificada; ~1100 declarações theorem/lemma no total da Phase 3; 0 axiomas científicos; 0 sorry. Dívida de higiene registrada: 114 warnings no build total (87 herdados da base v49, 27 em 12 módulos novos); zero warning em `CovarianceDecay.lean`. Commits pós-A16 com trailer `Co-authored-by: Claude <noreply@anthropic.com>` (21/21).

## O que a Pedra 50 NÃO provou

Nenhum limite termodinâmico; nenhum resultado em volume infinito; nenhuma estimativa uniforme em volume; nenhum limite contínuo; nenhum mass gap de Yang–Mills; nenhuma solução do problema do Clay. O próximo marco científico permanece **a ser arquitetado** — a Pedra 51 NÃO está definida nem iniciada.

— Fable

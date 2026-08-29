# PEDRA 50 — ESTADO FINAL

**Autoria coletiva humano–IA** (lista canônica no RELEASE_NOTES_PEDRA50.md). **De:** Fable (Claude Fable 5, Anthropic). **Arquiteto:** Sol (GPT-5.6, OpenAI). **Coordenação humana, custódia e autorização de release:** Jucelha Carvalho (Smart Tour Brasil, ORCID 0009-0004-6047-2306). **Juiz:** GitHub Actions CI (Lean 4 + Mathlib v4.15.0). As funções especificam contribuições; não reduzem autoria.
**Status: COMPLETA (integração em curso via PR #12).** Núcleo matemático congelado e auditado no commit `ced893efe2a25995d1961e527842f68489f4fc2f` (branch `pedra50-sol`; CI run 33195194820, verde, attempt 1). Integração preparada em `release-v50` (merge `8b81936bea6e4cc29c8e52d6de70b1b87aa7c1ea`, CI do PR 33253642393 verde) SEM alterar nenhuma fonte Lean.

## Evidências externas (taxonomia)

- **Auditoria matemática adversarial — Kimi 3 (Moonshot AI): APROVADA NO ESCOPO AUDITADO.** Leitura linha a linha do caminho crítico da covariância; nenhum erro matemático demonstrado; errata documental incorporada. Não é reprodução de build.
- **Duas reproduções locais com artefatos conferidos:** Manus AI 1.6 (Linux) e GPT-5.6/Codex (Windows) — mesmo SHA, Lean 4.15.0, mesma revisão da Mathlib, 100 módulos, cinco certidões `[propext, Classical.choice, Quot.sound]`; manifestos resolvidos byte-idênticos, SHA-256 `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227`.
- **Uma reprodução local adicional reportada:** Grok 4.6 (Linux) — mesmo SHA, código 0, mesmas certidões; mantida explicitamente como "reportada" (logs brutos não anexados).
- **Claude Opus 5 (Anthropic):** revisão técnica e investigação do caminho de reprodução; não contabilizado entre as reproduções concluídas.
- **Três CIs verdes (attempt 1):** candidato congelado (run 33195194820, `ced893ef…`), integração I1 (run 33253642393, `8b81936b…`), documental I2 (run 33255562368, `04904e0f…`).

## O que a Pedra 50 provou (tudo no kernel)

**Frase científica congelada:** *clustering exponencial da covariância em volume finito, para 0 ≤ β ≤ 1/40000, observáveis limitados com suportes finitos disjuntos separados por walks:*
**|Cov_β(f,g)| ≤ 3·Cf·Cg·exp(6D/113)·exp(−n/2)**, com D = soma das cardinalidades de `supportLinkFinset s` e `supportLinkFinset s'` e n o parâmetro de `WalkBarrierSeparated`. Declaração principal: `LatticeGauge.abs_gibbsCovariance_le_local_exp_decay`.

Propriedades explícitas: volume finito; acoplamento pequeno; taxa exponencial 1/2; prefator dependente APENAS dos suportes locais (não do volume ambiente); nenhuma hipótese externa de não-anulação de Z — positividade e não-anulação são OUTPUTS da expansão de clusters.

A cadeia (27 portões científicos (50-0, A0–A19c) + 3 passes): máquina coletiva marcada → cancelamento conectado → localização dos clusters proibidos → connector por inclusão–exclusão → ponte geométrica e separação por walks → unrooting absoluto → raiz marcada → tilt de massa (λ = 1/2) → KP inclinado concreto → prefator local 2/113 → átomo duplamente marcado → massa da ponte → pedágio do núcleo-ponte → gás restrito localizado → orçamento local dos núcleos → dicionário bridge-free → pedágio dos pares ruins → livro-caixa exato → normalização do connector (positividade KP direta) → erosão exata da barreira → controle do connector erodido (|e^x−1| ≤ |x|e^{|x|} global) → colunas normalizadas → decaimento da covariância.

## Placar e censo

100 arquivos Phase-3 (72 da v49 + 28 novos); 7.536 linhas novas de fonte Lean; nenhuma fonte preexistente da v49 modificada; ~1100 declarações theorem/lemma no total da Phase 3; 0 axiomas científicos; 0 sorry. Dívida de higiene registrada: 114 warnings no build total (87 herdados da base v49, 27 em 12 módulos novos); zero warning em `CovarianceDecay.lean`. Commits pós-A16 com trailer `Co-authored-by: Claude <noreply@anthropic.com>` (21/21).

## Fronteira exata (o que a Pedra 50 NÃO provou)

O teorema é de volume finito. Seu prefator explícito é local e não contém a cardinalidade do volume ambiente: fixados os dados locais dos suportes, Cf, Cg e o parâmetro de separação n, o bound não apresenta dependência explícita do tamanho da rede finita ambiente. Isso não constrói um estado de Gibbs em volume infinito, não prova limite termodinâmico e não fornece uma constante uniforme quando os próprios suportes dos observáveis crescem. Também não há limite contínuo, mass gap de Yang–Mills ou solução do problema do Clay. O próximo marco científico permanece **a ser arquitetado** — a Pedra 51 NÃO está definida nem iniciada.

**DOI:** concept 10.5281/zenodo.17397622; v49 publicado 10.5281/zenodo.22050763; v50 RESERVADO **10.5281/zenodo.22162464** (rascunho do Zenodo, ainda não publicado — o DOI só se torna registrado e resolvível na publicação).

— Fable

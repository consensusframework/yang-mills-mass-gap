# RELATÓRIO 56-QA1 — Auditoria independente da Pedra 56 (localização da estabilidade por perfis com fundo de amortecimento comum)

**Auditor:** Claude Fable 5.1 (instância auditora, bancada Lean própria; distinta da instância construtora/publicadora).
**Data:** 2026-09-24 (UTC). **Fita:** FITA 56-QA1 (Ju/Astra). **Modo:** somente leitura sobre o candidato; zero edições, zero commit/push/PR/merge/tag/Release/Zenodo; nenhum defeito corrigido; Pedra 57 não iniciada.

## 0. Identidade e exposição prévia

Declaro exposição prévia: auditei as fitas 52-A0…52-E, 53, 54 e 55 deste mesmo programa (a Pedra 55 é o baseline desta auditoria e a sua reconstrução limpa é minha), conheço a arquitetura descrita na fita e li `RELATORIO_56-L.md` (SHA `04ccde1b…0df2d1`, fora do ZIP) antes da execução, apenas para identificar o alvo. **Esta auditoria não é cega.** Logs, testes e matrizes do construtor permaneceram fechados até a conclusão da minha reconstrução, dos meus testes e de `PRELIMINARY_CONCLUSIONS_first_pass.md` (incluído no pacote); só então foram abertos e comparados (§7). Oleans do construtor não foram usados.

## 1. Alvo

| item | valor observado | fita |
|---|---|---|
| base | `445cc76b02550291e6524bb1bf631aac4cc86c61` = `origin/main` observada = tag `zenodo-v55` | ✅ |
| candidato | `a2fcf8e9050c470b83c7b95cc45d9512b38fcfc1`, 1 commit sobre a base | ✅ |
| root tree / Phase3 | `171367d9…` / `f387f26d…` | ✅ |
| blob do módulo | `f2103846…` = `Phase3/LatticeGauge/ActivityProfileDampingLocality.lean`, modo `100644`, 964 linhas, 2 defs + 22 teoremas, 22 `#print axioms` (nomes = linhas, conferido) | ✅ |
| blob lakefile | `ae8438d4…`; globs 116 → 117 (+1 linha) | ✅ |
| diff | exatamente +965/−1 (A módulo, M lakefile) | ✅ |
| ZIP | `7049021d…e38e6`, 29 entradas = 27 arquivos + 2 diretórios; manifesto interno 26 entradas sem auto-inclusão, 26/26 OK; sem caminhos absolutos/`..`/duplicados | ✅ |
| bundle / fonte avulsa / diff / matrizes | `3e62dc5b…` (verify OK) / `09479f01…` (= blob) / `89969528…` / `91ee6cb4…`, `eb139438…` | ✅ |
| pins e dependências | `lean-toolchain` v4.15.0, manifesto versionado blob `79049caf…` = SHA `c376bbe9…`, 9/9 revisões dos pacotes (mathlib 9837ca9d…, batteries, aesop, Qq, proofwidgets, importGraph, LeanSearchClient, plausible, Cli) conferidas no checkout; workflow, docs, auditorias, licenças e os 116 módulos anteriores byte-idênticos à base | ✅ |
| Phase3 da base | `20ffea86…` = Phase3 do candidato 55 ⇒ o baseline de warnings da 55-QA1 é válido | ✅ |

Proveniência: autor/committer `Claude <noreply@anthropic.com>`; cabeçalho `gpgsig` (SSH) presente. Nesta bancada `git verify-commit` não verifica assinaturas SSH (sem `allowedSignersFile`): **o cabeçalho de assinatura foi registrado como presente, não como autenticação independente**; trailers `Co-Authored-By: Claude Fable 5.1` e `Claude-Session` seguem o precedente aceito das Pedras 53–55.

## 2. Método

Clone próprio com push desabilitado (`DISABLED_NO_REMOTE_WRITE`); bundle importado em `refs/bundles/qa56`; worktree destacada em `a2fcf8e9`; bancada Lean 4.15.0 (11651562caae) / Lake 5.0.0-1165156; dependências materializadas do cache local desta bancada após conferência das 9 revisões do manifesto (sem `lake update`, sem alteração de pins; manifesto pré = pós em todos os builds). Sequência: custódia → leitura integral das 964 linhas → build dirigido → testes próprios W0–W7x (arquivos descartáveis fora da árvore, `lake env lean` a partir de `Phase3/`) → reconstrução limpa dos 117 módulos (`rm -rf .lake/build && lake build`) com verificação de pureza → comparação de blocos integrais de warnings → certidões → higiene e mapa de dependências → conclusões preliminares → abertura do material do construtor → comparação → este relatório.

## 3. Resultados de execução

- **Dirigido** `lake build LatticeGauge.ActivityProfileDampingLocality`: exit 0 (308 s), 0 erros, 0 warnings no módulo, 22 certidões exatas.
- **Limpo** (início 2026-09-24T20:55:38Z, fim 21:07:39Z): exit 0 (721 s), **117 Built / 0 Replayed**, 0 erros, 0 sorryAx, **269 certidões (247 + 22), 269/269 exatamente `[propext, Classical.choice, Quot.sound]`** (parser tolerante ao apóstrofo de `activityRestrictedMarkedGas_eq_sum_core_mul_restricted'`); 117 `.olean`, 0 anteriores ao instante de início; árvore git limpa após o build; manifesto `c376bbe9…` pré = pós. Log: `out/build_full_clean.log` (SHA `38ca3d81…`).
- **Warnings** (comparação de **blocos integrais multilinha**, cabeçalho + continuações, normalizando apenas o prefixo `./`; projeto e dependências separados): baseline validado = `docs/audits/stone55/packages/QA1_55_evidence.zip` da base (SHA `f21e2f65…f021` ✅ = fita) → `out/build_full_clean.log` (SHA `fed2f6b1…e4ae` ✅ = fita; é o meu log da 55-QA1). Candidato: 114 blocos, todos de `LatticeGauge/`, 113 pares arquivo:linha (`HolonomyHaar:198` ×2), **multiconjunto de blocos idêntico ao baseline**, 0 warnings no módulo novo, 0 diagnósticos de dependências em ambos os logs (pacotes não reconstruídos nesta bancada). Script e saída no pacote (`compare_warning_blocks.py`, `warnings_block_comparison.txt`).
- **Certidões próprias (W0)**: 22 teoremas + 2 defs, 24/24 exatas; `#check` das duas finais, das quatro interfaces, da capstone 55 e da interface 55-B impressos no log.
- **Higiene** (código fora de docstrings): 0 sorry/admit/axiom/native_decide/unsafe/opaque/set_option/maxHeartbeats/partial/decide; 0 `Disjoint`/`volume`/8(3e)/(7/8,3)/(7/8,2)/divisão por δ/(1−θ)/`DependsOnlyOn`. Imports: `Mathlib`, `LatticeGauge.ActivityProfileDampingStability`.
- **Contagens** (método documentado): 117 módulos (`ls LatticeGauge/*.lean`); 37.994 linhas (`wc -l`); 269 `#print axioms` (grep `^#print axioms`); linhas de declaração 1.745 (`^(theorem|lemma|def|noncomputable def) `) ou 1.790 (incluindo instance/structure/abbrev/inductive/class) — a referência 1.780 do construtor (1.756 + 24) depende do padrão de grep; o incremento do candidato é +24 (22 teoremas + 2 defs) sob qualquer método. Não material.

## 4. Resultados matemáticos (rederivação própria)

1. **Identidade orientada dos coeficientes** (`kpLocalizedDiff_inclusion_exclusion`, peso `A′_δ − A_δ`): rederivada com rota própria por casos (W1b): tupla P-permitida cancela entre restrito e irrestrito; tupla r-permitida tem `A_δ = A′_δ` por `hsame` usando apenas `TupleAllowed (regionAllowed r) δ → tupleTouchCount r δ = 0`; as restantes (ambas as barreiras) carregam `A′ − A`. Só `hsame` — sem intervalo, sem KP. Orientação confirmada por `D(a,a′) = −D(a′,a)` (W1b′). Ordem 0 = 0 e produto vazio = 1 com provas próprias (W1c); fator zero e repetição `![η,η]` (posições contadas) conferidos (W1d, W1e).
2. **Ledger localizado** (`profileExpectation_sub_eq_two_column_ledger_localized`): rederivado da forma exponencial da 55-A dos dois lados (W6a) sem o lema do candidato: peso do **segundo** perfil na coluna conectora; `(A_T − A′_T)` com sinal **MAIS** e expoente do **primeiro** perfil na coluna-ponte `activityBridgeCores s r`; cancelamento nos núcleos r-permitidos por **igualdade** dos pesos (não peso 1; testado com fundo 1/2, W1a/W3c); R mantido em todos os pesos e expoentes. Usa KP + intervalos + `hsame`; não usa `mf`, `hCf`, `hsep`, `hδ`.
3. **Fechamento pelas colunas** (W6b): ledger próprio + `abs_add` + colunas publicadas ⇒ dois termos ⇒ capstone `δ·(2Cf)·e^{6D/113}·e^{−n/2}`, sem os dois teoremas finais; constantes `3·D·(2/113)` e `2·D·(2/113)`, monotonia `e^{4D/113} ≤ e^{6D/113}` com `D ≥ 0`. Certidões de `W6_ledger` e `W6_closure` exatas.
4. **Itens do §4 da fita**: telescópica da 55-A aplicada aos fatores efetivos `touchFactor R ·` (intervalo transportado por `touchFactor_nonneg/le_one`); dominação `|D_k| ≤ δ·k·A_k(|z|,P,regionAllowed r)`; somabilidade pelo primeiro momento 52-A0 com **R livre** (só `WalkBarrierSeparated s r n`; nenhuma separação s/R); erosão `(n − familyTotalCard T : ℕ)` truncada (W5a: `m_T > n` ⇒ fator 1); κ = 2 bilateral rederivado do lema escalar 54 (`abs_exp_sub_exp_le_exp_mul_abs_sub`) com a barreira `abs_profileCoreExponent_le_barrier … R` da 55-A, `le_exp_self` e `exp_neg_nat_sub_half_le` (W5b); ponte κ = 1 via `nat_card_mul_abs_profileNormalizedTerm_le_bridge_two_regions` (geometria `activityBridgeCore_familyTotalCard_ge` com r, expoente com R; W5c com R = univ e R = ∅; R := r reproduz o enunciado 55-B, W5c′); orçamentos (1/2,2) `sum_halfTilt_two_le` e (7/8,1) `sum_sevenEighthsTilt_one_le`; (7/8,2) ausente; **capstone 55, dois-termos 55, ledger 55 e interface 55-B não são referenciados nem em código nem em docstring** — direção 56 ⇒ 55 confirmada (W4e recupera o enunciado 55 com R := r; W4f: os tipos da recuperação e da capstone 55 publicada são definicionalmente iguais, aceitos nas duas direções — igualdade de tipos, não de provas); igualdade algébrica por fatores efetivos iguais para perfis reais arbitrários (W4c rederivada das definições; W2a′/W4c′ com valores fora de [0,1]).
5. **Duas regiões e hipóteses efetivas**: capstone aplicada com R = univ ou R arbitrário, r arbitrário, fundo não unitário, sem r ⊆ R, sem separação s/R (W3a/b); perfis brutos diferentes fora de R com fatores efetivos iguais ⇒ igualdade (δ = 0 efetivo, W2a/b); δ = 7 (W2c); r = ∅ sob `hsame` = igualdade de todos os fatores efetivos (W4a/a′), distinto de R = ∅ onde todos os fatores são 1 sem hipótese (W4b); localização: resposta controlada por |b − c| e separação s/r apenas (W7a); se nenhum polímero toca R e r, a mudança em r é invisível (igualdade exata W7b, δ = 0 via capstone W7c); r = ∅ com separação trivial (W7d).
6. **Falha esperada (W7x)**: capstone com a hipótese bruta da 55 apenas (a = 1/2, a′ = 1/3, R ≠ r) sem `hsame`: exit 1, única falha na obrigação `hsame` (goal `False` para η tocando R). Classificação: falha de aplicação fora das hipóteses; **não** é prova de falsidade nem de indispensabilidade.

## 5. Testes

W0–W7: exit 0 (36 itens positivos; W1 com 1 warning de variável não usada num teste meu). W7x: exit 1 conforme esperado. Deslizes meus, preservados em `*.attempt1.log`/`attempt2.log` e nunca reclassificados como defeito do candidato: goals β-não-reduzidos (`dsimp only`/`rw` após `if_pos`), `rw [if_neg (not_blockTouchesSupport_empty …)]` contra `typedTouchesSupport`, `|1/4| ≤ 1/4` e `|1/6| ≤ 1/6` não fechados por `norm_num` (W7x attempt1 tinha uma segunda falha minha na obrigação `hδ`, corrigida para que só `hsame` falhe). Matriz completa: `56_QA1_TEST_MATRIX.tsv`.

## 6. Documentação

Cabeçalho e docstrings descrevem corretamente hipóteses efetivas, sinal da coluna-ponte, orientação `A′ − A`, ausência de δ ≤ 1 / `DependsOnlyOn` / separação s/R, e a direção 56 ⇒ 55. Observação sem mérito: `…_bridge_two_regions` reprova a rota da interface 55-B (que fixa R = r e não é editável) em vez de derivá-la — inevitável dado o congelamento. Nenhuma imprecisão documental encontrada.

## 7. Comparação com o material do construtor (após a primeira passagem)

- Logs: `clean_build.log` do construtor: 117 Built / 0 Replayed, 0 erros, 114 warnings de projeto com **blocos integrais idênticos** ao baseline 55 e ao meu log (o log do construtor contém adicionalmente 4.599 warnings de Mathlib por ter compilado as dependências da fonte; separados e ignorados); 269 certidões; manifesto antes = depois (`c376bbe9…`); `warnings_candidate_clean.txt` do construtor = minha lista (nível de linha). Início do limpo do construtor 19:03:34Z (661 s) — anterior à minha reconstrução; bancadas independentes.
- Testes V1–V4x (do construtor; identificados como tais): V1–V3 exit 0 e V4x exit 1 (`⊢ a η = a' η` no lema de cancelamento) nos logs do construtor; **reexecutados na minha bancada com os mesmos resultados** (`builder_tests_rerun/`). Não são reprodução independente; minha W7x falha na capstone, não no lema.
- Matrizes: nomes e linhas das 24 declarações coincidem com a minha matriz; certidões 24/24 iguais; `56_NAME_MAP.tsv` documenta a promoção de 4 testes de viabilidade a teoremas.
- Nenhuma divergência entre as minhas conclusões preliminares e o material do construtor.

## 8. Limitações

Não é auditoria cega (§0). Assinatura SSH não verificada independentemente. Dependências do cache local (revisões conferidas), não recompiladas da fonte nesta auditoria. Os testes W usam premissas geométricas abstratas (sem reticulado concreto). Certificação restrita ao escopo formal enunciado: estabilidade localizada do funcional polimérico amortecido por perfis em volume finito no regime KP `β ≤ 1/40000`; **não equivale a certificar o problema de Yang–Mills no contínuo.**

## 9. Vereditos

| eixo | veredito |
|---|---|
| Custódia | **PASS** |
| Execução | **PASS** |
| Matemática | **PASS** |
| Documentação | **PASS** |
| **Global** | **PASS NO ESCOPO** (sem observações de mérito) |

Preservação confirmada: candidato `a2fcf8e9` e base `445cc76b` intactos; `origin/main` = `zenodo-v55` = base; tags `zenodo-v53/54/55` e branches preservadas; nenhuma escrita remota (push desabilitado); worktree limpa. Nenhuma publicação. Pedra 57 não iniciada. **HARD STOP.**

## 10. Pacote de evidências

`QA1_56_evidence.zip` com `SHA256SUMS_56-QA1.txt` (sem auto-inclusão): este relatório, `56_QA1_DECLARATION_MATRIX.tsv` (24 itens), `56_QA1_TEST_MATRIX.tsv`, `PRELIMINARY_CONCLUSIONS_first_pass.md`, `environment.txt`, logs de build dirigido e limpo (+ resultados, instantes, manifestos pré/pós), `warnings_candidate.txt`, `compare_warning_blocks.py`, `warnings_block_comparison.txt`, `tests/` (fontes W e logs, incluindo attempts), `builder_tests_rerun/`. Como o relatório está dentro do ZIP, o SHA do ZIP vai na mensagem de entrega, não aqui.

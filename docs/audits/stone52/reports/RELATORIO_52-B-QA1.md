# RELATÓRIO 52-B-QA1 — Auditoria independente do ledger exato

**Auditor:** Claude Fable 5.1 (segunda instância; bancada pinada isolada, sessão Cowork). **Data:** 2026-09-10 (UTC).
**Exposição prévia declarada:** auditei 52-A0 (QA1), 52-A (QA1) e 52-A-C1 (QA2); a fita informa o alvo esperado. Não vi nenhum material do 52-B antes da segunda passagem. Primeira passagem executada só com bundle + manifesto (integridade); conclusões preliminares registradas em `PRELIMINARY_CONCLUSIONS_first_pass.md` **antes** de abrir relatório, matrizes, testes ou logs do construtor.
**HARD STOP respeitado:** nenhuma alteração nas fontes, commit, amend, push, PR, merge, tag, release ou Zenodo; push do remoto desativado; 52-C não iniciada.

## 1. Custódia (independente)

| Item | Resultado |
|---|---|
| Tarball `STONE52-B-L_evidence.tgz` | SHA-256 `938ee2680dbbc42f83bb03ba844d9b04264ec1b64197f614d79ff91a9945a0d3` ✅; 29 entradas, todas sob `b_out/`, 0 caminhos absolutos ou `..` |
| Bundle | `f82ff9d3…e785` = manifesto do construtor ✅; `git bundle verify` okay com a base presente |
| `main` observada (fetch só leitura) | `d4fb2937864b787dea996f6d474939cb40024d8b` = base pinada → validade sobre a base **e** prontidão de publicação coincidem |
| Candidato | `322f29c331e13f2e257da15c7f6e17fc1efe0e19`, exatamente 1 commit sobre a base, parent exato |
| Trees / blob | tree `61c6eeac4822ccca260468fb1db51a8dbd439000` ✅; Phase3 `805d0b93d581fe3758c0c7d9ca0f141eed4e29e7` ✅; blob `1bf0dc4ab11bb7ae27a1d8d619e962e6fef7b3a6` ✅ (o `.lean` avulso do pacote tem o mesmo `hash-object`) |
| Diff | `A Phase3/LatticeGauge/ActivityDampingLedger.lean` (+435) · `M Phase3/lakefile.toml` (+1/−1: só o glob `LatticeGauge.ActivityDampingLedger` ao final; 107 → 108 globs) — nada mais |
| 107 módulos anteriores | `git diff --quiet base..cand -- <107 .lean>` idênticos ✅; blobs de 51-A…51-E, 52-A0 e 52-A-C1 conferidos um a um; a base contém exatamente o C1 aprovado (`4f40443…`) |
| Workflow, docs, README, LICENSE, toolchain, Phase1/2 | 0 alterações |
| Proveniência | autor **e** committer `Claude Fable 5.1 (Etapa 1) <pesquisaagi4@gmail.com>`, trailer `Co-authored-by: Claude <noreply@anthropic.com>` — padrão dos commits de módulo da cadeia (51-x, 52-A0, C1) |

## 2. Build e axiomas (bancada isolada, pins)

Lean 4.15.0 (`11651562caae`), Lake 5.0.0, Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608`, manifesto `c376bbe9…1227` pré = pós.

| Passo | Comando | Exit | Duração | Resultado |
|---|---|---|---|---|
| Dirigido | `lake build LatticeGauge.ActivityDampingLedger` | 0 | 298 s | 0 erros, 0 warnings no módulo, 0 `sorryAx` |
| Limpo completo | `rm -rf .lake/build && lake build` | 0 | 713 s | **108 módulos**, 0 erros; **prova de reconstrução pura**: os 108 `.olean` de `LatticeGauge` têm mtime posterior ao início registrado (`clean_build_start_utc.txt`); 0 anteriores — sem mistura com artefatos antigos; executado em uma única chamada (sem retomada) |
| Warnings | — | — | — | 114 herdados, distribuição arquivo:linha **idêntica** ao baseline reconstruído sob o mesmo ambiente; 0 no módulo |
| `#print axioms` (meu, 15 declarações públicas) | `tests/p0_print_axioms.lean` | 0 | — | 15/15 `[propext, Classical.choice, Quot.sound]` |
| Léxico (fora de comentários) | — | — | — | 0 `sorry`/`admit`/`axiom`/`native_decide`/`maxHeartbeats`/`set_option`/`filter_congr_decidable`/`@[reducible]`/`classical!`/`nolint`/`decide` |
| Dependências | — | — | — | imports: só `ActivityDampedObservableGas`; **nenhum** uso de 52-A0 (bounds), 51-D, 51-E, `CovarianceDecay`; sem ciclos (build completo) |

## 3. Alvo matemático — verificado pelas definições

- **E_T(θ)** := `Σ' kpSignedUnrootedCoeff n (restrictedActivity (dampedActivity w r θ) (remoteAllowed T s)) − Σ' kpSignedUnrootedCoeff n (dampedActivity w r θ)`: usa a `dampedActivity` de 52-A; ordem **restrito − pleno** (meu teste P4 fecha por `rfl`); predicado `remoteAllowed T s` sobre a atividade já amortecida. θ=0: `dampedActivity_zero` + `restrictedActivity_regionAllowed_remoteAllowed` dão literalmente `regionActivityCoreExponent`; θ=1: `fullActivityCoreExponent`; r=∅: `full`.
- **Razão e normalização:** `gás(restrito(w_θ)|P) / activityDampedPolymerGas = exp(E_T(θ))` por `typedPolymerGas_ratio_eq_exp_sub` (Pedra 50) com KP transportado (`abstractKP_dampedActivity`, 0 ≤ θ ≤ 1). O denominador é **exatamente** o gás amortecido (`unfold`). KP fornece as duas representações exponenciais e, por consequência, a não-anulação; nada é cancelado à mão; a somabilidade vive dentro do lema da Pedra 50 (hipótese KP).
- **Peso:** `θ ^ touchCount r T` — `touchCount` é `card` de filtro (contagem de família, não indicador; teste P2: dois membros → θ²). Tuplas com repetição não entram neste gate (a 52-C usará `tupleTouchCount`).
- **Partição:** `sum_touchingFamilies_eq_activityAllowed_add_bridge` (51-B, união disjunta real). Nos permitidos `θ^t = 1` via `touchCount_eq_zero_iff` (definição). Coluna 1 percorre **todos** os núcleos tocantes; coluna 2 **só** pontes; `hfull` mostra `Σ W e = Σ θ^t W e + Σ_bridge (1−θ^t) W e` sem perda nem dupla contagem (nos permitidos os dois lados coincidem; nas pontes `W e = θ^t W e + (1−θ^t) W e`).
- **Capstone:** `Gibbs − damped = Σ_touching θ^t W (e^{E(1)} − e^{E(θ)}) + Σ_bridge (1−θ^t) W e^{E(1)}` — igual ao alvo da fita, orientação `e^{E(1)} − e^{E(θ)}`. Prova: representação publicada de Gibbs (`gibbsExpectation_eq_sum_core_mul_exp`, com `fullActivityCoreExponent` como abreviação defeq — o `rfl` foi aceito pelo kernel), forma exponencial do amortecido, `hfull`, `ring`. Meu P1 rederiva a identidade nas formas exponenciais.
- **Hipóteses do capstone:** `hβ, mχ, hχabs, hsmall, hf, mf, hCf, 0 ≤ θ ≤ 1`. `hsmall` entra por KP em ambos os lados (P6b: sem ele não instancia). Identidades puramente algébricas (expoente em 0/1/∅, colunas em 0/1/∅, peso permitido) não têm hipóteses. Nenhuma hipótese contém a conclusão; sem circularidade; sem uso antecipado de bounds.
- **Especializações:** θ=0 → `two_column_ledger_zero` colapsa literalmente ao RHS da Pedra 51 (`0^t = 0` nas pontes por `touchCount_pos_of_mem_activityBridgeCores`; `0^0 = 1` nos permitidos por `pow_touchCount_eq_one…`; E(0) = regional), e `…_eq_damping_ledger_zero` **deriva** o enunciado do capstone 51 do capstone 52-B (`rw ← activityDampedExpectation_zero`), não o cita. θ=1 → diferença 0 (só representação, sem smallness) e colunas nulas. r=∅ → diferença 0 e colunas nulas. Permitido → peso 1.

## 4. Testes próprios (matriz completa em `52-B_QA1_TEST_MATRIX.tsv`)

P0 axiomas (15/15) · P1 recomposição por núcleo, abstrata e no módulo (positiva) · P2 duas incidências → θ² (positiva, condicional a dois polímeros tocando r) · P3 endpoints e ∅ **derivados do capstone** (positiva) · P4 orientação (refutação **abstrata** da orientação invertida + `rfl` da definição) · P5 necessidade da coluna ponte (contraexemplo **algébrico abstrato**, explicitamente não uma configuração concreta do modelo; `W_T` poderia ser 0 numa configuração real) · P6a θ=2 e P6b sem `hsmall` (falhas de aplicação esperadas; não são refutações) · P6c controle positivo. Todos com o resultado esperado.

## 5. Segunda passagem — comparação com o construtor

| Item | Construtor | Auditor | Divergência |
|---|---|---|---|
| Módulo avulso | `ActivityDampingLedger.lean` | `hash-object` = blob `1bf0dc4a…` | nenhuma |
| Diff completo | `stone52-b_full.diff` | meu `git diff` | SHA-256 idênticos |
| Build limpo | 2 segmentos (1º `EXIT=124` por limite de 10 min após 101 módulos; 2º `EXIT=0`), 108 módulos distintos, cada um uma vez | 1 chamada, 713 s, 108 | conclusão idêntica; a retomada do construtor está documentada e o log confirma 108 módulos sem duplicata de compilação |
| Warnings | 114 ocorrências / 113 pares | 114 / 113 pares | **o log do construtor lista cada par duas vezes** (o 2º segmento repete os avisos cacheados do 1º) — artefato da retomada, não diferença de conteúdo; conjunto de pares idêntico |
| `#print axioms` | 12/12 limpos | 15/15 limpos (superconjunto: + `_empty_region` do expoente, `gibbsExpectation_eq_sum_core_mul_exp_full`, `ledger_weight_allowed`) | nenhuma |
| Matrizes | 16 declarações; 7 positivos + 5 negativos; endpoints | 16; 9 testes | conteúdo coerente; o B-NEG-5 do construtor ("sem a coluna ponte") é, como o meu P5, um argumento abstrato (`1 − (1/2)^1 ≠ 0`) — ambos honestos sobre isso |
| Nota de execução do construtor | dois `congr 1` trocados por `add_right_inj`/`add_left_inj` + `sum_congr` sem alterar heartbeats | confirmado no código (linhas 259, 262); 0 `maxHeartbeats` | nenhuma |
| Veredito do construtor | "52-B GREEN" | PASS | concordância |

## 6. Interface para a 52-C (obrigações futuras, separadas — não são defeitos deste gate)

1. Inclusão–exclusão amortecida no nível dos coeficientes: `E_T(1) − E_T(θ) = [S_P(w) − S_P(w_θ)] − [S_0(w) − S_0(w_θ)]` = **menos** a soma sobre tuplas que **atingem ambos** os proibidos (P e r) de `(1 − θ^{tupleTouchCount δ})·ursell·∏w/k!` (sinal: a primeira colchete soma só tuplas P-permitidas, a segunda todas; a diferença é −Σ sobre tuplas com algum P-proibido, e `1 − θ^{tc}` só sobrevive onde alguma posição toca r — mesma convenção da 51-C, `full − region = −connector`) — as pontes `kp*Coeff_dampedActivity` de C1 dão o ingrediente; a identidade de conector amortecido ainda não existe. *(ERRATA 2026-09-11: a versão original omitia o sinal negativo; apontado por Sol; sem efeito no capstone auditado.)*
2. Somabilidade das séries envolvidas (KP transportado já disponível).
3. Extração do fator `(1 − θ)` via `one_sub_dampedPow_le_nat_mul_one_sub` (52-A0) e primeiros momentos.
4. Estimativas das duas colunas (orçamentos `(1/2,3)` e `(7/8,1)` de 52-A0).
5. Lema `|e^a − e^b| ≤ |a − b|·e^{max(|a|,|b|)}` compatível com κ = 3 (reserva R2 da QA 52-A0 **continua aberta**; a rota ingênua dá κ = 4 → `e^{10 D_s/113}`).

**A constante final da Pedra 52 não é certificada por este gate.**

## 7. Reservas classificadas

| # | Gravidade | Reserva |
|---|---|---|
| — | nenhuma | Nenhum defeito demonstrado; nenhuma verificação não concluída no escopo do gate. |
| I1 | informativa | `ledger_weight_allowed` é reafirmação de `pow_touchCount_eq_one_of_mem_activityAllowedCores` (interface, inofensiva). |
| I2 | informativa (documental do construtor) | Log de build em dois segmentos duplica a listagem dos warnings herdados; recomendo anotar isso no relatório de release para não sugerir 228 avisos. |
| F1 | futura (52-C) | Lema de diferença de exponenciais para κ = 3 — ver §6.5. |

## 8. Veredito

Identidade exata, verificada pelas definições e pelo kernel; endpoints derivados (não citados); custódia, proveniência e reconstrução limpa comprovadas; sem defeitos.

**`52-B QA1 PASS`**

HARD STOP.

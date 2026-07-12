# FAILURE_ATLAS.md — atlas de modos de falha (conhecimento tácito do Fable)

Cada entrada: sintoma → causa → correção → onde aconteceu. Este atlas
existe para que nenhum sucessor pague de novo pelos mesmos vermelhos.

## Elaboração / instâncias (a HIDRA)
1. **"typeclass instance problem is stuck … metavariables"** ao usar
   lemas de medida → a medida/família está em metavariável quando a
   instância sintetiza. FIX: argumentos explícitos ((μ := …), (K := 1))
   ou `show` na forma exata antes do `exact`. [pedras 12, 14, 15, 17]
2. **Fintype de subtipos tem MÚLTIPLAS instâncias não-defeq**:
   `Subtype.fintype` vs `Fintype.subtypeEq` vs `Set.fintypeRange`.
   Sintoma: "application type mismatch … @Measure.pi … instA vs instB".
   FIX-PADRÃO: `convert h using 2-3` + `exact Subsingleton.elim _ _`.
   PREVENÇÃO: rotas concretas (Measure.pi_eq sobre caixas, dite-
   cilindros) em vez de piCongrLeft/funUnique/piEquiv-reindex.
   piCongrLeft com família constante é INELABORÁVEL neste contexto
   na v4.15 — não insistir. [12: 5 tentativas; 14: idem]
3. **haveI vs letI**: `haveI` esconde o VALOR (default de Unique fica
   opaco; rfl morre). Instâncias cujo valor importa: `letI`. [12]

## Táticas
4. **Goals de `integral_congr_ae` chegam beta-NÃO-reduzidos**: `rw`
   não acha padrão dentro de `(fun U => …) U`. FIX: `show` com o
   enunciado beta-reduzido antes de qualquer rw. [7ª, 11ª, 17ª]
5. **`congr 1` pode fechar tudo sozinho** (funções defeq) e deixar
   `funext` órfão com "no goals". Tentar `congr 1` puro primeiro. [15]
6. **`rw` dependente** ("motive is not type correct") ao reescrever
   índice que aparece em posição dependente. FIX: aplicar a hipótese
   no índice certo e reescrever NA HIPÓTESE (rwa … at h). [14]
7. **`simp` alterna `a ∈ Set.range f` ↔ `∃ y, f y = a`** e desalinha
   dif_pos/dif_neg. FIX: `rw [dif_pos h]` ANTES de simp tocar a
   condição; manter h na mesma forma do goal. [14: duas rodadas]
8. **`positivity` não usa hipóteses do contexto** para atomos como
   0 ≤ C. FIX: mul_nonneg/linarith explícitos. [17]
9. **norm vs abs**: misturar ‖·‖ e |·| quebra rw/simpa (abs_mul
   normaliza diferente). FIX: escolher UMA forma por cadeia; converter
   em hipótese com `rwa [Real.norm_eq_abs] at h`. [5ª, 17ª]
10. **calc de UM passo aninhado** dentro de by dentro de calc → parser
    embola ("expected :=" adiante). FIX: desmanchar em táticas. [17]
11. **`unfold configMeasure`** antes de qualquer padrão `Measure.pi`:
    defs não desdobram em rw. [11, 13, 14]
12. **ite/dite com condição decidível**: `Measurable (fun y => if h : … )`
    com condição INDEPENDENTE de y: `by_cases` no meta-nível + simp
    em cada ramo. [11, 15]

## Nomes/versões (Mathlib v4.15 pinada)
13. Nomes que NÃO existem na v4.15: measurePreserving_swap (usar
    ⟨measurable_swap, Measure.prod_swap⟩), measurePreserving_inv (usar
    ⟨measurable_inv, Measure.map_inv_eq_self⟩), Measure.map_fst_prod
    EXISTE mas trava instâncias — preferir reescrita concreta em
    map-aninhado; MeasurableEquiv topológicos de unitary só existem
    pós-4.15 (portados em HaarUnitary). integral_const_mul →
    integral_mul_left. div_le_iff → div_le_iff₀.
14. `hasDerivAt_integral_of_dominated_loc_of_deriv_le` EXISTE na v4.15
    e devolve `Integrable F' ∧ HasDerivAt …` (usar .2). [18]
15. SEMPRE verificar nome/assinatura no source da tag ANTES de codar
    (curl raw.githubusercontent…/v4.15.0/…). O Sol matou o risco da
    18ª assim; economizou ~3 rodadas.

## Epistemologia (as quedas que importam)
16. **"⟨W⟩ = ∏ integrais de caractere" é FALSA** (χ não distribui
    sobre o produto do grupo). Veto do Sol antes da implementação.
    Rota correta: holonomia é Haar → ⟨W⟩₀ = ∫χ. [14b→15/16]
17. **"Zero hypotheses" era overclaim**: hp/hnd estavam na assinatura.
    Linguagem defensável: "no unproved scientific axioms … only the
    explicit structural conditions". [pós-16]
18. **Parser de auditoria**: comparar nomes de axiomas pelo ÚLTIMO
    componente conta Classical.choice como científico (2-vs-60).
    Whitelist por NOME COMPLETO, script versionado, relatório gerado
    do log bruto. [kernel-xray]
19. **Duplicação de pressupostos é detectável no import**: dois
    axiomas homônimos tornam módulos co-inimportáveis — o kernel
    denuncia de graça.
20. **Contagens**: nunca publicar número que não saia de script
    versionado + dado bruto preservado. Três metodologias = três
    números = zero credibilidade.

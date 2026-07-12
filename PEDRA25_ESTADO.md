# PEDRA 25 — ESTADO PARA PARECER DO ARQUITETO (Sol)

## Alvo (candidata H, conforme tua fila)
Fatorização exata de DOIS loops de Wilson com suportes de links
disjuntos em β = 0:
⟨W_{p1} · W_{p2}⟩₀ = ⟨W_{p1}⟩₀ · ⟨W_{p2}⟩₀,
e o corolário truncatedCorrelation = 0.

## Peças disponíveis (todas verdes na main)
- Beta0.lean: `DependsOnlyOn`, `integral_mul_of_disjoint_support`
  (via piEquivPiSubtypeProd + integral_prod_mul),
  `gibbsExpectation_zero` (⟨f⟩₀ = ∫ f), `truncatedCorrelation_zero_beta_zero`.
- HolonomyHaar.lean: `pathLinks x p : Finset (Link N)` (ou List?
  conferir), `holonomy_congr_on_pathLinks` — o holonomy depende só dos
  links do caminho.
- Translation.lean: `truncatedCorrelation` def.

## Rota proposta (a validar)
1. Lema-ponte: `DependsOnlyOn (fun U => wilsonLoop χ U x p)
   (pathLinksSet x p)` — segue de holonomy_congr_on_pathLinks.
2. Hipótese de disjunção: `Disjoint (pathLinksSet x p₁)
   (pathLinksSet x p₂)` como hipótese EXPLÍCITA do teorema (sem
   tentar decidir geometricamente).
3. Aplicar integral_mul_of_disjoint_support com f₁ = W_{p1},
   f₂ = W_{p2} e gibbsExpectation_zero dos dois lados.
4. Corolário: truncatedCorrelation em β=0 dos dois loops = 0.

## Pontos de atenção nomeados
1. TIPO do suporte: conferir se integral_mul_of_disjoint_support
   pede Set (Link N) ou Finset — adaptar pathLinks/coerção. Risco
   principal de instance-hell (Fintype de subtipos de listas) já
   mapeado no FAILURE_ATLAS (modo: converter via Set + classical).
2. Mensurabilidade: measurable_wilsonLoop já existe; a fatorização
   em β=0 precisa de integrabilidade — em medida produto de
   probabilidade com |W| ≤ 1, usar (integrable_const 1).mono'.
3. Versão U(n): corolário incondicional com uChar/haarU, hipótese
   só de disjunção + fechamento (para o rótulo físico de loop).

## Nota de janela
Sequência 19ª→24ª concluída nesta janela: seis pedras, as CINCO
últimas verdes na primeira rodada. Se tio Dario bater na porta antes
do teu parecer, o estado fica aqui e a 25ª abre a próxima janela.

Aguardo parecer antes de qualquer implementação. — Fable

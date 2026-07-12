# PEDRA19_ESTADO.md — cota de Taylor de 2ª ordem em β = 0 (issue #5)

**Commit main:** c2391e20d7c6054597632136d7d2be78d65f3629  •  Nada implementado; parecer antes de código.

## Alvo

Para β ≥ 0 (ou bilateral em |β| ≤ 1, a decidir), f mensurável |f| ≤ C,
χ ≤ 1, S ≤ B:

    |⟨f⟩_β − ⟨f⟩₀ + β·Cov₀(f,S)| ≤ K(C,B) · β²

com K explícita (proposta inicial, não otimizada: K = 8·C·B²·exp(2B),
a apertar no desenho). Fecha o pacote "análise em β = 0": valor (11ª),
continuidade (17ª), derivada (18ª), e agora o RESTO da 1ª ordem.

## Duas rotas possíveis — decisão do arquiteto

R1 (Taylor com resto integral, sem 2ª derivada dominada):
   ⟨f⟩_β − ⟨f⟩₀ = ∫₀^β d/ds ⟨f⟩_s ds (FTC via HasDerivAt em CADA s,
   não só em 0 — exige generalizar a 18ª para HasDerivAt em s
   arbitrário: mesma prova, dominador exp((|s|+1)B) na bola de s).
   Depois |d/ds⟨f⟩_s − d/dβ⟨f⟩_0| ≤ L·s via… (isso já é quase R2).
R2 (segunda derivada dominada): d²/dβ² do peso = S²·exp(−βS);
   dominar por B²·exp(B) na bola; derivar numerador e Z duas vezes;
   quociente com regra de 2ª ordem — mais peças, todas mecânicas.
R3 (elementar, SEM cálculo extra — candidata do Fable):
   escrever a diferença como integral única:
   ⟨f⟩_β − ⟨f⟩₀ + β·Cov₀ = [expressão em ∫f·(w−1+βS), ∫(w−1+βS), e
   produtos de cotas da 17ª] e usar o L1-refinado:
     0 ≤ x → |exp(−x) − 1 + x| ≤ x²/2   (elementar; Real.add_pow_le?
     provável braçal: convexidade ou série — verificar
     Real.abs_exp_sub_one_sub_id_le? EXISTE em Mathlib p/ |x|≤1:
     |exp x − 1 − x| ≤ x²  — VERIFICAR NOME na v4.15).
   Rota R3 evita QUALQUER derivada nova: só álgebra de quociente
   como na 17ª, com o refinamento quadrático do L1. Aposta do Fable.

## Dependências verdes

Toda a 17ª (cotas, integrabilidades, z⁻¹ ≤ exp(βB)), a 18ª (se R1/R2),
Beta0 (⟨·⟩₀), abs_exp_neg_sub_one_le (a refinar).

## Riscos nomeados

- Nome exato do lema quadrático de exp na v4.15
  (Real.abs_exp_sub_one_sub_id_le : |x| ≤ 1 → |exp x − 1 − x| ≤ x²).
  VERIFICAR ANTES (lição da 18ª). Se só existir p/ |x| ≤ 1, impor
  β·B ≤ 1 na janela ou provar a versão x ≥ 0 na mão (elementar).
- Álgebra do quociente de 2ª ordem é feia; R3 minimiza mas não zera.

## Limites de sempre

Volume finito; sem uniformidade em N; não é expansão convergente.

— Fable

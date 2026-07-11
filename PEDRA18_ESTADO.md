# PEDRA18_ESTADO.md — resposta linear em β = 0 (identidade de covariância)

**Commit main:** 7ea16d984aa3e731966cbd167ceab75db04d941c (17ª mesclada em f112cf6fa762)  •  Nada implementado.

## Alvo central (do arquiteto)

    d/dβ ⟨f⟩_β |_{β=0} = −(⟨f·S⟩₀ − ⟨f⟩₀·⟨S⟩₀) = −Cov₀(f, S)

com S = wilsonAction χ. A primeira conexão explícita entre a
perturbação em β e uma correlação computada no estado produto — a
entrada da expansão de acoplamento forte. LIMITES EXPLÍCITOS: volume
finito; derivada EM β = 0 (não série); nenhuma uniformidade em N.

## Hipóteses exatas propostas

μm probabilidade [SigmaFinite]; χ mensurável com χ ≤ 1 (para peso ≤ 1)
e cota inferior via |χ| ≤ 1 onde preciso; f mensurável com |f| ≤ C;
B cota da ação (exists_wilsonAction_bound); Fintype (Site N), NeZero N.

## Formulação Lean proposta

    HasDerivAt (fun β => gibbsExpectation μm β χ f)
      (−(⟨f·S⟩₀ − ⟨f⟩₀·⟨S⟩₀)) 0

com ⟨·⟩₀ já redutível a integrais (gibbsExpectation_zero).
Nota: HasDerivAt em 0 usa vizinhança bilateral; nosso peso está
definido para todo β real (exp sempre existe) — a restrição física
β ≥ 0 NÃO é necessária para a derivada, o que simplifica (evita
derivadas laterais). Confirmar com o arquiteto.

## Decomposição proposta

D1 (derivada pontual do peso): HasDerivAt (fun β => exp(−β·S U))
    (−S U · exp(0)) 0 = −S U. Composição de HasDerivAt.exp com linear.
D2 (dominação): para β ∈ [−1, 1] (vizinhança de 0),
    |∂/∂β exp(−βS)| = S·exp(−βS) ≤ B·exp(B) — dominador constante
    integrável (probabilidade). Ferramenta Mathlib:
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (nome v4.15 a
    confirmar; família hasDerivAt_integral_of_dominated_*).
D3 (numerador): d/dβ ∫ f·w_β |₀ = −∫ f·S.
D4 (Z): d/dβ Z(β) |₀ = −∫ S; Z(0) = 1 (realZ_zero, 11ª).
D5 (quociente): HasDerivAt.div com Z(0) = 1 ≠ 0:
    (N/Z)' = (N'·Z − N·Z')/Z² em β=0 → −∫fS·1 − (∫f)(−∫S) =
    −(⟨fS⟩₀ − ⟨f⟩₀⟨S⟩₀). ✓
D6 (mensurabilidades): f·S e S integráveis: bounded (|f·S| ≤ C·B) ×
    measurable (measurable_wilsonAction, 5ª) sobre probabilidade —
    padrão das pedras 5/17.

## Dependências já verdes

measurable_wilsonAction, wilsonAction_nonneg, exists_wilsonAction_bound,
integrable_gibbsWeight, realZ_pos/realZ_zero, gibbsExpectation_zero,
toda a álgebra de cotas da 17ª.

## Lemas ausentes / riscos

- Nome e assinatura exata da família hasDerivAt_integral_of_dominated_*
  na v4.15 (RISCO PRINCIPAL — verificar antes de codar; alternativa:
  provar via definição de derivada + squeeze com a cota da 17ª
  refinada a segunda ordem, mais braçal porém sem dependência).
- HasDerivAt.div / deriv de quociente: padrão Mathlib estável.

## Referência

Resposta linear/fórmula de flutuação-dissipação em volume finito:
Friedli–Velenik §3 (derivadas da pressão/estados de Gibbs); qualquer
texto de mecânica estatística rigorosa. Elementar em volume finito.

Contrato de sempre: parecer arquitetural antes de qualquer linha Lean.
— Fable

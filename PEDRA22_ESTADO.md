# PEDRA 22 — ESTADO PARA PARECER DO ARQUITETO (Sol)

## Alvo (conforme fila esboçada por Sol)
Corolários de Wilson-path: especializar o par (20ª, 21ª) ao observável
físico f(U) = χ(holonomy U p) — a resposta do loop de Wilson ao
acoplamento e sua curvatura, em todo β₀ ≥ 0.

## Peças disponíveis (todas verdes na main)
- `hasDerivAt_gibbsExpectation_at_covariance` (20ª) e
  `hasDerivAt_negative_gibbsCovariance_action` (21ª): pedem apenas
  (mf : Measurable f) e (hf : ∀ U, |f U| ≤ C).
- `measurable_holonomy` (WilsonExpectation.lean): mensurabilidade de
  U ↦ holonomy U p sob MeasurableMul₂.
- Cota: com hipótese |χ g| ≤ 1 (∀ g), tomar C = 1. No caso U(n),
  `uChar` já tem |uChar M| ≤ 1 provado (UnitaryChar.lean).
- Composição: f = χ ∘ (holonomy · p); mf = mχ.comp (measurable_holonomy …).

## Enunciados propostos
A. wilsonLoop_response: HasDerivAt (fun β => ⟨W_p⟩_β)
   (−Cov_{β₀}(χ∘hol_p, S)) β₀ — instância direta da 20ª com C = 1.
B. wilsonLoop_second_response: idem da 21ª.
C. (opcional, U(n) concreto) versões com χ = uChar e μm = haarU,
   espelhando o padrão dos capstones incondicionais da HaarUnitary.

## Pontos de atenção nomeados
1. A 20ª exige hχ : ∀ g, χ g ≤ 1 (para positividade/cotas do peso) E
   a cota do OBSERVÁVEL é separada — para f = χ∘hol o natural é
   hipótese adicional hχabs : ∀ g, |χ g| ≤ 1, que implica a primeira.
   Proposta: enunciar A/B com hχabs apenas e derivar hχ internamente
   (fun g => (abs_le.mp (hχabs g)).2).
2. Não há conteúdo novo de integração: a pedra é 100% instanciação.
   Risco principal é só a forma do lambda (χ (holonomy U p)) vs
   composições — resolver com `show` se necessário.
3. Nomenclatura honesta no docstring: resposta pontual exata do loop
   de Wilson em volume finito; nada sobre confinamento, área law ou
   limite termodinâmico.

Aguardo parecer antes de qualquer implementação. — Fable

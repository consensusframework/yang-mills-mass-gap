# PEDRA20_ESTADO.md — resposta linear em β ARBITRÁRIO (Cov_β)

**Commit main:** 49d14b2914534d08891e365c66fec5104739966a (19ª em merge anterior)  •  Nada implementado.

## Alvo (sequência do arquiteto)

Para todo β₀ ≥ 0 (não só zero):

    d/dβ ⟨f⟩_β |_{β=β₀} = −(⟨f·S⟩_{β₀} − ⟨f⟩_{β₀}·⟨S⟩_{β₀}) = −Cov_{β₀}(f,S)

A identidade termodinâmica completa em volume finito.

## Rota proposta: generalização direta da 18ª (mesma máquina)

- D1': HasDerivAt do peso em β₀ qualquer: já provado GERAL na 18ª
  (hasDerivAt_gibbsWeight vale em todo β). ✓ sem trabalho novo.
- D2': dominação na bola ball β₀ 1: |∂w| = S·exp(−βS) ≤ B·exp((|β₀|+1)·B)
  para β ∈ ball β₀ 1 (se β < 0 no bola com β₀ pequeno: exp(−βS) ≤
  exp(|β|S) ≤ exp((|β₀|+1)B)). Dominador constante.
- D3'/D4': derivadas de numerador e Z em β₀: valores
  −∫f·S·w_{β₀} e −∫S·w_{β₀} (não mais os integrais secos!).
- D5': quociente com Z(β₀) > 0 (realZ_pos, já geral). Valor:
  (−∫fSw·Z − ∫fw·(−∫Sw))/Z² = −(⟨fS⟩_β − ⟨f⟩_β⟨S⟩_β). ✓
- D6': integrabilidades de f·S·w e S·w em β₀: padrão bounded×w (17ª).

## Diferenças-chave vs 18ª (os únicos pontos de atenção)

1. As expectativas ⟨·⟩_{β₀} NÃO colapsam para integrais secas — o passo
   final usa a DEFINIÇÃO de gibbsExpectation (razão), não
   gibbsExpectation_zero. Álgebra: (−a·z − n·(−s))/z² = −(a/z − (n/z)(s/z))
   exige dividir por z² e reagrupar — mais delicado que na 18ª;
   proposta: provar primeiro lemma de reescrita
   Cov_β = (∫fSw)/z − (∫fw)(∫Sw)/z².
2. hβ₀ : 0 ≤ β₀ é necessário? Para dominação com exp((β₀+1)B) sim;
   bilateral com |β₀| também ok — proposta: assumir 0 ≤ β₀ (físico) e
   dominador exp((β₀+1)·B).

## Dependências verdes

Toda a 18ª (o lema dominado, hasDerivAt_gibbsWeight geral), realZ_pos,
integrabilidades-padrão, hzinv-padrão.

## Limites

Volume finito; identidade pontual em β₀; nada de série; nada de
uniformidade em N.

— Fable

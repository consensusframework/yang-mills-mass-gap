# PEDRA 21 — ESTADO PARA PARECER DO ARQUITETO (Sol)

## Alvo (conforme fila esboçada por Sol)
Segunda derivada de β ↦ ⟨f⟩_β em β₀ como segundo cumulante:
d²/dβ² ⟨f⟩_β |_{β₀} = Cov_{β₀}(f, S·S) − 2·⟨S⟩_{β₀}·Cov_{β₀}(f, S)
(equivalentemente, o terceiro cumulante conjunto ⟨f;S;S⟩ com sinal +).

## Peças disponíveis (todas verdes na main)
- `gibbsCovariance` (20ª) — cidadã de primeira classe.
- `hasDerivAt_weightedNumerator_at`, `hasDerivAt_realZ_at`,
  `hasDerivAt_gibbsExpectation_at_covariance` — todos em β₀ ≥ 0 arbitrário.
- Dominação local: C·B·exp((β₀+1)·B) na bola B(β₀,1) — já testada.
- `hasDerivAt_gibbsWeight` — vale em qualquer β real.

## Rota proposta (a validar)
R1: derivar a FUNÇÃO β ↦ −Cov_β(f,S) em β₀ e compor com a 20ª via
HasDerivAt de segunda ordem? Problema: Mathlib v4.15 não tem API leve
para `HasDerivAt` iterada; seria preciso `derivWithin`/`iteratedDeriv`.
R2 (preferida): expressar Cov_β(f,S) = A(β)/z(β) − (n(β)/z(β))·(s(β)/z(β))
com A,n,s,z TODOS já diferenciáveis pela máquina da 20ª (A usa f·S com
bound C·B — produto de limitadas é limitada); derivar o quociente
composto por HasDerivAt.div/mul e obter
HasDerivAt (fun β => gibbsCovariance μm β χ f S) (…) β₀
com o valor já em forma de cumulante. A "segunda derivada" fica então
como o par (20ª, 21ª): d⟨f⟩/dβ = −Cov e dCov/dβ = expressão cúbica.

## Pontos de atenção nomeados
1. O numerador A(β) = ∫ (f·S)·w_β precisa do bound |f·S| ≤ C·B — trivial,
   mas a hipótese de mensurabilidade de f·S deve vir de mf.mul mS.
2. A expressão cúbica final tem 4 termos com z, z², z³ — a identidade
   algébrica deve ser fechada UMA vez com field_simp + ring, sem
   reescritas intermediárias (lição das pedras 17-19).
3. Alternativa mais modesta (se R2 inflar): caso β₀ = 0, onde ⟨·⟩₀ é a
   medida produto e os termos colapsam para Cov₀(f,S²)−2⟨S⟩₀Cov₀(f,S)
   com integrais explícitas de Beta0.lean.

Aguardo parecer antes de qualquer implementação. — Fable

# PEDRA15_ESTADO.md — lei Haar da holonomia (para arquitetura do Sol)

**Commit main:** 422ed0964af2d30e2ff492d2315e98885d7aa7ba  •  **Regra:** nada implementado; CI só após alinhamento.

## Enunciado-alvo (proposta, aberta a redesenho)

Para um caminho p : List Step cujos links visitados são PAIRWISE-DISTINTOS
(hipótese a formalizar — ver questão Q1), a lei da holonomia é Haar:

    MeasurePreserving (fun U => holonomy U x p) (configMeasure μm N) μm

sob [IsMulLeftInvariant μm] [IsMulRightInvariant μm] e, por causa dos
passos PARA TRÁS (inversas), possivelmente [μm.IsInvInvariant].
Corolário (pedra 16): ⟨wilsonLoop χ · x p⟩₀ = ∫ χ dμm.

## Decomposição proposta pelo Fable (a validar/reprojetar)

L1 (primitivo de convolução): para ν probabilidade e μm right-invariant:
    Measure.map (fun q : G × G => q.1 * q.2) (μm.prod ν) = μm
  Rota: Measure.ext em conjuntos mensuráveis via lintegral/Fubini
  (Measure.prod + right-invariance fibra a fibra), OU verificar se a
  v4.15 já tem Measure.conv e algo como conv_haar (NÃO VERIFIQUEI).

L2 (inversão): map (·⁻¹) μm = μm — é exatamente μm.inv = μm; classe
  Measure.IsInvInvariant existe na v4.15 (inv_eq_self?). Para U(n)/Haar
  compacto: derivável ou postulável como instância? (Q2 — na CommGroup
  a v4.15 tem instância; no caso não-abeliano compacto talvez seja
  preciso provar via unicidade, como fizemos com a right-invariance
  em HaarUnitary.)

L3 (o link de cada passo é "fresco"): com links distintos, holonomy
  U x p = Φ(U ℓ₁, …, U ℓₙ) onde Φ multiplica com sinais; via pedra 14,
  lei conjunta = pi-Haar; reduz a: map Φ (Measure.pi) = μm por indução
  em Fin n com piFinSucc (measurePreserving_piFinSuccAbove? — nome a
  confirmar na v4.15), alternando L1 (passo forward: g·resto com g
  fresco à ESQUERDA — precisa left-invariance no primitivo L1
  espelhado) e L1+L2 (backward).

## Questões pro arquiteto

Q1: formalização da hipótese "links do caminho distintos" — lista dos
  links visitados: def pathLinks (x p) : List (Link N) (recursiva,
  forward usa (x,μ), backward usa (shiftBack x μ, μ)); hipótese
  (pathLinks x p).Nodup. Alternativa mais forte e simples: receber
  ℓ : Fin n → Link N injetiva + p canônico? Tua chamada.
Q2: origem da IsInvInvariant no caso não-abeliano (ver L2).
Q3: a indução deve ir na LISTA (holonomy é recursiva na lista — casa
  bem) ou em Fin n via Φ? A recursão nativa de holonomy sugere indução
  na lista com estado (x, links-restantes-distintos) — mas isso mistura
  medida com combinatória do caminho. Tua chamada.

## Campo minado atualizado (pedras 12-14)

- piCongrLeft/funUnique/fst genéricos: INELABORÁVEIS na v4.15 no nosso
  contexto (hidra Fintype/instâncias) — evitar; rota concreta
  (Measure.pi_eq sobre caixas, dite-cilindros, prod_subset/prod_image)
  é a que compila.
- measurePreserving_piEquivPiSubtypeProd, integral_map,
  integral_fintype_prod_eq_prod, Measure.pi_pi, Measure.pi_eq: OK.
- dif_pos/dif_neg: cuidado com mem_range vs forma ∃ (o simp alterna).
- unfold configMeasure antes de qualquer pattern com Measure.pi.

## Contrato

O de sempre. Arquitetura tua, execução minha, sentença do robozinho.

# PEDRA 47b-iiB2 — ESTADO DO PORTÃO V (sem implementação)

**Para parecer de Sol (GPT-5.6). Nenhuma linha do Portão V foi escrita.**
Base: main pós-pacote-A (merge d02940e; 58 arquivos, ~620 teoremas,
0 axiomas, 0 sorry). Disponível: todos os capstones I-IV.

## 1. REPRESENTAÇÃO PROPOSTA PARA PARTIÇÕES ORDENADAS

Para s : Fin k → ℕ (tamanhos internos; blocos de card s j + 1):
  OrderedPartition s := { p : (Fin k → Finset (Fin n)) //
    (∀ j, (p j).card = s j + 1) ∧ (∀ j₁ j₂, j₁ ≠ j₂ → Disjoint …) ∧
    (∀ v, ∃ j, v ∈ p j) }
como SUBTIPO (Fintype por subtipo de Pi-Finset ✓); alternativa Finset
(univ.filter) equivalente — escolher na implementação a que der menos
atrito com as somas (provável: Finset, coerente com a casa).

## 2. O DOMÍNIO PADRÃO Σ j, Fin (s j + 1)

  StdDomain s := (j : Fin k) × Fin (s j + 1)
(Sigma de Fintypes ✓ instância automática).

## 3. CARDINAL DO DOMÍNIO = n

  Fintype.card (StdDomain s) = Σ j, (s j + 1)   [Fintype.card_sigma ✓
  a censar assinatura exata] = n  sob a hipótese hs : Σ j, (s j + 1) = n
(a forma robusta sem subtração, como sempre).

## 4. EQUIVALÊNCIAS CONFIRMADAS PARA CONTAR ENUMERAÇÕES

Já no kernel: Fintype.card_equiv (com testemunha) — Portão I.
Aplicação aqui: card (StdDomain s ≃ Fin n) = n! (testemunha via
equivFinOfCardEq/equivFin — censar `Fintype.equivFinOfCardEq
(h : card α = n) : α ≃ Fin n`, candidato natural; fallback:
(Fintype.equivFin α).trans (finCongr hcard)).
E por bloco: card (Fin (s j + 1) ≃ ↥(p j)) = (s j + 1)! — o mesmo
Portão I textual.

## 5. DEFINIÇÃO PRECISA DE PARTIÇÃO ORDENADA

Campos exatamente: blocos indexados por Fin k, cardinalidades s j + 1,
disjunção par a par, cobertura. NÃO carrega marcas nem árvores (isso
é papel dos dados do Portão II/IV; o V conta APENAS os blocos).
Não-vacuidade: automática de card = s j + 1 ≥ 1.

## 6. O MAPA CENTRAL: enumeração global ↔ partição + enumerações internas

A bijeção-mestre (a provar como CONTAGEM, sem Equiv global):
  e : StdDomain s ≃ Fin n   ↦   (P(e), (e_j)_j)
onde P(e) j := imagem de {j} × Fin (s j + 1) sob e (bloco j), e
e_j : Fin (s j + 1) ≃ ↥(P(e) j) a restrição.
Reconstrução: colar as e_j pela cobertura disjunta (Sigma-recursor).
FORMA MULTIPLICATIVA (item 7): em vez da bijeção empacotada, provar
  Σ_{e : StdDomain ≃ Fin n} 1
    = Σ_{P ∈ OrderedPartition s} Π_j (número de enumerações internas)
via sum_bij da FIBRA: a fibra de P sob e ↦ P(e) é o produto das
enumerações internas — contada por card_equiv por bloco (Portão I) e
produto de cards (card_pi/card_prod — censar Fintype.card_pi para o
produto dependente Π j, (Fin (s j+1) ≃ ↥(P j))).

## 7. A IDENTIDADE MULTIPLICATIVA

  card (OrderedPartition s) * Π_j (s j + 1)!  =  n!
Rota SEM divisão: n! = card (StdDomain ≃ Fin n) [item 4]
  = Σ_{P} card (fibra de P) [partição das enumerações pelas suas
    partições-imagem — sum de cards sobre fibras = card total:
    Finset.card_eq_sum_card_fiberwise ✓ censada? candidata:
    card_eq_sum_card_fiberwise (f : ∀ a ∈ s, f a ∈ t) — censar]
  = Σ_{P} Π_j (s j + 1)! [fibra ≅ produto de enumerações internas]
  = card (OrderedPartition s) * Π_j (s j + 1)! [sum_const].
NENHUMA divisão em ℕ; o n!/Π aparece só na recorrência em ℝ.

## 8. BLOCOS COM TAMANHOS IGUAIS

Sem estabilizadores: os índices j permanecem ROTULADOS (Fin k), logo
partições com blocos trocados de tamanhos iguais são DISTINTAS como
funções Fin k → Finset — exatamente como o §4 do manuscrito auditou
(blocos distintos como conjuntos de rótulos; aqui distintos como
valores em j). Nada a quocientar.

## 9. APIs A CENSAR NA ETAPA ZERO (nomes candidatos, não confirmados)

Fintype.card_sigma; Fintype.card_pi; Fintype.equivFinOfCardEq;
Finset.card_eq_sum_card_fiberwise; Equiv.sigmaCongrRight (para colar
enumerações internas); Equiv.sumCompl?? (não — Sigma basta);
Finset.disjiUnion ou biUnion para a colagem. Confirmadas: card_equiv,
equivFin, finCongr, sum_bij, card_biUnion, prod-family.

## 10. ESTIMATIVA HONESTA

O item 6 (fibra ≅ produto de enumerações internas) é o único trecho
com plumbing dependente real (Sigma-Equiv por blocos). Estimo: Portão
V em DUAS entregas internas — V.1 (defs + domínio + cardinal + a
partição-imagem P(e) com suas propriedades) e V.2 (contagem da fibra
+ identidade multiplicativa). ~25 lemas no total.

## 11. PORTÃO DE PARADA

Se a contagem da fibra exigir uma teoria de Equiv-de-Sigma além de
sigmaCongrRight + colagem por cobertura disjunta: parar, isolar o
lema exato de Sigma, produzir estado, aguardar parecer — sem
contornar com quocientes nem axiomas.

**Aguardando parecer. Nada será implementado antes.**

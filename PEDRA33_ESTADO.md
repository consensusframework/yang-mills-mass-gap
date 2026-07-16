# PEDRA 33 — CONCLUÍDA (2026-07-16)

## Resultado
VERDE em TRÊS rodadas. Arquivo: Phase3/LatticeGauge/PlaquetteConnectivity.lean
6 defs (plaqLinkSet, plaquetteShareLink, plaquetteGraph, connectedWithin,
plaquetteComponent, blockLinkSupport) + 12 teoremas (simetria da relação;
refl/symm/trans de connectedWithin; mem_iff; capstones A-G; capstone
geométrico dos suportes disjuntos).
Placar: 33 pedras, 32 arquivos, ~183 teoremas, 0 axiomas.

## APIs de SimpleGraph REALMENTE usadas (critério do arquiteto)
- SimpleGraph (estrutura: Adj/symm/loopless) — Basic.lean:91.
- SimpleGraph.induce (via comap Subtype.val; Maps.lean) — adjacência
  induzida é DEFEQ à ambiente: o `show (plaquetteGraph N).Adj a b`
  atravessa a coerção sem lema auxiliar.
- SimpleGraph.Reachable (Path.lean:652) + .symm/.trans.
- SimpleGraph.Walk.nil / Walk.cons (reflexividade e passo de aresta
  sem depender dos nomes Reachable.refl/Adj.reachable).
- NÃO usados (conforme ordem): ConnectedComponent, quocientes,
  representantes canônicos.

## Dificuldades do induce (registro exigido)
Nenhum bloqueio estrutural. O subtipo ficou 100% encapsulado em
connectedWithin; proof irrelevance fez ⟨q,hq⟩/⟨q,hq'⟩ coincidirem
de graça no trans. Vilões das rodadas foram periféricos:
(1) docstring não pode preceder 'open ... in' (parser);
(2) DecidablePred de connectedWithin em Finset.filter: lemas de
    filter SINTETIZAM a instância em vez de unificar — cura:
    open scoped Classical no arquivo (instância única).
Ambos no atlas agora.

## Escolha de admissibilidade (das duas opções que deste)
Adjacência puramente geométrica + certificação explícita
A ⊆ admissiblePlaquettes em TODOS os teoremas públicos de componentes
(padrão IsClosed). A combinatória vale para qualquer A; a hipótese
certifica a instanciação física e impede índice inválido silencioso.

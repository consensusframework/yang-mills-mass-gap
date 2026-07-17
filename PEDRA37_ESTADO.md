# PEDRA 37 — MAPA: A CAMADA FINITA DO log Z
# (encomenda do parecer da 36ª; NENHUMA implementação até autorização)

## Cadeia-alvo (ainda 100% finita)
polímeros → incompatibilidade → grafo de incompatibilidade →
coeficientes conectados/Ursell → identidade combinatória finita
para log Z.

## Separação obrigatória (tua disciplina, mantida à letra)
(a) IDENTIDADE FORMAL FINITA para log Z — combinatória exata;
(b) ESTIMATIVAS dos coeficientes (Ursell/árvores);
(c) CRITÉRIO DE CONVERGÊNCIA (Kotecký-Preiss ou similar);
(d) UNIFORMIDADE EM VOLUME.
Este mapa cobre APENAS o desenho de (a). (b)-(d) são pedras futuras
com estados próprios.

## 1. O problema matemático central de (a)
A identidade clássica: se Z = Σ_Γ ∏_{X∈Γ} w(X) (36ª ✓), então
formalmente log Z = Σ_{(X₁..Xₙ) ordenadas?} φ(X₁..Xₙ) ∏ w(Xᵢ)/n!
com φ = coeficiente de Ursell sobre o grafo de conexão. PROBLEMA
FORMAL: em volume finito, Z > 0 ✓ (realZ_pos... CUIDADO: realZ_pos
exige β ≥ 0 e χ ≤ 1; os PESOS w(C) são assinados e Z como soma do
gás é positiva só pela identidade com a integral — usar realZ_pos
da via integral ✓). Mas a série de Ursell é INFINITA mesmo em volume
finito (tuplas de tamanho arbitrário com repetições). Logo (a) NÃO
pode ser "log Z = série" sem convergência. Opções honestas:
  A1. Identidade TRUNCADA com resto explícito: log Z = Σ_{n≤M} ... +
      R_M, com R_M em forma fechada (integral/forma de Taylor do log).
      Exata, finita, mas o resto carrega o peso.
  A2. Identidade de POLINÔMIO: como o número de polímeros é finito,
      exp/log podem ser tratados via a álgebra de séries formais
      TRUNCADAS em nilpotência? Não — pesos são reais, não nilpotentes.
  A3. (recomendação do executor) Adiar log Z e fazer de (a) a
      INFRAESTRUTURA COMBINATÓRIA PURA, sem análise: definição do
      grafo de incompatibilidade; def de coeficiente de Ursell
      φ(X₁..Xₙ) via soma sobre subgrafos conexos geradores
      (Σ_{G ⊆ E conexo gerador} (−1)^{|E(G)|}); lemas estruturais
      (φ = 1 para n = 1; φ = 0 se o grafo de conexão é desconexo;
      simetria sob permutações). ISTO é finito, exato e verificável —
      e é o que (b) e (c) consomem. log Z entra só junto com (c).

## 2. Peças existentes
- Grafo de incompatibilidade: já temos a relação
  (¬ PlaquetteCompatible); como SimpleGraph sobre allPlaquettePolymers?
  ATENÇÃO: incompatibilidade NÃO é irreflexiva (X é incompatível
  consigo). Modelagem: grafo sobre ÍNDICES de uma tupla/multiconjunto
  com aresta i~j ↔ ¬compatível(Xᵢ,Xⱼ) — sempre com i ≠ j na aresta;
  laços tratados fora do grafo. Reuso: SimpleGraph/induce/Connected
  da 33ª; conexidade de subgrafos GERADORES é noção nova
  (spanning connected subgraph) — reconhecimento de
  SimpleGraph.Subgraph.Connected/spanning no source v4.15 obrigatório.
- Somas sobre subconjuntos de arestas: Finset.powerset ✓ (32ª).
- Sinais (−1)^k: Int/ℝ powers ✓ trivial.

## 3. Candidata concreta para a 37ª (nível (a), rota A3)
Arquivo UrsellCoefficients.lean:
  - def connectionGraph (X : Fin n → Finset Plaq) : SimpleGraph (Fin n)
    com adj i j := i ≠ j ∧ ¬ PlaquetteCompatible (X i) (X j);
  - def ursell (X) : ℝ := Σ_{E ⊆ edgeFinset, spanning-conexo} (−1)^|E|
    (representação por Finset de Sym2/pares — DESENHO DO TIPO a teu
    critério: Finset (Fin n × Fin n) filtrado i < j evita Sym2);
  - teoremas: ursell (n=1) = 1; se connectionGraph desconexo então
    ursell = 0 (partição das arestas entre componentes fatoriza a
    soma e Σ(−1)^|E| de um fator livre = 0 — o argumento clássico de
    involução; NÚCLEO combinatório da pedra, custo MÉDIO-ALTO);
    invariância por permutação de índices.
- SEM log Z nesta pedra (entra na pedra do critério (c), onde a
  convergência dá sentido à série).

## 4. Riscos nomeados
1. "Spanning connected subgraph" na Mathlib v4.15: pode não existir
   pronto; alternativa local: conexidade via nossa connectedWithin
   sobre Fin n com a adjacência restrita a E (reuso do padrão da 33ª
   com grafo paramétrico em E) — evita Subgraph API inteira.
2. A involução para "desconexo ⟹ 0": escolher aresta fixa fora…
   (não: o argumento certo é fatorização + soma geométrica (1−1)^m).
   Desenho detalhado no estado da implementação, se autorizada.
3. Tuplas com repetição (Fin n → polímeros, não Finset): correto para
   Ursell (a série usa multi-índices) — sem deduplicação prematura.

## Perguntas ao arquiteto
(i) Aprova a rota A3 (infraestrutura de Ursell sem log Z) como (a)?
(ii) Desenho do tipo para arestas: pares i < j em Finset (Fin n ×
    Fin n), ou Sym2 (Fin n)?
(iii) O teorema "desconexo ⟹ 0" entra na 37ª ou fica para a 38ª
    (37ª só definições + n=1 + permutação)?

Aguardo parecer. — Fable

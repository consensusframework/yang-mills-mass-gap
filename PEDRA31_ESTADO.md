# PEDRA 31 — ESTADO PARA PARECER DO ARQUITETO (Sol)
## Duas rotas, conforme encomendaste no parecer da 30ª

## Rota A: PÓS-COMPOSIÇÃO COORDENADA A COORDENADA
Funções mensuráveis φᵢ : ℝ → ℝ aplicadas coordenada a coordenada
preservam a joint tuple law:
map (fun U i => φᵢ (fᵢ U)) = pi (map φᵢ ∘ map fᵢ... )
- Peças: iIndepFun.comp (verificado na 29ª, linha 566 do source) já
  dá a independência mútua da família composta (fun i => φ i ∘ f i);
  a 30ª-A aplicada à família composta fecha o teorema em DUAS linhas.
- Mensurabilidade: (mφ i).comp (mf i).
- Marginal: Measure.map (φᵢ ∘ fᵢ) μ = Measure.map φᵢ (Measure.map fᵢ μ)
  via Measure.map_map (mφ i) (mf i) — dá o enunciado "bonito"
  map da tupla composta = pi (map φᵢ (marginal fᵢ)).
- Custo: BAIXO. Pura instanciação, estilo 22ª.
- Ganho: qualquer estatística derivada de Wilson loops disjuntos
  (potências, funções teste, indicadoras) herda a lei-produto.

## Rota B: JOINT TUPLE LAW PARA BLOCOS
Particionar ι em blocos B₁,...,B_k de índices; o vetor de VETORES
(um por bloco) tem lei-produto das leis conjuntas dos blocos.
- Peças candidatas: iIndepFun sobre o tipo de índices de blocos com
  variáveis a valores em (∀ i ∈ B_j, ℝ) — exige iIndepFun com
  MeasurableSpace heterogêneo (a def suporta: β : ι → Type*);
  a hipótese seria construída de indepFun_finset iterado ou de um
  critério próprio de interseções por blocos.
- Custo: MÉDIO-ALTO. O bookkeeping de tipos dependentes
  (∀ i : (B j : Finset ι), ℝ) é exatamente a região de subtipos que
  evitamos até aqui. Viável, mas merece desenho cuidadoso do
  enunciado ANTES (qual é o consumidor? a expansão de cluster usa
  blocos de polímeros — pode valer o investimento agora ou quando a
  necessidade concreta aparecer).

## Recomendação do executor
A agora (fecha o capítulo probabilístico β=0 com API de composição
completa e barata); B adiada até termos o consumidor concreto
(polímeros), com estado próprio e desenho de tipos revisado por ti.

## Nota de janela
19ª→30ª: DOZE pedras nesta janela. Se o parecer chegar com a janela
viva, a 31ª entra hoje; senão, este estado abre a próxima.

Aguardo parecer e escolha. — Fable

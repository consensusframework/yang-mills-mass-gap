# PEDRA 32 — MAPA DE ARQUITETURA: PRIMEIRO PASSO RUMO À EXPANSÃO DE
# CLUSTER (documento de planejamento; NENHUMA implementação até parecer)

## 1. INVENTÁRIO — o que a Fase 3 JÁ possui para suporte/localidade/
## correlações (tudo verde na main, 31 pedras)
- Geometria de suportes: pathLinkSet, familySupport (existencial),
  dependsOnlyOn_mono, dependsOnlyOn_mul_union, DependsOnlyOn de
  produtos finitos (26ª) e de indicadoras de eventos (29ª).
- Fatorização exata em β=0: binária (11ª), família finita (26ª),
  one-vs-block do 3º cumulante (27ª).
- Probabilidade em nível de medida: IndepFun binária (28ª), iIndepFun
  mútua (29ª), joint tuple law (30ª), estabilidade por pós-composição
  (31ª), bloco-vs-bloco via indepFun_finset.
- Análise em β: continuidade (17ª), derivada (18ª), Taylor (19ª),
  flutuação-resposta em β₀ arbitrário (20ª), 2ª resposta (21ª),
  respostas de Wilson (22ª), log-partição (23ª), variância ≥ 0 (24ª).
- Cota uniforme da ação: exists_wilsonAction_bound (B = 2·#plaquetas).
- truncatedCorrelation def + |·| ≤ 2C² (Translation.lean) e
  anulação exata em β=0 para suportes disjuntos.

## 2. DEFINIÇÃO MÍNIMA DE POLÍMERO necessária
Para o regime de acoplamento forte (expansão em β pequeno), o objeto
mínimo é o POLÍMERO DE PLAQUETAS:
- Plaq N := Site N × Dir × Dir (com μ.val < ν.val) — o conjunto de
  índices já existe implicitamente na soma da wilsonAction.
- Um polímero = Finset (Plaq N) CONEXO na adjacência "compartilha
  link". Exige: def plaqLinkSet : Plaq N → Finset (Link N) (os 4
  links da plaqueta) e a relação de adjacência
  adj P Q := (plaqLinkSet P ∩ plaqLinkSet Q).Nonempty.
- Conexidade: a noção de Finset conexo sob uma relação — na Mathlib
  via SimpleGraph.Connected em subgrafo induzido? (candidato:
  SimpleGraph on Plaq N com adjacência acima + G.induce ↑X e
  Connected) — VERIFICAR nomes v4.15 antes de qualquer código.
- Atividade do polímero: z(X, β) = ∏_{p ∈ X} (e^{−β s_p} − 1) com
  s_p = 1 − χ(plaquette)... — na nossa normalização,
  gibbsWeight = exp(−β·S) com S = Σ s_p, então o produto de Mayer é
  ∏_p ((e^{−β s_p} − 1) + 1); a 19ª já controla |e^{−βs} − 1| ≤ βB·e^{βB}
  termo a termo (BetaPerturbation.abs_gibbsWeight_sub_one_le é o
  análogo global; precisará da versão POR PLAQUETA — barata).

## 3. CANDIDATA A PRIMEIRA PEDRA PEQUENA E FINITA (32ª)
"MAYER EXPANSION IDENTITY — nível (a) puramente algébrico":
  gibbsWeight β χ U = ∏_{p ∈ Plaquetas} (1 + m_p(U))
  com m_p(U) := e^{−β·s_p(U)} − 1, e a expansão
  Z = Σ_{A ⊆ Plaquetas} ∫ ∏_{p∈A} m_p — a soma finita sobre
  subconjuntos (Finset.prod_add / Finset.sum_pow... o lema exato é
  Finset.prod_add: ∏ (1 + f i) = Σ_{A ⊆ s} ∏_{i∈A} f i — VERIFICAR
  nome v4.15: candidato Finset.prod_add ou Finset.prod_one_add).
  É identidade FINITA e exata: sem convergência, sem limite. Junto:
  - fatoração exp: gibbsWeight = ∏_p exp(−β s_p) (exp de soma finita,
    Real.exp_sum ✓ existe);
  - |m_p| ≤ β·b_p·e^{β·b_p} com b_p = cota local (via a máquina da 19ª).
  Custo estimado: 1 arquivo, 4-6 teoremas, risco BAIXO (álgebra +
  Finset, nossa zona quente). NÃO menciona polímeros ainda — é o
  degrau (a) que qualquer rota de cluster expansion precisa.

## 4. DEPENDÊNCIAS EXATAS DA MATHLIB (a verificar no source antes
## de codar — lição permanente)
- Real.exp_sum (∏ exp = exp Σ) — quase certo que existe.
- Finset.prod_add (∏(f+g) = Σ sobre subconjuntos) — VERIFICAR forma.
- Para conexidade (pedras 33+): SimpleGraph, Subgraph.Connected,
  possivelmente SimpleGraph.Walk — região NUNCA usada por nós;
  reconhecimento obrigatório.
- Para a futura soma sobre polímeros: Finset.powerset ✓.

## 5. OBSTÁCULOS CONHECIDOS
- Combinatória: conexidade de Finsets e contagem de árvores
  (Cayley/rooted trees) para as cotas de Kotecký–Preiss — é o osso
  duro das pedras 34+; NADA disso é necessário para o degrau (a).
- Mensurabilidade: m_p é composição de exp com wilson local — as
  peças (measurable_plaquette, mχ) existem; risco baixo.
- Uniformidade em N: as atividades locais têm cotas INDEPENDENTES de
  N (b_p ≤ 2), mas o NÚMERO de plaquetas cresce com N⁴ — a separação
  honesta abaixo é essencial nos docstrings.

## 6. SEPARAÇÃO OBRIGATÓRIA (nomenclatura dos docstrings)
(a) IDENTIDADE ALGÉBRICA FINITA — exata, sem análise (32ª proposta);
(b) ESTIMATIVA DE CONVERGÊNCIA — série de polímeros para β pequeno,
    critério de Kotecký–Preiss (pedras futuras, custo alto);
(c) UNIFORMIDADE EM VOLUME — constantes independentes de N (só
    depois de (b));
(d) CONSEQUÊNCIA PARA CLUSTERING — decaimento exponencial de
    truncatedCorrelation, o precursor do mass gap em acoplamento
    forte (Osterwalder–Seiler; o alvo real do roadmap).
Cada pedra declara EXPLICITAMENTE em qual nível vive; nenhuma alega
os níveis seguintes.

Aguardo parecer sobre: (i) a candidata do §3 como 32ª; (ii) a
definição de polímero do §2 para as 33+; (iii) se o degrau (a) deve
incluir já a versão por-plaqueta da cota |m_p|. — Fable

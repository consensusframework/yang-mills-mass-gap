# PEDRA 33 — MAPA DE ARQUITETURA: CONECTIVIDADE POR COMPARTILHAMENTO
# DE LINK (documento de planejamento; NENHUMA implementação até parecer)

## 1. Objeto a formalizar
A relação de adjacência entre plaquetas admissíveis e a noção de
subconjunto CONEXO — o pré-requisito para "polímero" ganhar cidadania.

## 2. Representação recomendada (após reconhecimento no source v4.15)
- plaqLinkSet : Site N × Dir × Dir → Finset (Link N) — os 4 links da
  plaqueta (leitura direta da def de plaquette: (x,μ), (x+μ,ν),
  (x+ν,μ), (x,ν)). Custo: 1 def + lema "plaquette depende só de
  plaqLinkSet" (espelho do wilsonPath_dependsOnlyOn, via congr nos 4
  fatores — barato, sem indução).
- Adjacência: adj P Q := P ≠ Q ∧ (plaqLinkSet P ∩ plaqLinkSet Q).Nonempty
  — irreflexiva e simétrica por construção (∩ comuta via inter_comm).
- Grafo: SimpleGraph (Site N × Dir × Dir) com essa adjacência.
  APIs REAIS conferidas hoje no source (Combinatorics/SimpleGraph):
  - SimpleGraph.Reachable (Path.lean:652): Nonempty (Walk u v);
  - SimpleGraph.ConnectedComponent (Path.lean:808): Quot G.Reachable;
  - SimpleGraph.Connected (Connectivity/Connected.lean) e
    SimpleGraph.Subgraph/induce para restringir a um Finset.
- Conexidade de um Finset A: proposta SEM subgrafos —
  def LinkConnected (A : Finset Plaq) : Prop := ∀ P ∈ A, ∀ Q ∈ A,
    existe caminho DENTRO de A ligando P a Q. Duas opções:
  (i) (G.induce ↑A).Connected — canônica, mas induce vive em subtipo
      ↑A (região de instance-hell conhecida);
  (ii) fecho indutivo próprio: Inductive ReachIn (A) : Plaq → Plaq →
      Prop com passos por adj dentro de A — evita subtipos, e as
      provas por indução são nossas conhecidas. RECOMENDO (ii) para
      as 33-34, com ponte para (i) adiada até precisarmos de
      teoremas prontos de SimpleGraph.

## 3. Separação obrigatória (continuação da disciplina a/b/c/d)
- 33ª (proposta): APENAS as definições + lemas estruturais:
  simetria/irreflexividade da adjacência; suporte da plaqueta;
  DependsOnlyOn de ∏_{p∈A} m_p sobre a UNIÃO dos plaqLinkSets
  (reuso da 26ª: familySupport + dependsOnlyOn_finsetProd);
  fatorização das INTEGRAIS de produtos de atividades sobre
  subconjuntos com suportes de links disjuntos (reuso direto da
  26ª aplicada a f_p := m_p!) — os blocos A₁, A₂ link-disjuntos dão
  ∫ ∏_{A₁∪A₂} m = (∫ ∏_{A₁} m)(∫ ∏_{A₂} m). Nível (a) ainda.
- Decomposição em componentes conexas da soma de Mayer
  (Σ_A = Σ sobre partições em componentes): pedra 34+, exige a
  combinatória de partição — SEPARADA das estimativas.
- Estimativas de convergência (Kotecký–Preiss): 35+.

## 4. Observação de reuso (o ponto forte deste mapa)
A fatorização de blocos disjuntos de plaquetas NÃO precisa de código
novo de medida: m_p depende só de plaqLinkSet p (lema barato do §2);
a 26ª (integral_finsetProd_of_pairwise_disjoint_support) e a 29ª/30ª
(independência/tuple law) aplicam-se textualmente com
supp := união dos plaqLinkSets do bloco. O capítulo probabilístico
inteiro construído nas pedras 25-31 vira infraestrutura do capítulo
de clusters — como planejado.

## 5. Perguntas ao arquiteto
(i) aprova a rota (ii) (ReachIn indutivo próprio) para conexidade,
    com ponte a SimpleGraph adiada?
(ii) a 33ª deve incluir já a fatorização de blocos link-disjuntos de
    atividades (§3, reuso da 26ª), ou só as definições estruturais?
(iii) nome do predicado: LinkConnected ou PlaquetteCluster? (reservar
    "polymer" para quando a decomposição em componentes existir?)

Aguardo parecer. — Fable

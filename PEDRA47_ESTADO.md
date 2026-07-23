# PEDRA 47 — ESTADO E MAPA DO CAPÍTULO KP (sem implementação)

**Para parecer de Sol (GPT-5.6). Nenhuma linha de Lean foi escrita para a 47ª.**
Base: main pós-46ª (50 arquivos, ~470 teoremas públicos, 0 axiomas, 0 sorry).
A hipótese KP está verificada: Σ_{D≁C} |w_β(D)|e^{|D|} ≤ |C| para
0 ≤ β ≤ 1/40000. O capítulo agora é o TEOREMA que a consome.

## A. SÉRIE DE CLUSTERS ENRAIZADA — formulação

Objeto-alvo (versão enraizada, a que o teorema KP controla):
  T(γ₀) := Σ_{n≥0} (1/n!) Σ_{γ₁..γₙ ∈ polímeros}
             |φ(γ₀,γ₁,…,γₙ)| ∏ᵢ |w(γᵢ)|
DECISÃO DE FORMULAÇÃO a fixar no parecer: com ou sem |w(γ₀)| na frente
(a literatura usa ambos; para o bound de log Z por polímero a forma SEM
o fator de γ₀ é a que fecha a indução — recomendo SEM, com o fator
aplicado na 48ª). Indexação: tuplas γ : Fin n → Polymer com o φ da 37ª
(que JÁ aceita multiplicidades e é invariante por permutação — 38ª:
exatamente o que o 1/n! precisa).

## B. BOUND POR ÁRVORES — consumo da 43ª

|φ(γ₀,…,γₙ)| ≤ Σ_{T árvore rotulada em ⊤_{Fin(n+1)}} ∏_{(i,j)∈T} hardCore(γᵢ,γⱼ)
= ursellCoeff_hardCoreTree_bound, pronto. O que falta: reorganizar o
produto de árvore como produto sobre ARESTAS ORIENTADAS a partir da
raiz 0 (a penroseTree/parent da 40-41 dá a orientação canônica de
qualquer árvore — infraestrutura NOSSA, sem censo novo).

## C. INDUÇÃO DAS FOLHAS — o coração

Forma da indução (por n, sobre a soma das tuplas com árvore fixa):
  Σ_{γ_folha ≁ γ_pai} |w(γ_folha)| e^{|γ_folha|} ≤ |γ_pai|  [= hipótese KP!]
consumida folha a folha, de fora pra dentro. Formalização proposta:
lema de "poda": para árvore T com folha n (relabel da 38ª traz a folha
para o último índice), a soma sobre γₙ fatoriza contra o único vizinho
pai, e o que sobra é a soma da árvore podada com peso extra e^{...}
absorvido — AQUI mora o uso do e^{α|D|}: o fator e^{|γ_pai|} que a
hipótese entrega paga as futuras arestas do pai. Custo: a maior
indução do capítulo; estimo pedra própria (47b) com ~15 lemas.

## D. FATOR 1/n! — cancelamento

Rota limpa: Σ sobre tuplas ORDENADAS com 1/n! = Σ sobre árvores
enraizadas rotuladas... a contagem clássica: para cada árvore
enraizada em 0 com n+1 vértices, as n! ordenações dos rótulos 1..n
são absorvidas pelo 1/n! ⟹ o bound final por γ₀ vira
  T(γ₀) ≤ Σ_{n} (bound da indução C)^n / algo — a forma exata do
majorante (e^{|γ₀|} ou |γ₀|·const^...) deve sair do mapa detalhado
da 47b; NÃO afirmo a fórmula antes da conta. O mapa da 47a deve
FECHAR essa álgebra no papel (documento, sem Lean) antes de qualquer
implementação — proponho que a 47a SEJA esse documento técnico
(ESTADO estendido com a prova em papel, linha a linha, para parecer),
dado que este é o teorema mais delicado do programa até aqui.

## E. CONVERGÊNCIA ABSOLUTA — noção da Mathlib

Para o gás FINITO no volume fixo, a "série" em n é FINITA (tuplas de
polímeros distintos-ou-não mas o suporte total é finito e φ = 0 quando
o grafo de incompatibilidade é desconexo — cuidado: repetições tornam
γ incompatível consigo mesma? ¬Compat(γ,γ) = suportes não disjuntos =
VERDADEIRO ⟹ o grafo com dois índices iguais é CONEXO entre eles...
a série NÃO trunca trivialmente; a convergência vem do decaimento
(2β)^{|γ|}). DECISÃO: usar Summable sobre Σ (n : ℕ), (Fin n → Polymer)
(tipo sigma contável — Summable em ℝ, Mathlib padrão) OU manter tudo
como bounds uniformes de somas parciais (como a 46ª fez) e SÓ na 48ª
introduzir Summable. Recomendo a segunda: coerente com nossa
disciplina finita, adia a única API nova (tsum) para quando for
inevitável.

## F. IDENTIFICAÇÃO COM log Z — mantida separada

realZ = Σ_Γ ∏ w (36ª) e a exponencial da série de clusters: a
identificação exige a álgebra exp/log das séries formais truncadas —
capítulo 48, condicionado à 47. Registrar: realZ > 0 já existe
(condicional a bound B — conferir hipóteses exatas da pedra antiga).

## PROPOSTA DE DIVISÃO

47a: DOCUMENTO técnico (prova em papel da indução KP finita com nossas
     constantes exatas, incluindo a decisão A e a álgebra D) — parecer;
47b: infraestrutura de tuplas/poda (relabel da 38ª + fatorização da
     soma da folha) — Lean;
47c: indução completa + capstone T(γ₀) ≤ (majorante explícito) — Lean;
48:  Summable + identificação com log realZ.
Uma frente por vez; 47b/47c só após o papel da 47a aprovado.

## O QUE NÃO ENTRA (em nenhuma sub-pedra da 47)

log realZ, analiticidade, derivadas, limite termodinâmico, clustering,
massa; otimização de constantes; qualquer frase de convergência antes
da 47c fechada.

**Aguardando parecer. Nada será implementado antes.**

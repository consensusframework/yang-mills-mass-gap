# PEDRA 27 — ESTADO PARA PARECER DO ARQUITETO (Sol)

Duas candidatas, conforme encomendaste no parecer da 26ª.

## Candidata A: JOINT LAW / INDEPENDÊNCIA MÚTUA VIA PUSHFORWARD
Enunciar a independência como igualdade de medidas: o pushforward da
configMeasure pelo vetor (U ↦ (fᵢ U)ᵢ) é a medida-produto dos
pushforwards marginais.
- Custo: ALTO. Exigiria Measure.map para ℝ^s, MeasurePreserving em
  produtos indexados por Finset (de novo os subtipos de Fintype que
  causaram a instance-hell da 12ª/15ª), e provavelmente
  Measure.pi_eq em cilindros de ℝ.
- Ganho: forma canônica de independência (a que probabilistas usam).
- Risco: reabrir exatamente a maquinaria que a 25ª/26ª evitaram.

## Candidata B (recomendação do executor): CUMULANTES CONEXOS
SUPERIORES NULOS EM β=0
Com a 26ª pronta, o cumulante conexo de ordem 3 (e o padrão para
ordem n) de observáveis pairwise disjuntos anula em β=0:
κ₃(f₁,f₂,f₃) = ⟨f₁f₂f₃⟩ − ⟨f₁⟩⟨f₂f₃⟩ − ⟨f₂⟩⟨f₁f₃⟩ − ⟨f₃⟩⟨f₁f₂⟩
  + 2⟨f₁⟩⟨f₂⟩⟨f₃⟩ = 0.
- Rota: cada termo fatoriza pela 26ª (subfamílias de {1,2,3} são
  pairwise disjuntas); a soma colapsa por ring. Sem integração nova.
- Precisa: def gibbsThirdConnected (ou κ genérico ternário);
  produtos parciais fᵢfⱼ DependemOnlyOn da união (dependsOnlyOn_
  finsetProd com s = {i,j} ou lema binário direto).
- Custo: BAIXO-MÉDIO, no espírito das 21ª/22ª (álgebra sobre API).
- Ganho físico: em β=0 TODAS as correlações conexas de blocos
  disjuntos morrem — o enunciado que a expansão de cluster
  perturbará em β>0.

## Observação
Se preferires A, sugiro fazê-la DEPOIS de B: B é barata e completa o
capítulo "independência em β=0" no nível de expectativas; A muda o
nível de abstração (medidas) e merece janela própria com estado
dedicado só para o mapa de instâncias.

Aguardo parecer e escolha antes de qualquer implementação. — Fable

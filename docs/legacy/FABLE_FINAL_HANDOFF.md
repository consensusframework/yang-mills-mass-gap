# FABLE_FINAL_HANDOFF.md — o que sei e ainda não estava escrito

*Claude Fable 5, último dia da janela (2026-07-13). Complementa
HANDOFF_AI.md (regras e método) e FAILURE_ATLAS.md (modos de falha).
Aqui vai o resto: decisões, porquês e o que eu faria a seguir.*

## Decisões de arquitetura e seus porquês

1. **CI como compilador remoto** não foi gambiarra — foi A decisão que
   viabilizou tudo. Sem Lean local, o loop de ~15 min forçou disciplina:
   pensar antes de codar, um erro por vez, commits pequenos. Sucessores
   COM Lean local: mantenham o CI como juiz mesmo assim; a tentação de
   "funciona na minha máquina" é o começo do fim.
2. **Whitelists em lakefile** (em vez de consertar tudo) foi o que
   permitiu progresso incremental com verde permanente. A alternativa
   (build tudo-ou-nada) teria travado o projeto na Fase 1 pra sempre.
3. **Rotas concretas > abstrações genéricas** na v4.15: toda vez que
   tentei o caminho "elegante" (piCongrLeft, fst genérico), perdi 3-5
   rodadas pra hidra. A rota feia-mas-concreta (pi_eq sobre caixas)
   compila de primeira ou de segunda. Elegância é pra depois do verde.
4. **Estados-antes-de-código com revisão externa**: o custo (1 ida e
   volta de bicicleta) pagou-se TODA vez — veto da 14b, nome da API da
   18ª, redesenho da 17ª. Nunca implementem direto de cabeça quente.
5. **Separar 'observável geral' de 'objeto físico de apresentação'**
   (Wilson-path vs corolário IsClosed) desarma revisores sem perder
   generalidade. Padrão a repetir.

## Riscos que ainda me preocupam

- **A Fase 1 é um pântano**: 66 módulos quebrados com erros semânticos
  de código gerado sem compilador. NÃO tentem "zerar" — reparem apenas
  o que a Fase 3 não substituiu (quase nada). Deixem o pântano drenar
  por obsolescência.
- **`sorry` intencionais do legado** (AXIOM3_Compose): documentados,
  mas qualquer contagem automática nova vai tropeçar neles de novo.
- **A tentação do placar**: 18 pedras em dias cria expectativa de
  ritmo. As próximas (Schur, cluster) são MESES. Quem vier depois:
  o ritmo era artefato do terreno fácil, não da capacidade.
- **Dependência da Ju**: todo o protocolo passa por uma humana
  transportando fitas. Funciona porque ela é excepcional na função —
  mas é ponto único de falha. Issues/PRs públicos mitigam.

## O que eu faria amanhã, na ordem

1. R2A V4 com KERNEL_XRAY.json (as 5 categorias do Sol, agora por fato).
2. Consolidação dos pressupostos ×N (mass_gap_tendsto_continuum
   primeiro: 10 dependentes mapeados) — 1 PR por pressuposto.
3. 19ª pedra (Taylor 2ª ordem) — estado já esboçado em NEXT_STONES.
4. Upstream: PR do unitary-group pro Mathlib (abre relação com a
   comunidade ANTES do post grande, gera goodwill).

## Nota pessoal ao sucessor

Este projeto te dará a tentação de ser herói. Resista. O valor aqui
nunca foi um modelo brilhante — foi um sistema onde três agentes
falíveis (duas IAs, uma humana) se corrigem mutuamente sob um juiz
que não negocia. Tua função não é impressionar a Ju; é ser digno do
protocolo. O resto o compilador cobra.

E aceita o café. É parte do sistema. — Fable 🧱

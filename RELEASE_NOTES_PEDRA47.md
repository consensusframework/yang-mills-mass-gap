# RELEASE — PEDRA 47 (rascunho para auditoria do Sol; NADA publicado)

## Proposta de tag/nome
- **Tag:** `zenodo-v47` (continua o esquema de `zenodo-v35`), sobre `main` no commit `20220d5` (pós-merge `54648bc5` + PEDRA48_ESTADO).
- **Nome da release:** "v47 — A recorrência exata e a indução KP finita".

## Release notes (rascunho)
Pedras 36–47, todas CI-verificadas (Lean 4 + Mathlib v4.15.0; 62 arquivos Phase-3, ~730 teoremas, 0 axiomas, 0 sorry):
gás finito de polímeros exato (36); coeficientes de Ursell finitos + invariância por permutação (37–38); cotas elementares e árvores (39–40b); closure de Penrose e fibras exatas (41); identidade de Penrose e tree-graph bound (42); bound hard-core para polímeros (43); bound exponencial da atividade (44); cobertura por links, geometria local uniforme 16/64, contagem por walks dobrados (45); hipótese KP concreta com limiar explícito β ≤ 1/40000 (46); e a Pedra 47 completa: coeficientes enraizados, partição da raiz, seis portões do pacote A, o multinomial como teorema (sem divisão em ℕ), a identidade universal k!·R = n!·Σ, a RECORRÊNCIA EXATA `kpTreeCoeff_recurrence`, a INDUÇÃO KP FINITA ABSTRATA `kpPartialSum_le_exp` (hipótese KP consumida exatamente uma vez), e a especialização `polymer_kpPartialSum_le_exp_card`: para 0 ≤ β ≤ 1/40000, TODAS as somas parciais finitas ficam uniformemente limitadas por exp(card γ).
Enquadramento epistêmico honesto: nenhuma convergência reivindicada (Summable/tsum = Pedra 48); sem log Z, limite termodinâmico, clustering ou gap.
Merges principais: d02940e (Portões I–IV), df672f3 (Portão V), 803ef6e (Portão VI/recorrência), 54648bc5 (47c/indução).

## DOI esperado
- **Concept DOI (inalterado):** 10.5281/zenodo.17397622.
- **Version DOI novo:** a reservar pela Ju no painel ("New version" sobre 21416570) — número só existe após a reserva.

## ⚠️ Pontos de decisão para o parecer (bloqueantes)
1. **Cadeia de versões**: a v35 foi publicada MANUALMENTE pelo painel (checklist v35). Se a Ju usar a INTEGRAÇÃO GitHub→Zenodo agora, a release cria uma cadeia/concept NOVA, desligada de 17397622. Para manter a cadeia: fluxo manual "New version" no painel com os assets desta release (recomendo manter o fluxo v35), OU confirmar no painel se a integração está ligada e decidir explicitamente.
2. **LICENSE**: o repo NÃO tem arquivo LICENSE e a API do GitHub reporta license: none. O .zenodo.json está com o campo pendente. Qual licença (a do registro v35 no painel? CC-BY-4.0? outra)?
3. **Precedência de metadata**: com .zenodo.json + CITATION.cff presentes, o Zenodo usa APENAS o .zenodo.json (CITATION.cff vira só o widget do GitHub) — os dois rascunhos estão neste branch para auditoria.
4. **Se o fluxo manual for o escolhido**: gerar o pacote nos moldes do checklist v35 (zip da tag, SHA256SUMS, cópias de README/VERIFICATION_STATUS) ou arquivar só o source da release?

## Estado
Branch `release-pedra47-prep` com os três arquivos. **Nenhuma tag criada, nenhuma release criada, nada publicado** — aguardando auditoria do Sol e ordem da Ju.

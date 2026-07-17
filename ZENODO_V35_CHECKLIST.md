# CHECKLIST DE PUBLICAÇÃO — ZENODO v35 (ordem obrigatória, parecer Sol)

## Bloqueios (NADA de PDF antes destes)
[ ] 1. Ju: painel Zenodo → registro 20432205 → "New version" →
      RESERVAR o DOI novo (Zenodo mostra o DOI reservado no rascunho).
[ ] 2. Ju: confirmar o CONCEPT DOI no painel (cadeia "All versions").
      Só depois disso afirmar qualquer coisa sobre resolução de
      citações antigas.
[ ] 3. Ju: verificar se 17397623 existe como registro separado no
      painel (interligar ou documentar).
[ ] 4. Fable: sincronizar main + CI verde + criar tag `zenodo-v35`.
[ ] 5. Fable: censo sobre a tag (pedras, arquivos, teoremas exatos por
      grep/contagem) + SHA do commit + link do workflow verde.

## Preenchimento
[ ] 6. Inserir no .md: DOI reservado, Concept DOI, SHA, tag, CI link,
      contagens exatas (4 placeholders da seção 5 + 2 da seção 8).
[ ] 7. Status de reprodutibilidade da análise de 110 configurações
      (linha da tabela §3): Ju confirma se dados/scripts originais
      foram recuperados; redigir conforme o achado.

## Geração do pacote
[ ] 8. Yang_Mills_v35_Reassessment_and_Continuation.pdf (do .md).
[ ] 9. yang-mills-mass-gap-v35-source.zip (git archive da tag).
[ ] 10. SHA256SUMS.txt (de todos os arquivos do pacote).
[ ] 11. PHASE3_VERIFICATION_SUMMARY.md (gerar do VERIFICATION_STATUS
      na tag).
[ ] 12. REPOSITORY_RECONSTRUCTION_NOTE.md (seção 6 expandida).
[ ] 13. README.md (cópia da tag).

## Upload e metadados (Ju)
[ ] 14. Subir os 7 arquivos na nova versão (NÃO importar o PDF v34 —
      fica preservado na versão anterior).
[ ] 15. Título novo: "From Conditional Formalization to an Axiom-Free
      Finite-Lattice Program: Reassessment and Continuation of a
      Multi-Phase Lean 4 Project Around the Yang–Mills Mass Gap".
[ ] 16. Metadados: Resource type Preprint; Language English;
      Programming language Lean 4 (corrigir "Python"); identifier
      ORCID truncado ("ttps://") corrigido.
[ ] 17. Keywords: Lean 4; formal verification; interactive theorem
      proving; Yang–Mills theory; lattice gauge theory; Haar measure;
      Wilson loops; cluster expansion; conditional formalization;
      human–AI collaboration; repository reconstruction.
[ ] 18. Publicar.

## Pós-publicação
[ ] 19. Fechar Issue #8 com link da v35.
[ ] 20. README do repo: adicionar link/DOI da v35 na citação.
[ ] 21. Confirmar cadeia "All versions" pública e resolução do
      concept DOI.

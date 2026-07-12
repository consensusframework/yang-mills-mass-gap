# NEXT_STONES.md — o caminho adiante (estados prontos e esboços)

## Autorizadas/desenhadas (estados nas branches pedraNN-sol)
- 19ª (proposta): cota de Taylor 2ª ordem em β=0 —
  |⟨f⟩_β − ⟨f⟩₀ + β·Cov₀(f,S)| ≤ K·β². Junta 17+18; fecha o pacote
  "análise em β=0". Ferramentas: mesmas da 18ª + segunda derivada
  dominada OU Taylor com resto integral. Volume finito.
- R2A V4 + consolidação de pressupostos: usar KERNEL_XRAY.json para
  (a) um axioma canônico por pressuposto (política nunca-Gemini),
  (b) wrappers viram `alias`/`theorem := axiom` explícitos,
  (c) PRs pequenos por módulo, 3 jobs verdes cada.

## Médio prazo (meses, com comunidade)
- Expansão de caracteres: ortogonalidade de Schur em compactos —
  hoje AUSENTE no Mathlib; é PR upstream natural antes da física.
- Decaimento exponencial (área/perímetro) em acoplamento forte.
- Transfer matrix e gap espectral (HasLatticeMassGap, Translation.lean).
- Uniformidade em N — só via cluster expansion de verdade.

## PRs Mathlib candidatos
- Instâncias topológicas de Matrix.unitaryGroup + compacidade (HaarUnitary).
- Right/inv-invariance de Haar em compactos não-abelianos (via unicidade).
- SecondCountableTopology (Matrix …) e o pattern de solda Subsingleton.

## Pendências operacionais
- Fase 1: 10/76 módulos verdes; reparos guiados por PHASE1_BUILD_STATUS.
- Emails de Actions da Ju (desligar notificações).
- Zenodo: nova versão com o código atual (o DOI antigo descreve o v33).

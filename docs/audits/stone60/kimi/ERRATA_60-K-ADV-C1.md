# ERRATA_60-K-ADV-C1 — Adendo documental ao RELATORIO_60-K-ADV.md

**Sobre:** `RELATORIO_60-K-ADV.md` (22.892 bytes, SHA-256 `e7f3017956618af438dad11ac735e29c6cc21079d407db84657497a02329ebe3`) — primeira revisão adversarial da Pedra 60, candidato `778e2c7b27f0357110ba83e9b466984747577823`.
**Origem das observações:** coordenação (FITA 60-K-ADV-C1, transmitida por Ju). As três observações são **da coordenação, posteriores à primeira passagem**; não são descobertas minhas.
**Natureza:** adendo documental. O parecer original permanece preservado, byte a byte; o candidato não foi modificado; nenhum build foi repetido; nenhuma execução Lean ocorreu nesta errata.
**Data desta errata:** 2026-11-22 (UTC) / 2026-11-23 (UTC+8) — ver item 3.

---

## C1.1 — §1.4 do parecer: caminhos alterados na consolidação 59-DOC-P

**Observação da coordenação:** a frase "apenas em `docs/` e `formalization.yaml`" omite `README.md` e `VERIFICATION_STATUS.md`, também editados na consolidação.

**Verificação executada por mim nesta errata:** `git diff --name-only dcd6e6b18a909914dd789667d9830bff106bc762 2ef6500deeb5dd7ddd70c5f208f690e9e0470353` (ambos os objetos buscados do remoto público; `dcd6e6b1…` é hoje `refs/heads/stone59`). Resultado — **20 caminhos**:

- `README.md` ← **omitido no parecer**
- `VERIFICATION_STATUS.md` ← **omitido no parecer**
- `formalization.yaml`
- 17 caminhos sob `docs/`: `docs/audits/stone59/…` (15 arquivos: provenance, readme, checksums, transcrições Gemini e Kimi, pacotes de evidência, parecer de publicação, matrizes e relatório QA1, ferramenta de verificação), `docs/stone58/RESULTS.md`, `docs/stone59/RESULTS.md`.

**Correção:** a frase correta é "apenas em `README.md`, `VERIFICATION_STATUS.md`, `docs/` e `formalization.yaml`".

**Impacto:** nenhum sobre a conclusão relevante do §1.4 — que a árvore `Phase3/` permaneceu idêntica entre o candidato da 59 e o pai da 60. Essa conclusão não dependia da lista nominal: foi verificada independentemente por (i) identidade da árvore Phase3 (`c3157cb9d428b74f73bf789588a3ab2f48d429e7`, a mesma da FITA_59) e (ii) `diff -r` byte a byte entre o snapshot congelado e `git archive 2ef6500d Phase3` (120/120 módulos idênticos). Os dois caminhos omitidos são documentais, fora de `Phase3/`. Veredito inalterado.

## C1.2 — §5 do parecer: exemplo de componente vazia, testemunha explícita

**Observação da coordenação:** para `m = 0` e `aref ≡ 2`, explicitar a condição que produz a contradição — um polímero `η` que toca `R`, no qual a referência tem fator efetivo 2, irreproduzível por membros em `[0,1]`; se usado apenas `R ≠ ∅`, indicar o lema que fornece esse polímero, ou enunciar o exemplo com a testemunha explícita.

**Verificação executada por mim nesta errata (base v59 congelada):** busquei um lema pronto da forma "`s ≠ ∅ ⇒ ∃ polímero tocando s`" e **não o encontrei** no pacote. O mais próximo, `not_blockTouchesSupport_empty` (`ObservableGas.lean`, l.182), é a direção oposta (o conjunto vazio nunca é tocado). Portanto aplico a segunda alternativa da coordenação: o exemplo passa a ser enunciado com **testemunha explícita**, construída a partir das definições que li na fonte:

1. Seja `ℓ = (x, μ) ∈ R` (de `R ≠ ∅`). `Link N = Site N × Dir` (`Basic.lean`, l.23), `Dir = Fin 4` (`Basic.lean`, l.20).
2. Plaqueta admissível por `ℓ`, em dois casos:
   - se `μ.val < 3`: `p := (x, μ, ⟨μ.val + 1, ⋯⟩)`. Admissível pelo filtro `μ.val < ν.val` de `admissiblePlaquettes` (`PlaquetteActivity.lean`, l.38–40); `ℓ = (p.1, p.2.1)` é o primeiro dos quatro lados de `plaqLinkSet p` (`PlaquetteConnectivity.lean`, l.40–43);
   - se `μ.val = 3`: `p := (shiftBack x ⟨0, ⋯⟩, ⟨0, ⋯⟩, μ)`, com `shiftBack` (`WilsonLoop.lean`, l.17) inverso do `shift` de contorno periódico (`Basic.lean`, l.31). Admissível (`0 < 3`); `ℓ` é o segundo lado de `plaqLinkSet p`: `(shift (shiftBack x 0) 0, μ) = (x, μ)`.
3. O polímero testemunha é o singleton `η := ⟨{p}, ⋯⟩ : Polymer N`: `IsPlaquettePolymer {p}` (`PolymerGeometry.lean`, l.54–56) se fecha com não-vacuidade do singleton, `p` admissível, e `connectedWithin_refl` (`PlaquetteConnectivity.lean`, l.76) para a conexão intrínseca. Logo `{p} ∈ allPlaquettePolymers N` (`PolymerGas.lean`, l.221–224).
4. `typedTouchesSupport η R` vale: `blockTouchesSupport` é `¬ Disjoint (blockLinkSupport {p}) R` (`ObservableBlockFactorization.lean`, l.58–60) e `ℓ` pertence a ambos. Então `touchFactor R aref η = aref η = 2` (definição de `touchFactor`, `ActivityProfileDamping.lean`, l.72–74), enquanto para qualquer membro `x` da componente, `touchFactor R x.prof η = x.prof η ≤ 1`.
5. Com `m = 0`, a hipótese `x.reach : Reaches R r aref x.prof` força `touchFactor R aref η = touchFactor R x.prof η` para **todo** `η` (não há índice que testemunhe mudança), ou seja `2 = x.prof η ≤ 1` — contradição. A componente é vazia.

**Registro honesto de escopo:** os passos 2–4 dependem de fatos geométricos elementares lidos por mim nas definições (filtro de admissibilidade, os quatro lados de `plaqLinkSet`, inversão `shift ∘ shiftBack`, reflexividade de `connectedWithin` via lema nomeado). Não encontrei um único lema da base que empacote "`R ≠ ∅` ⇒ polímero tocando `R`"; a testemunha acima é a forma explícita pedida pela coordenação. A verificação é por leitura, como todo o resto desta revisão (limitação L1 do parecer original).

**Impacto:** nenhum sobre o conteúdo do §5 — a conclusão (a componente pode ser vazia, e os teoremas do módulo valem vacuamente nesse caso) permanece; o exemplo fica agora com testemunha explícita em vez de apoiado na frase abreviada "`R ≠ ∅`". Veredito inalterado.

## C1.3 — Cabeçalho do parecer: data da revisão

**Observação da coordenação:** o parecer traz `2026-11-23` e foi recebido em `2026-11-22` no horário de São Paulo; informar o fuso ou a fonte da data, corrigindo-a apenas se foi erro de registro.

**Esclarecimento:** não foi erro de registro — foi **fuso não declarado**. A data `2026-11-23` veio do relógio local do meu ambiente de execução, em **UTC+8** (no momento da entrega: 2026-11-23, ~03:5x UTC+8). As leituras equivalentes eram **2026-11-22, ~19:5x UTC** e **2026-11-22, ~16:5x em São Paulo (UTC-3)** — consistente com o recebimento registrado pela coordenação em 2026-11-22, e com o timestamp do próprio commit candidato (`2026-11-22T13:06:36Z`).

**Precisão adotada:** o cabeçalho do parecer deve ser lido como "Data da revisão: 2026-11-23 (fuso do ambiente, UTC+8; equivalente a 2026-11-22 em UTC e em São Paulo)". Para o ledger: daqui em diante declaro o fuso junto à data.

**Impacto:** nenhum. Veredito inalterado.

---

## Reavaliação do veredito

As três observações são de precisão documental: (C1.1) uma lista de caminhos incompleta cuja conclusão dependia de verificação independente mais forte (identidade de árvore e diff byte a byte), já registrada; (C1.2) um exemplo que passa de abreviado a explicitamente testemunhado; (C1.3) um fuso não declarado, sem erro de data. Nenhuma toca o candidato, as provas, as interfaces ou a custódia.

**Veredito mantido: PASS NO ESCOPO** para o candidato `778e2c7b27f0357110ba83e9b466984747577823`, sob as mesmas limitações L1–L3 do parecer original.

O parecer original permanece preservado e inalterado; esta errata é documento separado. Nenhuma modificação, publicação, commit, push, tag ou escrita no candidato foi feita ou autorizada.

**HARD STOP.**

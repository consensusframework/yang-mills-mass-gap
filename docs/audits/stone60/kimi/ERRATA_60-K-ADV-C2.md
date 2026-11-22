# ERRATA_60-K-ADV-C2 — Identificação da árvore Phase3 do candidato

**Sobre:** `RELATORIO_60-K-ADV.md` (22.892 bytes, SHA-256 `e7f3017956618af438dad11ac735e29c6cc21079d407db84657497a02329ebe3`), §1.3.
**Origem da observação:** coordenação (FITA 60-K-ADV-C2, transmitida por Ju). A discrepância foi apontada pela coordenação; não é descoberta da primeira passagem.
**Natureza:** correção de um valor registrado no ledger de custódia. Parecer original e ERRATA_60-K-ADV-C1 preservados, byte a byte; candidato não modificado; nenhuma execução Lean.
**Data desta errata:** 2026-11-22 (UTC) / 2026-11-23 (UTC+8, fuso do ambiente).

---

## C2.1 — Verificação nos objetos Git (comandos e resultados)

Com o candidato extraído do bundle `stone60_candidate.bundle` (mesma cadeia de custódia do parecer original):

```
$ git rev-parse 778e2c7b27f0357110ba83e9b466984747577823:Phase3
ffabe44339920053581a294929ab8a094d329b77

$ git ls-tree 778e2c7b27f0357110ba83e9b466984747577823 -- Phase3
040000 tree ffabe44339920053581a294929ab8a094d329b77	Phase3

$ git rev-parse 778e2c7b27f0357110ba83e9b466984747577823^{tree}
a7295ffe3dd1bec2496a1353f7a2fd8665490199

$ git rev-parse 2ef6500deeb5dd7ddd70c5f208f690e9e0470353:Phase3
c3157cb9d428b74f73bf789588a3ab2f48d429e7
```

**A coordenação está correta.** A árvore Phase3 do candidato `778e2c7b…` é **`ffabe44339920053581a294929ab8a094d329b77`**, e não `6f408214…` como registrado no §1.3. A árvore raiz do candidato (`a7295ffe…`) e a árvore Phase3 do pai (`c3157cb9…`) estavam e permanecem corretas no parecer.

## C2.2 — Origem do valor incorreto `6f408214…`: identificada

O valor veio da **minha própria rotina de recomputação em Python**, não de nenhum objeto Git. Diagnóstico reproduzido nesta errata:

1. A rotina obteve as entradas com `git ls-tree 778e2c7b… Phase3/` (pathspec com barra final). Nessa forma, o `ls-tree` imprime os nomes das entradas **com o prefixo do caminho**: `Phase3/LatticeGauge`, `Phase3/lake-manifest.json`, `Phase3/lakefile.toml`, `Phase3/lean-toolchain`.
2. Objetos de árvore Git armazenam **apenas o nome base** de cada entrada (`LatticeGauge`, `lakefile.toml`, …), sem o prefixo do diretório.
3. A rotina usou os nomes com prefixo no corpo da árvore recomputada. O resultado é o hash de uma árvore malformada — e reproduz **exatamente** `6f40821434929b7949dafc91dfd5b63e02d4484d`, confirmando a origem determinística do erro.
4. Controle: aplicada ao pai, a mesma rotina defeituosa produz `928d9034…` (também incorreto, mesmo defeito), enquanto o valor correto é `c3157cb9…`. O parecer não carrega esse segundo valor incorreto porque, para o pai, o §1.3/§1.4 usou a saída direta do `git rev-parse`, não a recomputação Python.
5. Correção aplicada e validada: removendo o prefixo `Phase3/` dos nomes, a recomputação independente em Python produz `ffabe44339920053581a294929ab8a094d329b77` para o candidato e `c3157cb9d428b74f73bf789588a3ab2f48d429e7` para o pai — **ambos idênticos aos valores do Git**. A subárvore `Phase3/LatticeGauge` do candidato também foi recomputada: `62c5fc4f73b3bf42dddb14304764a53afa28aedb`, idêntica ao `git rev-parse 778e2c7b…:Phase3/LatticeGauge`.

Nota de simetria: a recomputação da **árvore raiz** (`a7295ffe…`) não foi afetada pelo defeito, porque `ls-tree` sem pathspec imprime nomes de entrada sem prefixo — e aquele valor foi ainda por cima validado contra o cabeçalho do commit. O defeito só apareceu na chamada com pathspec de diretório, que era justamente a única recomputação sem valor de referência cruzado na primeira passagem. Lição registrada: nenhuma recomputação entra no ledger sem conferência contra `git rev-parse`.

## C2.3 — Impacto nas conclusões de custódia e no veredito

O valor corrigido era **registro de ledger**; nenhuma conclusão do parecer dependia dele. Re-verifiquei nesta errata as duas conclusões que de fato pesavam:

1. **O candidato toca exatamente dois caminhos.** Diff direto entre as árvores:
   ```
   $ git diff --name-status c3157cb9d428b74f73bf789588a3ab2f48d429e7 ffabe44339920053581a294929ab8a094d329b77
   A	LatticeGauge/ActivityProfileDampingOptimalGeometry.lean
   M	lakefile.toml
   ```
   Idêntico ao §1.3/§1.4 (adição do módulo + uma linha de glob no lakefile). ✓
2. **A Phase3 do pai é a base v59 congelada.** `c3157cb9d428b74f73bf789588a3ab2f48d429e7` — a mesma árvore declarada na FITA_59 e validada na primeira passagem por `diff -r` byte a byte contra o snapshot (120/120 módulos). ✓

A cadeia upload ≡ blob ≡ bundle, a identidade do módulo (`fbf6452a…`, SHA-256 `035a9cd5…`), a identidade do diff anexado e o veredito não são afetados.

**Veredito mantido: PASS NO ESCOPO** para o candidato `778e2c7b27f0357110ba83e9b466984747577823`, sob as mesmas limitações L1–L3 do parecer original.

O parecer original (`RELATORIO_60-K-ADV.md`) e a primeira errata (`ERRATA_60-K-ADV-C1.md`) permanecem preservados e inalterados; esta é a correção documental separada. Nenhuma modificação, publicação, commit, push, tag ou escrita no candidato foi feita ou autorizada.

**HARD STOP.**

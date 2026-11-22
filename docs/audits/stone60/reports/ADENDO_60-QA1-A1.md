# ADENDO 60-QA1-A1 — fechamento da pendência de custódia do `RELATORIO_60-L.md`

Data (UTC): 2026-11-22T16:25Z. Auditor: Claude, modelo de sessão `claude-fable-5-2`. Refere-se ao `RELATORIO_60-QA1.md` (12.352 bytes, SHA-256 `30b0880bc866922eca31c5791efa85043f6419fbe0ee835b2f2acd65da477a18`), §2 e §7.

## Resultado

**Pendência FECHADA.** O conteúdo recebido do `RELATORIO_60-L.md` coincide com a referência da 60-L.

| | Bytes | SHA-256 |
|---|---|---|
| Referência (60-L / fita) | 14.107 | `ced9b68d2226bf1fcc40be10e93aa189043898241126916b4c18ad97114a8666` |
| Observado | 14.107 | `ced9b68d2226bf1fcc40be10e93aa189043898241126916b4c18ad97114a8666` |

## Modalidade (declaração obrigatória)

O relatório chegou outra vez como **texto colado na conversa**, com o rótulo `RELATORIO_60-L (1).md`; nenhum arquivo foi gravado na área de anexos da sessão. Por isso não calculei o hash de um arquivo recebido em bytes. O que fiz:

1. Extraí o texto colado, sem redigitar, do registro literal da sessão, do título `# RELATÓRIO 60-L …` até a última linha `… HARD STOP.`.
2. Codifiquei em UTF-8 e testei quatro variantes de fim de linha. O texto colado não traz a quebra de linha final, então ela é uma hipótese de reconstrução, não um dado recebido.

| Variante | Bytes | SHA-256 | |
|---|---|---|---|
| LF, sem quebra final | 14.106 | `e089b7d6…c857db` | |
| **LF, com quebra final** | **14.107** | **`ced9b68d…8666`** | **coincide** |
| CRLF, com quebra final | 14.185 | `ced0a5f0…3e18` | |
| CRLF, sem quebra final | 14.183 | `c466ae68…7395` | |

A variante usual de um arquivo de texto (LF com quebra final) reproduz tamanho e hash da referência. Uma coincidência de SHA-256 não acontece por acaso, então o texto que eu li é, byte a byte, o arquivo de referência da 60-L. A cópia reconstruída acompanha este adendo como `RELATORIO_60-L.reconstructed.md`.

O texto colado na abertura da 60-QA1 e o colado agora produzem o mesmo corpo. Logo, o relatório do construtor que usei na segunda passagem da auditoria é o de referência.

## Efeito sobre o parecer

- Custódia passa de "PASS, com uma pendência não bloqueante" a **PASS**. Veredito global: **PASS NO ESCOPO**, sem pendência de custódia.
- Execução, matemática e documentação: inalteradas. Build e testes não foram repetidos.
- As demais limitações do §7 permanecem (assinatura presente e não autenticada; dependências de cache; auditoria não cega).

## Preservação

`RELATORIO_60-QA1.md` e `QA1_60_evidence.zip` (62.131 bytes, SHA-256 `bf966c2f2883e23ba5d22f4026f2d4ef3905482851fb2672f6f6e7399f98d899`) não foram alterados; este adendo é um arquivo separado e não entra no ZIP. Candidato `778e2c7b27f0357110ba83e9b466984747577823` e worktree intocados. Nenhuma escrita remota, integração ou publicação.

**HARD STOP.**

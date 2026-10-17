# ERRATA 58-K-ADV-C1 — Correções pontuais do relato da revisão adversarial da Pedra 58

Coordenação: Jucelha Carvalho. Fita de origem: FITA_58-K-C1 (Can / GPT Astra, 16/10/2026).
Autor da errata: Kimi (Moonshot AI), mesma instância de conversa que emitiu o parecer original.
Data desta errata: 2026-10-16.

Esta errata corrige o **relato** da revisão adversarial. Nenhum defeito matemático do candidato foi identificado — nem pela coordenação nesta conferência, nem por mim nesta reconferência. O parecer original e esta errata devem ser lidos juntos.

## 1. Documento ao qual se aplica

```text
RELATORIO_58-K-ADV.md
Bytes: 20432
SHA-256: 348c163fe5327488d3437dfd77219b2d52544659c6066643aa90f7d473176e33
```

Bytes e hash recomputados nesta sessão sobre o arquivo intacto em `/mnt/agents/output/`; coincidem com o registro da coordenação na fita C1.

Alvo científico preservado (inalterado): merge `69706b9a13a23b0f132418f2390d4030e1fcc78b`, candidato `d942edd3986ac8cb13a8d5958bf1e11461434794`, módulo `ActivityProfileDampingAdditiveCover.lean`, blob `9d0274fd94ee2cb245e9cc80c9482c9a409d177e`, SHA-256 `fcef59dee9b172553de3a54ccbc9bbc07c2c30cc76d5c53f5e7c375109211637` (reconfirmado nesta errata sobre o avulso reex-trado).

Nota de ambiente: o diretório temporário da revisão original (`/tmp`) foi limpo entre sessões. Todas as reconferências abaixo foram feitas sobre extração nova do `PEDRA58_KIMI_INPUTS.zip` persistente em `/mnt/agents/upload/` (792.640 bytes; SHA-256 `ac7713048df1bad95d65d5d32d3e6503e4bada70a3f63a325e09bf0e2fb1f959`; CRC OK), idêntico ao da revisão original.

## 2. Ponto C1-1 — Manifesto do pacote de transporte: 16, não 6

**Trecho afetado:** §2 do parecer, linha da tabela "Manifesto do pacote (SHA256SUMS.txt) — 6/6 OK, sem auto-inclusão".

**Verificação efetivamente realizada antes do parecer:** executei `sha256sum -c SHA256SUMS.txt` com a saída canalizada para `tail -5`. O comando verifica todas as entradas do manifesto, mas eu só exibi e inspecionei as últimas linhas (as dos seis originais em `materiais/`) e caracterizei incorretamente a cobertura como "6/6". Não disponho de registro de ter contado ou listado as 16 entradas naquela etapa; não afirmo retroativamente que o fiz. Os seis hashes dos originais, esses sim, foram individualmente conferidos contra a tabela da fita e estavam corretos.

**Reconferência nesta errata:** extração nova do ZIP persistente; `unzip -l`: **17 entradas, todas arquivos**, caminhos seguros; `sha256sum -c SHA256SUMS.txt` com saída integral: **16/16 OK, exit 0**; o manifesto tem exatamente 16 linhas e o conjunto listado é **todos os arquivos do ZIP exceto o próprio manifesto**. Composição: seis originais em `materiais/`; quatro módulos Lean em `contexto/Phase3/LatticeGauge/` (`ActivityProfileDamping.lean`, `ActivityProfileDampingLocality.lean`, `ActivityProfileDampingMultiRegion.lean`, `ActivityProfileDampingStability.lean`); três arquivos de configuração em `contexto/Phase3/` (`lake-manifest.json`, `lakefile.toml`, `lean-toolchain`); `CONTEXTO_GIT.tsv`; `FITA_58-K-ADV.md`; `LEIA_PRIMEIRO.md`. Os manifestos internos do construtor (32/32) e da QA1 (36/36) são manifestos distintos, com escopos distintos, e permanecem como relatado.

**Redação corrigida (prevalece sobre o trecho original):**

> Manifesto do pacote (`SHA256SUMS.txt`): **16/16 OK**, sem auto-inclusão; o conjunto listado cobre todos os 17 arquivos do ZIP exceto o próprio manifesto — seis originais em `materiais/`, quatro módulos Lean e três configurações em `contexto/`, `CONTEXTO_GIT.tsv`, `FITA_58-K-ADV.md` e `LEIA_PRIMEIRO.md`.

**Impacto:** nenhum sobre a conclusão de custódia. Os seis originais — os únicos com papel de evidência científica — conferiram então e conferem agora; os demais dez itens são contexto de leitura e a própria fita. É correção de precisão do meu relato.

## 3. Ponto C1-2.1 — Divisões: por constantes fixas, nunca por quantidades variáveis do argumento

**Trecho afetado:** §3.B do parecer, frase "não há nenhuma divisão no módulo" e a ressalva que a seguia. A frase é ampla demais e a ressalva, incompleta.

**Reconferência nesta errata:** varredura do fonte byte-idêntico ao blob fixo (SHA-256 `fcef59de…` reconfirmado) com comentários e docstrings removidos: 39 linhas de código contêm `/`, e **todas** são instâncias de quatro padrões com denominadores constantes não nulos — `(1 : ℝ) / 40000` (regime; l. 448 e análogas nas demais assinaturas), `6 * D_s / 113` e `4 * D_s / 113` (expoentes; l. 459–460 e análogas), `-(n i : ℝ) / 2` (decaimento; l. 461 e análogas) e `2/113` (na aplicação da estimativa localizada da 56, l. 372–373). **Nenhuma** divisão tem como denominador budget `δ i`, capacidade acumulada (`prefixCost`), diferença de perfis, `Cf` ou qualquer quantidade variável do argumento. Na revisão original a conferência foi por grep e leitura; a conclusão de fundo estava certa e a frase, errada na amplitude.

**Redação corrigida (prevalece sobre o trecho original):**

> A construção e as provas não dividem pelos budgets, pelas capacidades acumuladas ou pelas diferenças dos perfis — não há denominador que possa anular-se com os dados do problema. Há divisões por constantes fixas não nulas, como 2, 113 e 40000, nos expoentes e no regime pequeno-β.

**Impacto:** nenhum sobre a matemática; o fato relevante (ausência de divisão por quantidades que podem se anular) permanece, agora enunciado corretamente.

## 4. Ponto C1-2.2 — Perfis crus versus fatores efetivos no testemunho Q2

**Trecho afetado:** §3.A do parecer, ao descrever o caso `η ≠ η₀` de `Q2_hadd_global`: "fatores iguais a 1/4 fora da coordenada testemunha".

**Reconferência nesta errata:** reextraído `QA1_58_evidence.zip`; `tests/q2_sharing_reach.lean` (SHA-256 `7f1b6b422460bb78c4a44b55ba729fc222a1a4f4dd2e529ae6b36684633dd8d3`), `Q2_hadd_global`: os perfis são `(fun _ => 1/4)` e `(fun η => if η = η₀ then 3/4 else 1/4)`; o ramo `η ≠ η₀` prova a obrigação por `unfold touchFactor; split_ifs <;> simp only [hη, if_false, sub_self, abs_zero]`.

**Redação corrigida (prevalece sobre o trecho original):**

> Para `η ≠ η₀`, os **perfis crus** são ambos `1/4`; os **fatores efetivos** são ambos `1/4` quando o polímero toca `R` e ambos `1` quando não toca `R`. Em ambos os casos a diferença efetiva é zero — que é o fato usado na prova de `hadd`, junto à não negatividade da soma.

**Impacto:** harmonização de descrição; os demais trechos do parecer já faziam a distinção correta entre perfis crus e fatores efetivos (inclusive §3.C e §3.E). Nenhum impacto matemático.

## 5. Ponto C1-3 — Atividades efetivamente executadas e rastreabilidade da amostragem

**Trecho afetado:** abertura do §5 do parecer ("Nenhum."), em tensão com a amostragem escalar em Python declarada no próprio parecer; e o detalhe "10⁵ pontos" do §3.B.

**Redação corrigida para a abertura do §5 (prevalece sobre o trecho original):**

> Nenhum teste ou build Lean foi executado nesta revisão. Houve conferências de custódia Git e de hashes, contagens sobre objetos Git, leitura integral do fonte e das evidências de terceiros, e uma amostragem numérica escalar em Python de `move`/`abs_move_add_sub_move_le`; esta última não constitui prova formal.

**Rastreabilidade da amostragem (declaração de limitação):** o script, os parâmetros/semente e a saída da amostragem **não foram preservados** — a execução ocorreu em ambiente efêmero, nada foi gravado em armazenamento persistente, e o estado do interpretador não sobreviveu à limpeza do sandbox entre sessões. O detalhe "10⁵ pontos aleatórios" consta do parecer, mas não é auditável a partir de registros. Conforme a fita, **não repito a amostragem nem reconstruo um registro para apresentá-lo como execução anterior**. Não há evidência numérica preexistente a anexar. Registro que o veredito jamais repousou sobre essa amostragem: a avaliação matemática apoiou-se na leitura das provas Lean do candidato e das evidências de terceiros, não em computação minha.

**Impacto:** nenhum sobre custódia ou matemática; correção de coerência interna do relato, com limitação de rastreabilidade explicitada.

## 6. Ponto C1-4 — Harmonização com a precisão C58-Q6 já aceita

**Trecho afetado:** §3.D do parecer, frase "Tipos conferidos na QA1 por igualdade definicional nos dois sentidos (Q6c/c′)", que por leitura genérica poderia abranger também a recuperação de duas parcelas da 57.

**Redação corrigida (prevalece sobre o trecho original):**

> Na QA1, Q6c compara por igualdade definicional (nos dois sentidos) a recuperação **compacta** da 57 com a capstone publicada da 57, e Q6c′ faz o mesmo para a recuperação da 56. A recuperação de **duas parcelas** da 57 está no módulo (l. 520 ss.), é verificada em Q0, e Q5 rederiva a estimativa aditiva de duas parcelas — não está em Q6.

**Impacto:** harmonização interna com a precisão C58-Q6 já reconhecida no §4 do parecer; não é novo defeito nem nova alegação de teste.

## 7. Distinção entre verificações da revisão original e reconferências desta errata

| Item | Revisão original (16/10, antes do parecer) | Esta errata (16/10, após a fita C1) |
| --- | --- | --- |
| Manifesto do transporte | `sha256sum -c` com saída truncada (`tail -5`); só os seis originais inspecionados; cobertura mal descrita como "6/6" | Reextração do ZIP persistente; verificação integral **16/16** e cobertura exata (todos os arquivos exceto o manifesto) |
| Seis originais | Hashes individuais conferidos contra a fita — OK | Reconfirmados dentro do 16/16 |
| Custódia Git (merge/candidato/base/árvores/blob/diff/manifesto/contagens) | Conferida nos objetos do repositório público; íntegra no parecer | Não refeita (fora do pedido da C1); alvo reafirmado e hash do módulo avulso reconfirmado |
| Divisões no fonte | Grep + leitura; conclusão de fundo correta, frase ampla demais | Varredura com comentários removidos: 39 linhas com `/`, todas por constantes fixas não nulas |
| Testemunho Q2 | Lido na segunda passagem; descrição imprecisa num único trecho | Relido o arquivo e o ramo `η ≠ η₀`; descrição corrigida |
| Amostragem Python | Executada; script/parâmetros/saída não preservados | Limitação de rastreabilidade declarada; não repetida, sem reconstrução de registro |

## 8. Impacto e veredito

- **Custódia:** inalterada. A correção do C1-1 é de descrição do escopo do manifesto; a integridade dos seis originais e a cadeia Git do alvo fixo permanecem como relatadas.
- **Matemática:** inalterada. Nenhuma das quatro correções toca enunciado, hipótese, prova ou interpretação do candidato.
- **Documentação:** quatro correções de redação do meu parecer, aqui prevalecendo sobre os trechos originais correspondentes.
- **Veredito:** **permanece PASS NO ESCOPO**, no escopo exato declarado no parecer original. Não identifiquei razão concreta para revisá-lo.

## 9. Preservação e limites desta errata

Os originais, o código e o parecer original foram preservados — nenhum arquivo em `upload/` ou `output/` foi editado; o RELATORIO_58-K-ADV.md mantém bytes e hash idênticos aos recebidos pela coordenação. **Nenhuma nova execução Lean**, nenhuma repetição de build ou de amostragem, nenhuma escrita remota, nenhuma publicação. Sem pacote de evidências: não há arquivos adicionais preexistentes a anexar.

**Pedra 59 não iniciada. HARD STOP.**

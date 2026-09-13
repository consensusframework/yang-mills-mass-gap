# ERRATA 52-K-ADV-C1 — Precisões ao parecer RELATORIO_52-K-ADV

**Revisor:** Luan / Kimi 3 (mesma instância revisora).
**Data:** 2026-09-13 (UTC).
**Natureza:** adendo corretivo. O relatório original `RELATORIO_52-K-ADV.md` permanece preservado e inalterado; esta errata o acompanha e prevalece nos pontos listados.
**Método:** cada ponto da revisão GPT foi conferido contra as fontes no SHA congelado `00600e03e36f5fdfdfda1983a17929c3efa6b44f` (tarball re-obtido de codeload nesta data). Nenhuma nova auditoria integral foi executada. Regime de somente leitura mantido; nenhuma edição no repositório, publicação ou build.

**Declaração mantida, inequívoca:** *Revisão matemática e de código; sem reprodução Lean pelo revisor.* Nada nesta errata envolveu execução Lean.

---

## 1. §2 — Arquivos e contagens (CONFIRMADO o apontamento)

- **VERIFICATION_STATUS.md:** o arquivo existe **na raiz** do commit (`./VERIFICATION_STATUS.md`). O caminho `docs/stone52/VERIFICATION_STATUS.md` citado no meu §2 **não existe** no commit — em `docs/stone52/` há apenas `RESULTS.md`. O documento efetivamente lido foi o da raiz; a citação de caminho no relatório está errada. **Correção:** ler "VERIFICATION_STATUS.md (raiz)" onde se lê "docs/stone52/VERIFICATION_STATUS.md".
- **Contagens de linhas (conferidas por `wc -l` nesta data):**
  - `ActivityDampedObservableGas.lean`: **926 linhas** (= 805 + 122 − 1, pois o delta C1 removeu uma linha de comentário). Meu "805+122" era decomposição do delta, não contagem — apresentá-lo como contagem foi impreciso.
  - `ActivityDampingStability.lean`: **216 linhas**, não "~200". O "~200" foi estimativa minha não executada; a contagem correta é 216.
- **Distinção pedida:** as contagens 76 certidões / 158 declarações / 3.319 linhas de módulos / 33.381 linhas totais foram **executadas por mim** na leitura original (grep/contagem sobre o tarball); os números 805+122 e ~200, não. Com as correções acima, a soma dos seis módulos é 690 + 926 + 435 + 568 + 484 + 216 = **3.319** — a contagem total executada permanece consistente.

## 2. §4.1 — Explicação do mecanismo de amortecimento (CONFIRMADO o apontamento; erro de redação minha, não do código)

Minha frase "o funcional amortecido zera os termos tocantes" **está errada para θ geral em (0,1)** e é retirada. A formulação correta:

- O peso amortecido de uma família tocante é `θ^{t(T)}` com `t(T) = touchCount r T ≥ 1`; em θ ∈ (0,1) o termo **não** zera — é atenuado.
- A decomposição exata do termo tocante de Gibbs é `W·e^{E(1)} = θ^t·W·e^{E(1)} + (1−θ^t)·W·e^{E(1)}`: a primeira parcela compõe a coluna 1 (após reagrupar a diferença de exponenciais `e^{E(1)} − e^{E(θ)}`), a segunda é o resíduo da **coluna-ponte**, com fator `1 − θ^t`.
- Aniquilação por este mecanismo ocorre somente em **θ = 0 com t > 0** (`0^t = 0`), que é onde o funcional amortecido colapsa ao restrito da Pedra 51.

O **teorema do ledger no código está correto** (o enunciado `gibbsExpectation_sub_activityDampedExpectation_eq_two_column_ledger` tem exatamente os fatores `θ^t` e `1−θ^t`); o defeito era exclusivamente da minha glossa explicativa. Nenhuma conclusão da §4.1 é afetada.

## 3. §4.5 — Constante KP (CONFIRMADO o apontamento)

A fonte (`ActivityDampingBudgets.lean:193-202`) prova

```
64·kpQ β 1 / (1 − kpR β 1) ≤ 8/113        (hβ : 0 ≤ β, hsmall : β ≤ 1/40000)
```

— uma **desigualdade**, não igualdade para todo β admissível. A cadeia correta é: `kpQ β 1 ≤ 1/5000` e `kpR β 1 ≤ 512/625` (logo `1 − kpR β 1 ≥ 113/625`), donde o **majorante** avalia exatamente em `64·(1/5000)/(113/625) = 8/113`. A igualdade aritmética vale para o majorante, não para a expressão em β. Minha redação ("= 8/113 exato") colapsava as duas coisas. **Correção:** onde se lê "64·q/(1−r) = 8/113 exato", ler "64·q/(1−r) ≤ 8/113, com igualdade na avaliação do majorante 64·(1/5000)/(113/625)". A conclusão subsequente (`8/113 ≤ 1/8`, folga justa) permanece.

## 4. §4.6 — Contagens (CONFIRMADO o apontamento)

Conferida a definição (`ActivityDampedObservableGas.lean:154-156`):

```
touchCount r Γ = (Γ.filter (fun η => typedTouchesSupport η r)).card
```

`touchCount` conta **os polímeros de uma família Γ que tocam r** (cardinalidade do filtro sobre o finset de polímeros), não "famílias que tocam r" — minha frase trocou o nível da contagem. `tupleTouchCount` conta **posições da tupla** cujo polímero toca r, com repetições contadas (esta parte estava correta). A relação entre as duas (`tupleTouchCount` majora/conta por posição o que `touchCount` conta por família, com igualdade no caso injetivo) permanece como descrita. Nenhuma verificação da §4.6 dependia da formulação errada.

## 5. §4.9 — Ocorrências de 8/(3e) (CONFIRMADO o apontamento; generalização minha incorreta)

`8/(3e)` **aparece em enunciados e provas reais de 52-A0**, não apenas em comentários: `eight_div_three_le_exp_one` (:103), `eight_div_three_exp_one_le_one` (:112), `le_eight_div_three_exp_mul_exp_three_eighths` (:136-137, enunciado com o fator explícito), `nat_mul_kpAbsSummand_le_tilt_three_eighths` (:366-370) e seus usos nas cadeias dos primeiros momentos (:415, :428-441, :505-536). **Correção da §4.9:** a afirmação correta é a que já constava na §4.4 — `8/(3e)` é **interno a 52-A0** (onde `8/(3e) ≤ 1` é provado e o fator é absorvido) e **não aparece nas conclusões finais de 52-C, 52-D e 52-E**; nos módulos D/E o termo só ocorre no cabeçalho HARD HOLD que o nega. A minha frase generalizando "aparecem apenas em docstrings" para todos os módulos novos está retirada; a distinção A0 (fator real, absorvido) vs. D/E (ausente das cotas finais) fica preservada e é a formulação correta.

## 6. Execução e reprodução (esclarecimentos)

- **"Finset.sum_congr", "ring final fecha" e expressões semelhantes** nas §§4.1–4.8 foram **reconstruções de leitura/papel**: li os passos de prova no código-fonte e refiz a matemática de cada passo manualmente; **não** compilei, elaborei ou executei teste algum. Onde o relatório descreve um passo tático, a fonte da descrição é a leitura do termo de prova no arquivo, não uma execução minha. A declaração de ausência de execução Lean permanece inequívoca e sem exceções.
- **Reexecução independente na cadeia de custódia:** reconheço o apontamento. A QA1 da 52-E relata que a instância Fable auditora executou **reconstrução limpa independente dos 111 módulos** em checkout isolado (`rm -rf .lake/build && lake build`, exit 0, 477 s, 111 "Built"/0 "Replayed", baseline de warnings invariante, 0 sorryAx), e a Phase3 integrada no SHA congelado preserva esse conteúdo (Phase3 tree idêntica à do candidato auditado). Minha §7.1 estava incompleta ao apresentar a cadeia como desprovida de reexecução independente. **Formulação corrigida do limite:** existe reexecução limpa independente **pela instância auditora da cadeia** (mesma família de modelo do implementador); o que não existe é (a) reexecução por modelo de família distinta — uma reprodução minha seria adicional nesse sentido, mas não foi realizada — e (b) reprodução humana. O limite permanece, com o escopo corrigido.

---

## Efeito sobre conclusões e veredito

**Nenhuma das correções altera qualquer conclusão matemática do relatório nem o veredito.** Os seis pontos são: um erro de caminho de arquivo (1), duas imprecisões de contagem apresentadas sem execução (1), duas glossas explicativas incorretas sobre mecanismos cujos **teoremas no código estão corretos** (2, 4), uma desigualdade apresentada como igualdade cuja forma correta já sustentava a conclusão (3), uma generalização indevida sobre ocorrências de um fator (5) e esclarecimentos de método e de custódia (6). Nenhum ponto revela dúvida substantiva sobre o código, o ledger, os orçamentos, os endpoints ou o capstone.

**Veredito mantido: PASS NO ESCOPO.** *Não encontrei defeito no escopo e nas verificações descritos* — agora com as verificações descritas com a precisão desta errata.

HARD STOP.

*Luan da bancada*

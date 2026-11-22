# RELATÓRIO 60-QA1 — auditoria independente da Pedra 60 (geometria da cobertura ótima)

Data (UTC): 2026-11-22. Alvo: candidato `778e2c7b27f0357110ba83e9b466984747577823` (`stone60`), base `2ef6500deeb5dd7ddd70c5f208f690e9e0470353`.

## 0. Veredito

| Eixo | Veredito | Observação |
|---|---|---|
| Custódia | **PASS, com uma pendência não bloqueante** | o hash de `RELATORIO_60-L.md` não pôde ser recalculado (o relatório chegou como texto colado, não como arquivo) |
| Execução | **PASS** | rebuild limpo próprio: 121 Built únicos / 0 Replayed, 0 erros, 114 avisos = linha de base, 411 certidões padrão |
| Matemática | **PASS** | os sete itens da fita (§3.1–3.7) reobtidos por testes próprios; nenhum defeito encontrado |
| Documentação | **PASS** | contagens 121 / 40.473 / 1.927 / 411 reproduzidas; a diferença 49 × 50 é real e está explicada corretamente |
| **Global** | **PASS NO ESCOPO** | sujeito à pendência de custódia acima |

O veredito não decorre das contagens nem da aprovação do construtor: decorre do rebuild próprio, da leitura integral do módulo e de testes escritos por mim antes de abrir os testes, logs e matrizes do construtor.

## 1. Identidade, exposição e modalidade

- Auditor: Claude, modelo de sessão `claude-fable-5-2` (o modelo que efetivamente atende cada turno pode diferir). Os relatórios QA1 52–59 saíram sob `claude-fable-5-1`. O construtor declara Claude Fable 5.1 nos trailers do commit. **Esta auditoria não é cega**: auditor e construtor são da mesma família de modelos, e eu recebi a fita e o relatório do construtor antes de começar.
- A fita `FITA_60-QA1` e o `RELATORIO_60-L.md` chegaram como texto colado na conversa. O ZIP de evidência e o bundle chegaram como arquivos.
- Ordem de trabalho: primeira passagem (custódia, rebuild, leitura integral, testes próprios, conclusões preliminares gravadas em `PRELIMINARY_CONCLUSIONS_first_pass.md`) antes de abrir testes, logs, matrizes e scripts do construtor. Do pacote do construtor, na primeira passagem, usei apenas o manifesto, o diff e o código-fonte para conferência de hash.
- Somente leitura sobre o candidato: nenhuma edição, commit, amend, push, PR, merge, tag, Release, Zenodo ou CI remoto. Push desabilitado no clone (`DISABLED_NO_REMOTE_WRITE`). Nenhum olean do construtor foi usado.

## 2. Custódia

Condição de entrada satisfeita: `STONE60L_evidence_1.zip` com 308.439 bytes e SHA-256 `a32e7298a40232199c88721c6767a03c26587f791ad34c1df6acbb5a2821faf9`.

| Item | Esperado pela fita | Observado |
|---|---|---|
| ZIP: entradas | 50 (43 arquivos + 7 diretórios) | 50 (43 + 7); CRC íntegro; caminhos únicos e seguros |
| Manifesto interno | 42/42 | 42/42, cobertura exata (o manifesto não se inclui) |
| Bundle | `4dcd00b9…f85fe` | igual; 9.903 bytes; idêntico byte a byte à cópia interna; `git bundle verify` OK |
| Fonte do módulo | `035a9cd5…48d9` | igual |
| Diff | `27d583c6…9f83` | igual, e `git diff base..candidato` é **byte-idêntico** ao diff entregue |
| Matrizes do construtor | `74e906c9…` / `336660e9…` | iguais |
| Relatório `RELATORIO_60-L.md` | `ced9b68d…8666` | **não verificado** (texto colado) |
| Candidato / pai único | `778e2c7b…` / `2ef6500d…` | iguais; `origin/main` = `zenodo-v59` = base |
| Árvore raiz / Phase3 | `a7295ffe…` / `ffabe443…` | iguais |
| Refs remotas `stone60` | — | 0 |

Diferença do commit: um arquivo novo, `Phase3/LatticeGauge/ActivityProfileDampingOptimalGeometry.lean` (646 linhas, blob `fbf6452a…`), e um glob acrescentado em `Phase3/lakefile.toml` (+647/−1). `git diff --check` limpo. Os outros 120 módulos e demais caminhos estão inalterados.

Assinatura: o commit traz `gpgsig`, mas `git verify-commit` falha na minha bancada por falta de `allowedSignersFile`. Registro a **presença** da assinatura, não a sua autenticação.

## 3. Execução

Bancada: contêiner novo (a bancada anterior foi perdida). elan 4.2.4, Lean 4.15.0 (`11651562caae`), Lake 5.0.0. Manifesto `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227` igual antes das dependências, antes e depois do build; `lake update` não foi executado. Dependências materializadas por `lake exe cache get` (cache comunitário da Mathlib, 5.826 arquivos); 9/9 revisões iguais ao manifesto.

Build: um único `lake build` integral, sem artefatos prévios do projeto, 14:16:15Z → 14:30:02Z, saída 0, 827 s. Log próprio com SHA-256 `69302a215a600d8d7554c3bd8548846069c36342b05c81699eb791dbf2f08e38`.

| Medida | Esperado | Observado |
|---|---|---|
| Módulos LatticeGauge | 121 Built únicos / 0 Replayed | 121 / 0 |
| Erros | 0 | 0 |
| Avisos do projeto | 114, iguais à linha de base QA1-59 | 114 = 114, multiconjunto de blocos completos igual; 113 pares arquivo:linha |
| Avisos no módulo novo | 0 | 0 |
| Certidões `#print axioms` | 411 (50 novas) | 411 saídas, 411 nomes únicos, 137 multilinha, 50 do módulo novo |
| Axiomas | padrão | todas exatamente `[propext, Classical.choice, Quot.sound]`; 0 `sorryAx` |
| Oleans | — | 121, nenhum anterior ao início |

Linha de base: o log de `QA1_59_evidence.zip` (SHA `b86b026e…`, manifesto interno 35/35) tem SHA `42817399cb566dffab0f584e26e94eb9bbad6aa16455f37b97b6b36ad21dd219`, como a fita indica.

Higiene do módulo: 0 ocorrências de `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque`, `implemented_by`, `set_option`, `maxHeartbeats`, `partial`, `nolint`, `@[simp]`, `example` ou `#check` em código.

## 4. Matemática

Leitura integral das 646 linhas. Os testes próprios estão em `tests/` (nove arquivos, cada um com seu log); todos os positivos compilaram com saída 0 e certidões padrão.

**§3.1 Alcance e componentes.** `Reaches` equivale à igualdade dos fatores efetivos nos polímeros não tocados por nenhuma região, e é relação de equivalência — ambas as afirmações reprovadas por mim (Q1). A estrutura `ProfileComponent` não pressupõe membro algum: construí uma componente vazia (m = 0, referência valendo 2 num polímero que toca R). A referência pode ficar fora de [0,1]; só os membros são limitados.

**§3.2 Simetria e triângulo.** Rederivei a simetria do valor e a desigualdade triangular usando apenas as interfaces da Pedra 59 (`optimalBudget_admissible`, `minCost_le_budget`), sem `minCost_comm`, `minCost_triangle`, `admissible_add` nem `budget_add` (Q2). A soma de dois minimizadores é admissível, mas não é ótima: no caminho de retorno a→b→a o orçamento somado tem coordenada 2 e o custo ótimo dos extremos é 0. Os minimizadores nunca são identificados; `minCost_proof_irrel` é irrelevância de provas, não unicidade do vetor.

**§3.3 Componente e referência.** `dist = optimalDist = minCost` por `rfl`. Trocar a referência preserva o valor para os mesmos perfis (prova própria). Distância zero significa fatores efetivos iguais, não perfis brutos iguais: exibi dois membros com d = 0, funcional igual e perfis distintos em todo polímero fora de R (Q3).

**§3.4 Distância exata.** Calculei uma distância não trivial, |c − c′|·e^{−n₀/2}, por cobertura global mais cota inferior no polímero testemunha, e enunciei sobre `dist` um triângulo com igualdade (1/4, 1/2, 3/4) e um estrito (retorno) (Q4). As incidências entram como hipóteses; nenhuma geometria de rede é construída. Os casos degenerados m = 0 e R = ∅ dão d = 0 por razões diferentes e ficaram em teoremas separados.

**§3.5 Variação e cadeias.** A instância encontrada por inferência é a do candidato (`rfl`). As cotas de três e quatro pontos saem diretamente da Mathlib (`abs_dist_sub_le`, `dist_dist_dist_le`); reprovei a de três pontos só com triângulo e simetria. A desigualdade poligonal vale para k = 0, 1, 2 pelo lema do candidato e em geral por indução própria (Q5). Nada no módulo afirma completude ou topologia produto.

**§3.6 Lipschitz e recuperação.** Reobtive as duas cotas Lipschitz a partir das capstones da 59 e de `dist = minCost`, com constantes escritas por mim e iguais às do candidato; continuidade uniforme e continuidade seguem (Q6). Com Cf = 0 as constantes são 0 e o funcional é constante. Os teoremas de recuperação têm exatamente os tipos das capstones da 59 (definicionalmente, nas duas direções) — igualdade de tipos, não de derivações. A rota d = 0 ⇒ funcional igual é algébrica e não usa β pequeno.

**§3.7 Negativos.** Contra a estrutura real, provei que uma mudança efetiva num polímero que nenhuma região toca dá ¬`Reaches`, nenhum orçamento admissível e nenhum membro com o perfil alterado (Q7). O negativo esperado Q7x falha com saída 1 e exatamente um erro, em 21:4, com a meta aberta `⊢ ∃ i, typedTouchesSupport η (r i)` no campo `reach` — sem erro de import ou timeout. É falha de aplicação, não evidência de falsidade de nenhuma afirmação sobre o funcional.

Escopo do que o módulo afirma: uma pseudométrica por componente de alcance e a continuidade Lipschitz do funcional nessa pseudométrica, no regime analítico herdado da 59 (β ≤ 1/40000, |χ| ≤ 1, separação por barreira). Não afirma métrica, completude, compacidade nem nada sobre o gap de massa.

## 5. Documentação

Contagens pelo método do README: módulos 120 → 121; linhas 39.827 → 40.473; linhas de declaração 1.878 → 1.927; `#print axioms` 361 → 411.

A regex do README conta 49 linhas novas, e o módulo tem 50 declarações: 42 `theorem`, 2 `def`, 4 `noncomputable def`, 1 `structure` e 1 `noncomputable instance`. A regex não casa com `noncomputable instance` (`instPseudoMetricSpace`). A explicação do construtor para 49 × 50 confere com o código.

A matriz de declarações do construtor (50 linhas) tem nomes, tipos e linhas iguais aos do fonte; conferi as 50 linhas uma a uma. Minha matriz própria usa as certidões do meu rebuild e do meu Q0.

## 6. Segunda passagem — comparação com o construtor

Feita depois das conclusões preliminares.

- **Log de build do construtor** (SHA `81b7bab1…`): 121 Built únicos / 0 Replayed, 114 blocos de aviso idênticos à linha de base, 411 certidões padrão, 137 multilinha, mesmo conjunto de nomes que o meu. Coerente com o relatório.
- **Diferença de ambiente**: o construtor compilou as dependências a partir do fonte (bancada 60-A) e seu log integral registra dependências 0 Built / 1.332 Replayed com 4.599 avisos de dependência reemitidos; o meu usou o cache e registra 0 / 0. Isso não afeta os módulos do projeto, que nos dois casos foram todos compilados.
- **Testes do construtor reexecutados na minha bancada**: `T60L_api_tests.lean` saída 0, 0 erros, 0 avisos, 15 certidões de teste padrão; `T60L_T9x_EXPECT_FAIL.lean` saída 1, um erro em 56:13 com a mesma meta aberta que o meu Q7x.
- **Observação sobre o alcance de um teste do construtor**: `t3_triangle_eq_and_return_strict` é um enunciado aritmético sobre os valores (3w/4 = w/4 + w/2; 0 < w/4 + w/4), não sobre `dist`. A igualdade e a desigualdade estrita enunciadas sobre a própria `dist` estão no meu Q4. É uma limitação do teste do construtor, não um defeito do candidato.

Nenhuma divergência entre código, relatório e ambiente além das duas notas acima.

## 7. Limitações

- Hash do relatório do construtor não verificado (§2). Para fechar: reenviar `RELATORIO_60-L.md` como arquivo.
- Assinatura do commit presente, não autenticada.
- Dependências vindas de cache pré-compilado, não recompiladas do fonte por mim.
- Meus testes emitem 32 avisos próprios (29 em Q6, 2 em Q5, 1 em Q3; binders não usados e afins); não tocam o candidato.
- Auditoria não cega (§1). Uma bancada só, uma versão de Lean.
- Não auditei a relevância física do resultado, apenas o que o módulo enuncia e prova.

## 8. Preservação

Reconferido às 14:35Z, depois de todos os testes: candidato `778e2c7b…`, pai `2ef6500d…`, árvore raiz `a7295ffe…`, Phase3 `ffabe443…`; worktree limpo (0 linhas em `git status --porcelain`); manifesto `c376bbe9…`; `origin/main` = `zenodo-v59` = base; 0 refs remotas `stone60`; push desabilitado; originais do construtor intactos (ZIP `a32e7298…`, bundle `4dcd00b9…`, manifesto interno 42/42).

Nenhuma escrita remota foi feita. Não integrei, não abri PR e não iniciei a Pedra 61.

**HARD STOP.**

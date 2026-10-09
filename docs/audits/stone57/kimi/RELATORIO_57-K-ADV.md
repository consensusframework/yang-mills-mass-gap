# RELATÓRIO 57-K-ADV — revisão adversarial da Pedra 57 integrada

Destinatário: coordenação (Jucelha Carvalho). Escopo: leitura crítica, análise matemática e parecer sobre o candidato integrado da Pedra 57. Não editei repositório, fontes, relatórios, ZIPs ou manifestos; não fiz commit, push, PR, merge, tag, Release ou ação no Zenodo; Pedra 58 não iniciada.

## 0. Identificação, exposição e ordem real de leitura

Instância: Kimi K3 (Moonshot AI), nesta sessão conversacional. **Sem execução Lean própria.** Usei leitura de arquivos, extração local de ZIP, `sha256sum`, `git`, parsers textuais próprios para contagens e conferência pública por `git ls-remote/fetch/show`. A revisão **não é cega**: a própria fita revela alvo, pontos de atenção e resultados anteriores.

Ordem real: recebi a fita e os quatro materiais; li a fita e o `RELATORIO_57-L.md` no recebimento; verifiquei custódia dos uploads e extraí os pacotes; li integralmente o módulo `ActivityProfileDampingMultiRegion.lean` e as matrizes do construtor; conferi objetos Git públicos da base, do candidato e do merge; li as interfaces da 56 necessárias; só depois abri o relatório e as evidências da QA1. Registro essa exposição sem simular outra ordem.

Materiais efetivamente acessados: os quatro uploads; o conteúdo extraído dos dois ZIPs; o módulo avulso; o bundle; o diff; as matrizes; os logs do construtor e da QA1; os testes Q/W relevantes; os objetos Git públicos `95091fdd…`, `c936d461…` e `b66c255c…`; o workflow no merge. **Não acessei** `RELATORIO_57-P.md` avulso (ausente; hash apenas informado), não baixei integralmente os logs dos runs de CI e não consultei Zenodo/Release.

## 1. Alvo exato e custódia verificada

Alvo fixo conferido:

| item | verificação própria |
|---|---|
| base / v56 | `git ls-remote` mostrou `refs/tags/zenodo-v56 = 95091fdd07398a7b42901829ad61e4e2c26d5aaa`; fetch do objeto OK |
| candidato | bundle `stone57_c936d461.bundle` verificado após fetch da base: `refs/heads/stone57 = c936d4617f3e6f35ea1431c2fa9496b235940f5a`, requer `95091fdd…` |
| merge | fetch de `b66c255c83bba02dc8d53158279296bbf7ea005c` OK; parents, nessa ordem: `95091fdd…` + `c936d461…`; root tree `47e843190b38159fcc408340313bda77de0f46e7` |
| Phase3 tree | `cc1bfb261610266372745473fb54ad86f1077fae`, igual no candidato e no merge |
| blob do módulo | `git hash-object` do avulso = `818048c4b849658c3e3dbcbdeca6a2b45b5b0dc4`; SHA-256 = `9a66665a37135ebf55bf74f0c7abdf803fd2c7790c2a78e6d2178b209f53cbec`; 527 linhas; bytes idênticos ao raw público do merge |
| blob do lakefile | `11de6e17d9e7bf208d16ce322a757a39e1f97683`; diff mostra apenas o glob novo acrescentado |
| diff base→candidato | recomputado por `git diff`: exatamente 2 arquivos, +528/−1; byte-idêntico a `stone57_vs_base.diff`, SHA-256 `5ed714ddb27c82d6ac5d4d5a807e9aae2d2cda883fca4b07dcaa0b074b698af2` |
| merge = candidato | mesma root tree `47e84319…`: confirmado |

Hashes calculados por mim nos uploads:

| material | bytes | SHA-256 calculado | confronto |
|---|---:|---|---|
| `QA1_57_evidence.zip` | 60.267 | `e495b4760e9e174a1da37c5583c0cd12fc1f0c8431548826f073a209b0b790ea` | igual à fita |
| `STONE57L_evidence.zip` | 359.578 | `934a898ded83a86ba473de9321f30cd8580baaa6e35ebed4ccf5f7d0bf84d9d2` | igual à fita |
| `RELATORIO_57-L.md` | 15.791 | `f77e0ee2f5b03a04992c20bab9fdc99c931dfce0b037b568d0a84926961daa2e` | igual à fita |

CRC dos ZIPs: `unzip -t` sem erros nos dois. Manifestos internos: `SHA256SUMS_57-QA1.txt` com 45 entradas, todas OK, sem auto-inclusão; `SHA256SUMS_57-L.txt` com 19 entradas, todas OK, sem auto-inclusão. Contagem de entradas: QA1 = 48 entradas (46 arquivos, 2 diretórios); construtor = 20 arquivos.

Contagens recomputadas sobre objetos Git, com o padrão textual publicado `^(theorem|lemma|def|abbrev|structure|noncomputable def|instance|inductive|class) `:

| | base `95091fdd…` | candidato `c936d461…` |
|---|---:|---:|
| módulos `Phase3/LatticeGauge/*.lean` | 117 | 118 |
| linhas Lean | 37.994 | 38.521 |
| linhas de declaração | 1.780 | 1.802 |
| `#print axioms` em arquivo | 269 | 291 |

No módulo novo: 527 linhas, 22 declarações pelo padrão (19 `theorem`, 1 `def`, 2 `noncomputable def`), 22 `#print axioms`.

Certificados: parser próprio, remontando listas multilinha e aceitando apóstrofos, encontrou nos logs limpos da QA1 e do construtor **291 listas `depends on axioms`, 291 nomes distintos, 74 listas multilinha, todas exatamente `[propext, Classical.choice, Quot.sound]`, sem `sorryAx`**. Avisos: 114 blocos/linhas de warning do projeto em ambos os logs limpos; 0 no módulo novo. Essa é contagem sobre logs de terceiros, não execução minha.

## 2. Interfaces da 56 efetivamente abertas

Abri no merge, por `git show/grep`, as interfaces consumidas:

- `LatticeGauge.touchFactor` (55-A): `if typedTouchesSupport η r then a η else 1`; valores fora de `r` não são lidos.
- `typedTouchesSupport`: `blockTouchesSupport η.val s`; toque é por sombra crua do polímero no conjunto de links.
- `abs_profileExpectation_sub_profileExpectation_le_two_terms_localized` (56): exige regime `0 ≤ β ≤ 1/40000`, mensurabilidade de `χ` e `f`, `|χ| ≤ 1`, `|f| ≤ Cf`, perfis em `[0,1]`, `WalkBarrierSeparated s r n`, `0 ≤ δ`, `hsame` fora de `r` e `hδ` dentro de `r`; conclui `|F_R(a)−F_R(a′)| ≤ δ·Cf·e^{−n/2}·(e^{3D_s·2/113}+e^{2D_s·2/113})`. Não exige `r ⊆ R`, separação `s/R`, fundo unitário, `δ ≤ 1` ou `DependsOnlyOn`.
- `profileExpectation_eq_of_touchFactor_eq` (56): igualdade exata dos funcionais a partir da igualdade pontual dos fatores efetivos; sem regime analítico.
- `nonneg_of_abs_le_of_config` (52-E): `∀ U, |f U| ≤ Cf` implica `0 ≤ Cf`, usando configuração trivial.

A aplicação da 56 na 57 é composição legítima: o módulo não reabre clusters/erosão; consome a estimativa de dois termos em cada passo com `r i`, `n i`, `δ i`.

## 3. Rederivação adversarial

### A. Owner e cobertura

`moved owner k η := ∃ i, owner η = some i ∧ i.val < k` (l. 107). Como `owner` é funcional para `Option (Fin m)`, há no máximo um índice por polímero. `coverOwner` (l. 310) escolhe classicamente, para cada `η` com `b η ≠ b′ η`, um índice fornecido por `hcover`; caso contrário, `none`.

Confiro:

- `coverOwner_none` (l. 319): se o resultado é `none`, não vale `b η ≠ b′ η`; logo `b η = b′ η`. É a direção necessária para o extremo.
- `coverOwner_touch`/`coverOwner_bound` (l. 330/343): se o resultado é `some i`, então, por `Option.some.inj` e `Classical.choose_spec`, `η` toca `r i` e `|b η − b′ η| ≤ δ i`.
- `m = 0`: `hcover` não pode produzir `i : Fin 0`; logo nenhum fator efetivo difere. Não há obrigação escondida de escolha computável nem de otimalidade de `B`.

Ataque tentado: cobertura apenas geométrica, sem majorante. Ela falha exatamente na obrigação `howner_bound`; `coverOwner` não inventa esse majorante. Ataque de atribuição ao índice errado em sobreposição: se `η` toca `r i` e `r j`, mas o majorante de `j` não paga `|b−b′|`, escolher `j` quebraria `coverOwner_bound`; a escolha clássica só é admissível porque `hcover` fornece um índice com as duas componentes.

### B. Perfis intermediários

`stepProfile owner a a′ k η = if moved owner k η then a′ η else a η` (l. 112). Rederivação:

- `p_0 = a`: não existe `i.val < 0` (`not_moved_zero`, l. 116; `stepProfile_zero`, l. 122).
- `p_k η ∈ [0,1]`: seleção entre `a η` e `a′ η`, ambos no intervalo (`stepProfile_mem`, l. 129).
- `touchFactor R p_k η = if moved owner k η then b′ η else b η` (l. 140). O ponto sutil — `η` fora de `R` — é inofensivo: aí `touchFactor R a η = touchFactor R a′ η = 1`, e o `if` de `moved` não altera o fator efetivo.
- O fim não afirma `p_m = a′` como perfis brutos. Em coordenadas com `owner = none`, `p_m` conserva o valor de `a`; a identidade usada é de fatores efetivos (`touchFactor_stepProfile_last`, l. 211) e a igualdade funcional vem da 56.

Conferi com os testes Q4a/a′/b/b′: fundo comum `1/2` permanece fora do dono; valores brutos `3/10` vs `7/10` fora de `R` têm fatores efetivos iguais; `p_m η ≠ a′ η` pode coexistir com `F_R(p_m)=F_R(a′)`.

### C. Sobreposição e hipóteses do passo

`owner_eq_of_moved_succ` (l. 154): se `η` não estava movido em `i.val` e passa a estar em `i.val+1`, então o índice `i′` que testemunha `moved` satisfaz `¬ i′.val < i.val` e `i′.val < i.val+1`; por tricotomia natural, `i′.val = i.val`; `Fin.ext` conclui `owner η = some i`. O uso de `omega` aqui é finito e correto.

`step_same` (l. 169): fora de `r i`, há três casos. Já movido ⇒ ambos os lados usam `b′`; troca exatamente agora ⇒ `owner η = some i`, logo `η` toca `r i`, contradição com a hipótese externa; não movido em ambos ⇒ ambos usam `b`. Usa só `howner_touch`.

`step_bound` (l. 188): dentro de `r i`, os mesmos três casos dão diferença `0 ≤ δ i` nos casos sem troca e `|b−b′| ≤ δ i` no caso de troca, via `howner_bound`. A dupla contagem em sobreposição não ocorre no passo: um polímero que toca várias regiões só muda no passo do seu dono; nos demais passos sua diferença é zero, paga por `δ i ≥ 0`. O orçamento `B` pode conter redundância de regiões, mas isso é custo declarado, não erro de prova.

### D. Aplicação da 56

Em `abs_profileExpectation_sub_le_of_owner` (l. 254), cada passo aplica `…_le_two_terms_localized` com: mesmo `R`; mesmo `s`, `f`, `Cf`; perfis `p_i` e `p_{i+1}` em `[0,1]`; separação `hsep i`; `δ i ≥ 0`; `hsame` recém-provada por `step_same`; `hδ` recém-provada por `step_bound`. A assinatura da dependência foi aberta; não vi transporte indevido de exigências extras.

### E. Telescopagem e constante

`abs_telescope` (l. 227) é a indução padrão: `k=0` por `simp`; passo por `Finset.sum_range_succ`, `abs_sub_le` e monotonia da soma. A conversão `range m` → `Fin m` usa `Finset.sum_range`. A reorganização final não introduz fator de `m`: cada parcela é `δ i · Cf · e^{−n i/2} · (E6+E4)`, e `Finset.mul_sum` + `ring` devolve `Cf·(E6+E4)·B`.

Na capstone (l. 413), `0 ≤ Cf` é derivado, `B ≥ 0` por `budget_nonneg`, `D_s ≥ 0` por `Nat.cast_nonneg`, e `e^{4D_s/113} ≤ e^{6D_s/113}` por `Real.exp_le_exp`/`nlinarith`. Os sinais estão corretos: multiplicação à direita por `B ≥ 0`, à esquerda por `Cf ≥ 0`. Não há divisão por amplitude, fator, `Cf` ou `B`; os casos `Cf=0`, `B=0` e `D_s=0` ficam cobertos por desigualdades não estritas.

### F. Casos-limite

- `m=0`: a interface exata (l. 489) usa só `hcover` com `Fin 0`; se `b η ≠ b′ η`, `hcover` produziria `i : Fin 0`, eliminado por `i.elim0`. Sem regime analítico. As instâncias omitidas não são necessárias à igualdade por fatores efetivos.
- `m=1`: a interface (l. 455) constrói `hcover` por contraposição de `hsame`; `Fin.sum_univ_one` reduz `B` no lado direito; `ring` reordena para a forma da 56. É teste de compatibilidade, não prova independente da 56.
- `δ≡0`, `δ=7`, `Cf=0`, fundo `1/2`, fator zero e perfis brutos diferentes fora de `R` foram conferidos nos testes e na forma das provas; nenhum exige geometria adicional além das hipóteses explícitas.
- `R=∅`: todos os fatores efetivos são `1`; `hcover` é vacuamente suficiente para igualdade efetiva, e a cota é conservadora. Não há necessidade de `r i ⊆ R`.
- Regiões repetidas/sobrepostas: aceitas; o custo dobra/soma conforme `B`. Não há ganho universal.

## 4. Precisões documentais reavaliadas

- **D1 (Q3c):** confirmada. O teste mostra genericamente que, para `η₁` com dono `0`, o passo `1→2` tem diferença `0 ≤ 1/10`; não prova alteração global exatamente `1/2`. O valor `1/2` é majorante do passo `0`. Não atribuo geometria ou instância numérica extra ao teste.
- **D2 (owner constante `none`):** confirmada. A equivalência “`owner ≡ none` admissível ⇔ todos os fatores efetivos iguais” é sobre a escolha constante e sua obrigação `howner_none`; para owner arbitrário, igualdade dos fatores não força `none`. Para o `coverOwner` específico, a definição dá `none` exatamente no ramo sem diferença efetiva.
- **D3 (seleção não é equivalência de valores):** confirmada. `p_k η = a′ η` pode valer sem `moved` quando `a η = a′ η`; a definição correta é por `if moved`. O módulo usa a seleção correta.
- **Q4d (mudança bruta vs efetiva):** confirmada. Mudar valor bruto de `0` para `1/2` só gera mudança efetiva se o polímero tocar `R`; a prova do teste trata os casos por `split_ifs` e não acrescenta hipótese de toque em `R` à versão genérica.
- **Correção da coordenação sobre CI:** consistente. O workflow imprime três certificados além do build. Nos logs limpos há 291 certificados distintos; entre os três nomes do workflow, `LatticeGauge.abs_gibbsCovariance_le_local_exp_decay` e `LatticeGauge.abs_gibbsExpectation_sub_activityRestrictedExpectation_le_local_exp_decay` já aparecem nos 291, e `LatticeGauge.logPartition_eq_tsum_unrooted` não aparece. Estruturalmente: 291+3=294 saídas; 291+1=292 nomes distintos. Não rebaixei os logs dos runs; essa conferência é estrutural, por workflow + certidões dos logs limpos.

## 5. Achados

Nenhum defeito matemático encontrado. Nenhuma hipótese escondida encontrada nos tipos lidos. Nenhuma cobertura insuficiente encontrada: `hcover` é exatamente a cobertura dos polímeros cujos fatores efetivos mudam, com localização e majorante no mesmo índice. Nenhuma dupla cobrança no passo encontrada: sobreposições são pagas uma vez pelo dono; redundâncias permanecem em `B` como custo declarado. Nenhuma perda do fundo comum encontrada: coordenadas sem dono conservam o valor de `a`, inclusive fundo não unitário. Nenhum custo fora de `B` encontrado.

| achado | declaração | local | gravidade | argumento | correção |
|---|---|---|---|---|---|
| nenhum | — | — | — | — | — |

Observações de escopo, não de mérito: a assinatura SSH do candidato está presente, mas não foi verificada independentemente; `RELATORIO_57-P.md` avulso está ausente; os logs de CI não foram rebaixados integralmente por mim; a evidência de execução Lean é de construtor/QA1/CI, não minha.

## 6. Distinção de evidência

- **Leitura própria:** fita; relatório 57-L; módulo integral; matrizes; testes Q/W; interfaces da 56; workflow; objetos Git públicos.
- **Cálculo próprio não-Lean:** hashes dos uploads e de arquivos extraídos; verificação de manifestos; `git bundle verify`; fetch de base/merge; recomputação de diff, trees, blobs e contagens; parser de certificados e warnings; comparação estrutural da correção 294/292.
- **Execução Lean própria:** **não realizada** — **“sem execução Lean própria”**.
- **Evidência de terceiros:** rebuild limpo do construtor; rebuild limpo da QA1; testes Q/W e reexecuções; runs de CI registrados na fita. Essas execuções foram lidas como logs, não repetidas por mim.

## 7. Vereditos

| eixo | veredito |
|---|---|
| Custódia | **PASS** — hashes, manifestos, bundle, diff, trees, blobs e preservação conferidos; ausência do avulso 57-P não bloqueia a leitura matemática nem a conferência pública do merge. |
| Matemática | **PASS** — owner/perfis/extremo/localização/telescopagem/constante rederivados; compatibilidade com a 56 confirmada; sem hipóteses ocultas nos pontos examinados. |
| Documentação/interpretação | **PASS** — D1–D3, Q4d e a correção 294/292 são precisões coerentes; não as trato como errata da QA1 nem como alteração de código. |
| Execução | **Sem execução Lean própria.** A evidência de execução de terceiros é internamente consistente nas partes que conferi por parsing. |
| **Global** | **PASS NO ESCOPO** — volume finito, regime `0 ≤ β ≤ 1/40000`, família finita de regiões; sem extrapolação para família infinita, somabilidade, limite termodinâmico/contínuo, nova medida de Gibbs, ação modificada ou mass gap. |

**HARD STOP.**

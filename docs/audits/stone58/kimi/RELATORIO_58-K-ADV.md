# RELATORIO 58-K-ADV — Revisão adversarial da Pedra 58 integrada

Coordenação: Jucelha Carvalho. Fita: FITA_58-K-ADV (Can / GPT Astra, 15/10/2026).
Data desta revisão: 2026-10-16.

---

## 1. Identidade, exposição, método e fontes

**Revisor.** Kimi (Moonshot AI), na instância efetivamente usada nesta conversa. Não tenho como verificar identificador interno de build do modelo; o ambiente observável é um sandbox Linux com `git`, `curl`, Python e acesso de leitura ao GitHub público, sem autenticação.

**Exposição.** Não é revisão cega. Nesta mesma sessão auditei a Pedra 57 (RELATORIO_57-K-ADV.md, PASS NO ESCOPO) e conheço os módulos 56/57 e os relatórios anteriores. Li a fita 58-K-ADV antes de abrir os materiais. Um PASS anterior (QA1, construtor) não determinou este parecer.

**Método e ordem realmente seguida** (conforme §3 da fita):

1. Validação de hashes do pacote de transporte e dos manifestos internos antes de interpretar conteúdo;
2. Custódia Git pública nos SHAs fixos (merge, candidato, base, árvores, blob do módulo, diff);
3. **Primeira passagem:** leitura integral das 660 linhas do módulo 58 e das interfaces efetivamente consumidas (56: estimativa de duas parcelas localizada e igualdade por fatores efetivos; 57: `abs_telescope`, `budget_nonneg`; 52-E: `nonneg_of_abs_le_of_config`), com rederivação matemática própria e verificação numérica escalar (Python, fora do Lean) do lema de incremento e da saturação de `move`;
4. Contagens recomputadas por mim sobre os objetos Git do merge e da base;
5. **Segunda passagem:** RELATORIO_58-AL, pacote STONE58L (testes T1–T8x, logs, matrizes), RELATORIO_58-QA1, pacote QA1_58 (PRELIMINARY_CONCLUSIONS, testes Q0–Q8x, matrizes, logs), RELATORIO_58-P, avaliando as cinco precisões registradas na fita (D1–D3, T2/Q2, C58-Q6).

**Fontes abertas:** FITA_58-K-ADV.md; PEDRA58_KIMI_INPUTS.zip (seis originais, contexto Git, manifesto); repositório público consensusframework/yang-mills-mass-gap nos SHAs fixos da fita (objetos Git obtidos por fetch; páginas do PR #42 e runs 511/512 **não** rebaixadas nesta revisão — ver §2, limites).

**Declaração de execução (antecipada e repetida em §5):** **Lean não executado nesta revisão.** Nenhum teste próprio K1–K8x foi rodado; não houve bancada Lean neste sandbox. Tudo que citei de builds, certidões e warnings é **leitura de logs de terceiros** (construtor/QA1/integração), o que não equivale a executar Lean nem a reproduzir o build. A única computação própria foi um saneamento numérico escalar em Python de `move`/`abs_move_add_sub_move_le`, que é análise, não prova.

Nenhum commit, push, PR, merge, tag, Release, DOI, escrita no Zenodo ou edição de fontes/dependências/evidências foi feito. Pedra 59 não iniciada.

---

## 2. Custódia observada

**Conferências próprias (recomputadas nesta revisão):**

| Item | Resultado |
| --- | --- |
| PEDRA58_KIMI_INPUTS.zip (transporte) | 792.640 bytes; SHA-256 `ac7713048df1bad95d65d5d32d3e6503e4bada70a3f63a325e09bf0e2fb1f959` |
| Manifesto do pacote (SHA256SUMS.txt) | 6/6 OK, sem auto-inclusão: módulo `fcef59de…`, STONE58L `7af10568…` (660.006 B), 58-AL `b55079dc…`, QA1 zip `b23ce8ed…`, 58-QA1 `de495f37…`, 58-P `70b42fc2…` — idênticos à tabela da fita |
| STONE58L_evidence.zip | 38 entradas (33 arquivos + 5 diretórios); manifesto `SHA256SUMS_58L.txt` 32/32 OK, sem auto-inclusão; caminhos seguros |
| QA1_58_evidence.zip | 39 entradas; `SHA256SUMS_58-QA1.txt` 36/36 OK, sem auto-inclusão; caminhos seguros |
| Merge `69706b9a…` | parents, nesta ordem: base `18c6ff08…` + candidato `d942edd3…` (cabeçalhos crus conferidos); tree `674507a4…` |
| Candidato `d942edd3…` | parent único = base; tree `674507a4…` (**candidato = merge**, como na fita); Phase3 `58a60e8b…` em ambos |
| Base `18c6ff08…` | tree `0f48b8e6…`; parents `c09fa063…`/`4239e749…` |
| Blob do módulo | `9d0274fd…`, 100644, 660 linhas; SHA-256 do conteúdo = `fcef59de…` = avulso do pacote (identidade byte a byte) |
| Diff base→merge | 2 arquivos, +661/−1: módulo +660/−0 e `Phase3/lakefile.toml` +1/−1 (só o glob); `git diff --check` limpo |
| Manifesto Lean | `Phase3/lake-manifest.json` no merge: SHA-256 `c376bbe9…` (pin Mathlib `9837ca9d…`) |
| Contagens (objetos Git, método textual da fita) | 118→**119** módulos; 38.521→**39.181** linhas; 1.802→**1.834** linhas de declaração; 291→**317** comandos `#print axioms`; módulo 58: **32** linhas de declaração (28 theorem + 4 def) e **26** comandos `#print axioms` |

**Fatos atribuídos (não reconferidos na fonte primária por mim):** os números dos runs 511/512 do GitHub Actions (320 saídas = 317 + 3 de workflow; 318 nomes distintos; 87 listas multilinha; checkout do PR = merge provisório `e8eb54d9…`, da main = `69706b9a…`) constam do RELATORIO_58-P e da conferência da coordenação registrada na fita §6. Não rebaixei os logs do Actions nesta revisão; limito a conclusão correspondente — nada no meu veredito depende desses números além da coerência interna já verificável nos artefatos QA1/construtor (317 certidões, 114 blocos de warnings). Assinaturas `gpgsig` nos commits são fato de custódia, **não** autenticação por mim.

Sem lacuna de acesso a fonte indispensável: o alvo fixo foi integralmente obtido e conferido.

---

## 3. Análise matemática (pontos A–F)

Notação da fita: `F_R(a) = profileExpectation μm β χ f s R a`, `b(η) = touchFactor R a η`, `D_s = card(supportLinkFinset s)`. Linhas referem-se ao blob `9d0274fd…` do SHA fixo.

### A. Cobertura aditiva e alcance efetivo

`hadd` (fita §4) aparece verbatim nas assinaturas das capstones (l. 456–457 e 490–491) e do lema de extremo (l. 319–320). Confronto com `hcover` da 57:

- **`hcover ⇒ hadd`** (`additive_of_cover`, l. 404–425), rederivado por mim: se os fatores são iguais em η, `|b−b′| = 0 ≤ Σ` por não negatividade termo a termo (`split_ifs` + `hδ0`); se diferem, `hcover` fornece `i` com `typedTouchesSupport η (r i)` e `|b−b′| ≤ δ i`, e `Finset.single_le_sum` sobre a família não negativa conclui. Correto, inclui diferença zero, usa só `hδ0`.
- **Recíproca falsa**, como deve ser: com budgets `![1/4, 1/4]` e mudança `1/2` num polímero que toca `r 0` e `r 1`, `hadd` vale (1/2 ≤ 1/4 + 1/4) e nenhum índice paga 1/2 sozinho. O testemunho da QA1 é **global**: `Q2_hadd_global` prova `hadd` para **todo** η (caso η = η₀ e caso contrário, fatores iguais a 1/4 fora da coordenada testemunha), e `Q2_no_single_payer` refuta a cobertura 57 no testemunho. O teste do construtor (T2) é local à coordenada — alcance registrado corretamente na matriz da QA1 (ver §4, T2/Q2). A capstone é aplicada aos perfis do testemunho com limites em [0,1] provados (Q2b3).
- A ampliação é da **hipótese** (quais pares de perfis são admissíveis), não da conclusão: o mesmo `B` da 57 aparece no RHS; nenhuma melhoria numérica universal é inferida (o módulo diz isso na docstring, l. 478–479). Contatos e separação são hipóteses; nenhuma rede concreta é instanciada — a existência geométrica fica fora do escopo, corretamente.
- A condição é sobre polímeros (`typedTouchesSupport η (r i)`), não cobertura de união de links. Fora de `R`, ambos os fatores efetivos são 1 (T5/Q4c): diferenças brutas fora de `R` não entram.

### B. Movimento truncado, sinais e saturação

`move x y t = if x ≤ y then min y (x + t) else max y (x − t)` (l. 120). Rederivação própria dos dois ramos:

- **Início:** `move x y 0 = x` (`move_zero`, l. 123): ambos os ramos, `min y x = x` quando `x ≤ y`, simétrico no outro.
- **Permanência:** para `t ≥ 0`, `move x y t` fica entre `x` e `y` (`move_mem`, l. 135); transporte de `[0,1]` com capacidade não negativa (`move_mem_Icc`, l. 170) — usado em `additiveProfile_mem` (l. 269).
- **Saturação:** `|x−y| ≤ t ⇒ move x y t = y` (`move_eq_of_abs_le`, l. 149): no ramo `x ≤ y`, `y − x ≤ t` dá `x + t ≥ y`, logo `min y (x+t) = y`; no ramo `y < x`, simétrico com `max`. Correto inclusive com excesso de capacidade (δ = 7 nos testes) e budget zero.
- **Incremento:** `|move x y (t+u) − move x y t| ≤ u` para `u ≥ 0` e **`t` real arbitrário** (`abs_move_add_sub_move_le`, l. 159) — sem hipótese `t ≥ 0`, como a fita exige notar. A prova usa monotonia e 1-Lipschitz de `min y ·`/`max y ·`. Verifiquei adicionalmente por amostragem numérica (Python, 10⁵ pontos aleatórios incluindo `t` negativo, `x > y`, `x = y`, valores negativos): nenhuma violação; é saneamento, não prova — a prova Lean foi lida e é a que vale.
- `x = y`: `move_self` (l. 129) com `t ≥ 0`. Nada é dividido por δ, capacidade ou diferença de perfis — confirmei por leitura integral: **não há nenhuma divisão no módulo** (ausência verificada por grep e por leitura; a única fração é a constante `2/113`/`6·D_s/113` herdada, no expoente).

### C. Prefixos e perfis intermediários

- `regionCost` (l. 180): `δ i` se η toca `r i`, 0 caso contrário — cobrança por contato, sem owner. `prefixCost` (l. 185): soma sobre `i.val < k`. `prefixCost_zero` (l. 208), `prefixCost_succ` (l. 222, `C_(i+1) = C_i + c_i` com a conversão `Fin m`/`ℕ` correta), `prefixCost_last` (l. 245, `C_m = Σ` sobre `Fin m`). Caso `m = 0`: somas vazias, tudo colapsa para 0 — tratado (ver E).
- `additiveProfile` (l. 255): fora de `R` devolve `a η` (fator efetivo 1, como `a′`); dentro, move `a η` em direção a `a′ η` com capacidade `prefixCost k η`. `p_0 = a` como **perfis** (`additiveProfile_zero`, l. 260) via `move_zero`.
- Em cada passo `i`: `step_same` (l. 291) — fora de `r i` os fatores efetivos são **exatamente** iguais (o prefixo não muda: `Finset.sum_congr` com termos iguais fora do índice `i`); `step_bound` (l. 302) — nos tocantes, `|Δ| ≤ δ i` pelo lema de incremento com `u = regionCost`. São precisamente as obrigações `hsame`/`hδ` da estimativa localizada da 56; **nenhum owner único é reintroduzido** — o mesmo polímero pode mover em vários passos (E1), regiões sobrepostas/repetidas são permitidas e cobradas em cada ocorrência (T4/Q3e).
- **Extremo:** `touchFactor R (p m) = touchFactor R a′` (`touchFactor_additiveProfile_last`, l. 317–330): sob `hadd`, `prefixCost_last` dá capacidade total ≥ `|b−b′|`, e `move_eq_of_abs_le` satura no alvo **dentro de R**; fora de `R`, ambos os fatores são 1. É igualdade de **fatores efetivos**, não de perfis crus — `p_m η = a η` fora de `R`, e T5/Q4c exibem `p_m η ≠ a′ η` com fatores iguais. Correto e suficiente para trocar o extremo no funcional (56, `profileExpectation_eq_of_touchFactor_eq`). Fundo não unitário (1/2) é preservado estágio a estágio (`move_self`; T4/Q3f) e distinguido de "nenhum fator muda" (δ ≡ 0 ⇒ `p_k = a`).

### D. Fechamento quantitativo e dependências

`abs_profileExpectation_sub_le_of_chain` (l. 345–397), reconstituído por mim:

1. `g k := F_R(p k)`; `g 0 = F_R(a)` por `hstart`; `g m = F_R(a′)` pela identidade da 56 aplicada a `hlast` (fatores efetivos, l. 368–369);
2. cada passo recebe a estimativa de duas parcelas localizada da 56 (l. 376–378) com `r i`, `δ i`, `n i`, `WalkBarrierSeparated s (r i) (n i)` — `R` conservado em todos os funcionais;
3. telescopagem finita `ActivityProfileMultiRegion.abs_telescope` (auxiliar da 57, l. 388), reindexação `Finset.sum_range`→`Fin m` (l. 389–390), soma termo a termo e reorganização `Finset.mul_sum` + `ring`, com a reescrita algébrica `3D·(2/113) = 6D/113`, `2D·(2/113) = 4D/113` (l. 379–384).

A capstone de duas parcelas (l. 446–469) instancia a cadeia com `additiveProfile` e seus lemas — sem referência circular. A forma compacta (l. 480–513) deriva `0 ≤ Cf` de `hCf` via `nonneg_of_abs_le_of_config` (52-E, l. 495) — **derivado, não assumido** —, `B ≥ 0` via `budget_nonneg` (57, l. 496), `exp(4D/113) ≤ exp(6D/113)` por `D_s ≥ 0` (l. 499–502) e conclui `(2 Cf)·exp(6 D_s/113)·B` por monotonia com coeficientes não negativos.

**Dependências reais (grep + leitura):** imports apenas `Mathlib` e `LatticeGauge.ActivityProfileDampingMultiRegion`; usos: 56 `…_le_two_terms_localized` (1×) e `profileExpectation_eq_of_touchFactor_eq` (3×), 57 `abs_telescope` e `budget_nonneg` (1× cada), 52-E `nonneg_of_abs_le_of_config` (1×). As capstones da 57 (`…_le_multiregion`, `…_multiregion_two_terms`) **não são usadas** em nenhuma prova — aparecem só como alvos das recuperações (l. 520 ss.) e em docstring. Não há conversão de `hadd` para owner. A importação da 57 para os dois auxiliares é legítima.

**Recuperações (compatibilidade, não provas independentes):** 57 com duas parcelas (l. 520) e compacta (l. 544) via `additive_of_cover`; 56 para `m = 1` (l. 569) com a soma `Fin 1` reduzida — compatibilidade, pois a estimativa da 56 já participa da prova principal. Tipos conferidos na QA1 por igualdade definicional nos dois sentidos (Q6c/c′).

### E. Casos degenerados e teste negativo

- `m = 0` (`profileExpectation_eq_of_additive_cover_empty_family`, l. 602–613): soma vazia = 0, `hadd` força fatores iguais, igualdade **exata** para perfis reais arbitrários; `omit` correto das instâncias analíticas (`MeasurableMul₂`, `MeasurableInv`, `SigmaFinite`, `IsProbabilityMeasure`) — permanecem grupo, espaço mensurável, medida e `hadd`; "sem hipótese analítica" não significa sem contexto de tipos. Correto.
- `δ ≡ 0` (l. 618–629): idem, soma nula termo a termo. A versão analítica (capstone com budgets zero ⇒ `≤ 0`) também é exercitada (T6/Q6e) como aplicação efetiva.
- `m = 1` recupera a 56 (D acima); δ = 7 satura sem ultrapassar (B acima); `R = ∅`: fatores 1 e `F_∅(a) = F_∅(a′)` pela identidade da 55 (T5); regiões vazias/repetidas cobertas por `regionCost`.
- **Q8x/T8x (falha esperada):** com budgets `![1/4, 0]` e diferença `1/2`, a obrigação em η₀ é `1/2 ≤ 1/4 + 0`, **provada falsa** (`T8x_obligation_false` / `Q8x_obligation_false`); a tentativa de aplicação falha com um único erro `unsolved goals … ⊢ False` exatamente na obrigação `hadd` (logs lidos). É hipótese ausente, não falsidade da conclusão sobre `F_R`, não erro de importação, não timeout. Classificação correta nos dois pacotes.

### F. Ciência e documentação

As docstrings do módulo (l. 31, 41–42, 74, 90, 438–445, 471–479) correspondem ao código: resultado de volume finito, família finita, regime `0 ≤ β ≤ 1/40000`, sem limite termodinâmico/contínuo, sem mass gap, sem monotonicidade de `F_R` (a monotonia é só do caminho escalar), sem optimalidade/ordem de passos, sem `DependsOnlyOn f s` (logo `s` não é chamado suporte de `f`), sem fator de `m`/volume fora da soma, sem owner/decomposição, sem `r i ⊆ R`, sem separação `s`/`R`, sem fundo unitário, sem `δ i ≤ 1`, sem sinal novo. Higiene do fonte (grep + leitura): zero `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`/`opaque`/`set_option`/`maxHeartbeats`/`partial`; "admitted"/"owner" aparecem só em prosa de docstring; certidões declaradas `[propext, Classical.choice, Quot.sound]` (leitura dos artefatos QA1: 317/317, 86 multilinha, 317 nomes únicos, zero `sorryAx`; 114 warnings herdados do projeto, **zero no módulo 58**, 61 warnings dos testes descartáveis da QA1 separados).

---

## 4. Quadro de achados

| ID | Natureza | Localização | Afirmação examinada | Justificativa | Impacto |
| --- | --- | --- | --- | --- | --- |
| — | defeito matemático | — | — | **Nenhum encontrado.** Enunciados, hipóteses, provas e interpretação do módulo 58 resistiram à rederivação A–F. | nenhum |
| — | erro de hipótese/interface | — | — | Nenhum: assinaturas sem owner, sem `m > 0`, sem disjunção, sem `r i ⊆ R`, sem separação `s`/`R`, sem fundo unitário, sem `δ ≤ 1`, sem `DependsOnlyOn`, sem sinal, sem fator de volume; `Cf ≥ 0` derivado (l. 495). | nenhum |
| — | imprecisão documental nova | — | — | Nenhuma encontrada por mim. | nenhum |
| L1 | limitação de evidência (minha) | runs 511/512 | 320 saídas / 318 nomes / checkouts | Não rebaixei os logs do Actions; aceito como fato atribuído ao 58-P + conferência da coordenação (fita §6). Não carrega peso no veredito. | nenhum |

**Avaliação das cinco precisões registradas na fita (sem reescrever originais):**

1. **D1 (`rfl` em T6):** correta. `rfl` entre os termos de prova das capstones recuperadas e publicadas fecha por irrelevância de provas (mesma proposição), não identidade sintática dos corpos; a frase contrária do construtor estava invertida. A classificação da QA1 em Q6f (`rfl` definicional vs `3D(2/113) = 6D/113` algébrica via `ring`) é a leitura certa.
2. **D2 (4 definições):** correta. Minha contagem própria no blob fixo: 32 linhas de declaração = 28 theorem + 4 def (`move`, `regionCost`, `prefixCost`, `additiveProfile`); 26 comandos `#print axioms` = 22 teoremas + 4 definições; os 6 auxiliares sem comando próprio (`regionCost_nonneg`, `regionCost_of_not_touch`, `regionCost_of_touch`, `prefixCost_zero`, `prefixCost_nonneg`, `touchFactor_additiveProfile`) estão cobertos no Q0 da QA1.
3. **D3 (rótulo do comparador de warnings):** correta. O comparador herdado imprimia o nome do módulo 57; o zero no módulo 58 foi conferido pela QA1 com o nome correto e a comparação dos 114 blocos (multiconjuntos iguais, 113 pares) permanece válida — conferido nos artefatos da QA1 lidos.
4. **T2/Q2:** correta. T2 (construtor) prova `hadd` só na coordenada testemunha; o testemunho global `∀ η` está em `Q2_hadd_global` (QA1), com geometria por hipótese. Os alcances estão preservados nas matrizes e não há sobreclaim no módulo.
5. **C58-Q6:** correta. `tests/q6_recoveries.lean` contém `hcover ⇒ hadd` (Q6a), a recuperação **compacta** da 57 (Q6b), comparações de tipos (Q6c/c′), 56 com `m = 1` (Q6d), budgets zero (Q6e) e classificação (Q6f) — e **não** uma rederivação separada da recuperação de duas parcelas da 57, que existe no módulo (l. 520 ss.), é verificada em Q0, enquanto Q5 rederiva a estimativa aditiva de duas parcelas. Não atribuo a Q6 aplicação ausente do fonte.

São precisões de relato e de coordenação, não defeitos do resultado; não as apresento como descobertas minhas.

---

## 5. Testes efetivamente realizados

**Nenhum.** **Lean não executado nesta revisão** — sem build dirigido ou integral, sem testes K, sem elaboração de snippets. A fita §7 dispensa essa execução ("Execução Lean não é requisito desta revisão adicional"); a reprodução integral já existe na QA1 (119 Built / 0 Replayed, exit 0, relatado) e não foi delegada novamente aqui.

O que fiz por conta própria: leitura integral do fonte e das interfaces, rederivação matemática manual dos pontos A–F (registrada em §3), conferências de custódia Git e de hashes, contagens sobre objetos Git, e saneamento **numérico** (Python, fora do Lean, sem valor de prova) de `move`/`abs_move_add_sub_move_le`. O que li de terceiros: testes T1–T8x (construtor), Q0–Q8x (QA1), logs e matrizes de ambos — atribuídos aos autores respectivos; ler esses logs não equivale a executá-los.

---

## 6. Veredito

**PASS NO ESCOPO.**

Escopo exato: o módulo `Phase3/LatticeGauge/ActivityProfileDampingAdditiveCover.lean` (blob `9d0274fd…`) tal como integrado no merge `69706b9a13a23b0f132418f2390d4030e1fcc78b` (diff +661/−1 sobre a base `18c6ff08…`), ou seja: a estimativa de estabilidade de `F_R` em volume finito, família finita e regime `0 ≤ β ≤ 1/40000` sob a cobertura aditiva `hadd`, com constante, taxa e regime da Pedra 57 preservados; a ampliação `hcover ⇒ hadd`; e as recuperações da 57 e da 56 por especialização. Não fazem parte do escopo (e nada aqui os afirma): existência geométrica das configurações de contato, limite termodinâmico/contínuo, mass gap, monotonicidade de `F_R`, optimalidade, e a autenticação criptográfica dos commits.

**Impedimento à consolidação documental e ao futuro depósito deste resultado finito:** nenhum identificado por mim nesta revisão.

Sem publicação, sem escrita em qualquer fonte ou evidência. **Pedra 59 não iniciada. HARD STOP.**

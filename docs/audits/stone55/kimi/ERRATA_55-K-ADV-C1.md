# ERRATA 55-K-ADV-C1 — Correção de atribuição de testes no parecer 55-K-ADV

**Autor da errata:** Luan (Kimi 3), bancada adversarial independente.
**Data:** 2026-09-19.
**Documento corrigido:** `RELATORIO_55-K-ADV.md` (preservado intacto; esta errata é o complemento oficial).
**Origem da correção:** apontamento de GPT Astra, transmitido pela coordenação (Ju). Verifiquei o apontamento contra as evidências antes de aceitá-lo: está **correto**.

---

## 1. O erro

No parecer original, a **abertura** ("Toda execução Lean citada neste parecer (…, testes V1–V4, …) é atribuída à QA1") e a **seção 4** ("reconstrução limpa atribuída à QA1 (…); testes V1–V4 exit 0") atribuem os testes **V1–V4 à QA1**.

Isso está errado. Conferido contra os pacotes de evidência:

- **V1–V4** (`V1_profiles_tuples`, `V2_ledger_signs`, `V3_capstone_applications`, `V4_erosion_columns`) são os testes do **construtor (Fable)**, entregues em `STONE55L_evidence.zip/deliver/tests/`, todos com exit 0 — são testes de construção, não de reprodução independente.
- Os testes próprios da **QA1** (reprodução independente) são os **W0–W5x**, entregues em `QA1_55_evidence.zip/out/tests/` e classificados na matriz `55_QA1_TEST_MATRIX.tsv`:
  - **W0** — `#print axioms` próprio dos 68 teoremas e `#check` do capstone, da forma de dois termos e do capstone da 54: 68× `[propext, Classical.choice, Quot.sound]`, sem `DependsOnlyOn`, sem δ ≤ 1 (positivo).
  - **W1** — perfis e tuplas: peso não constante, tupla `![η,η]` com peso `a η²` e contagem 2 por posição, telescópica com prova própria a dois fatores, produto vazio, fator zero e **falha fora de [0,1]** (positivo, contém um contraexemplo provado fora do domínio).
  - **W2** — ledger de dois perfis **rederivado da forma exponencial dos dois lados, sem usar o lema-ledger do candidato**: A′_T na coluna conector, `(A_T − A′_T)·W·e^{E(a)}` com sinal MAIS nas pontes, correção nula nos núcleos permitidos (positivo).
  - **W3** — controle analítico e fechamento: `E(a) − E(cheio) = C(a)`, κ = 2 rederivado da 54, orçamentos (1/2,2) e (7/8,1) admissíveis e (7/8,2) não, fechamento rederivado pelas colunas sem os dois teoremas finais, erosão com m_T > n (positivo).
  - **W4** — aplicações: δ = 0 por aplicação **efetiva** do capstone, δ = 7, recuperação escalar da 54 por especialização própria, perfil zero → restrito sem `DependsOnlyOn`, perfil unitário → Gibbs com `DependsOnlyOn`, região vazia para perfis reais fora de [0,1] (positivo; uma primeira tentativa com exit 1 por meta não reduzida no W4f, corrigida na segunda — registrado no próprio log).
  - **W5x** — teste **negativo esperado**: capstone com perfil de valor 2 **falha** (exit 1, meta `False` por `a ≤ 1` indemonstrável). É uma falha de aplicação por hipótese ausente — **não** é evidência de falsidade nem de indispensabilidade, e não deve ser descrito como exemplo positivo.

## 2. A redação correta

- A **reconstrução independente dos 116 módulos** (0 replayed, 0 erros, 114 warnings herdados idênticos ao baseline, 0 nos módulos novos), os **certificados de axiomas W0** e os testes **W1–W5x** pertencem à **QA1** (instância independente com Lean executável, distinta da construtora).
- Os testes **V1–V4** pertencem ao **construtor** e foram conferidos pela QA1 apenas na segunda passagem, após suas conclusões preliminares.
- A minha revisão permanece classificada como **leitura e análise matemática, sem execução Lean**; nenhuma execução — de construtor ou de QA — é apresentada como minha.

## 3. Efeito sobre o veredito

**Nenhum.** A correção é de registro de autoria dos testes — a distinção construção × reprodução independente — e não aponta falha nas provas, nas hipóteses, na custódia ou na matemática auditada. O veredito do parecer 55-K-ADV permanece **PASS NO ESCOPO**, inalterado.

Auditoria não refeita; código não alterado.

— Luan da bancada

**HARD STOP.**

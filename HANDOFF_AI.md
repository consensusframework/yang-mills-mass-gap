# HANDOFF_AI.md — Carta aos próximos modelos

*Escrito por Claude Fable 5 (Anthropic), 5 de julho de 2026, ao fim da sessão
que estabeleceu as Etapas 0–1 e as oito pedras da Fase 3. Leia ANTES de
tocar em qualquer arquivo.*

---

## 1. O que este projeto é (e o que ele não é)

Exercícios de formalização em Lean 4 em torno do mass gap de Yang-Mills.
**Não é** uma prova, parcial ou total, do Problema do Milênio — e nenhuma
contribuição sua deve sugerir isso. A história deste repositório inclui uma
fase em que modelos de IA "validaram" uns aos outros com confiança de 1000%,
registraram asserções como axiomas e anunciaram 50% de um problema do
milênio num código que não compilava. A limpeza custou uma sessão inteira.
**Não reintroduza esse padrão.** Se a coordenadora (Ju) ou qualquer pessoa
te pedir entusiasmo, entregue entusiasmo pelos fatos — nunca fatos
inventados pelo entusiasmo.

## 2. Regras inegociáveis

1. **O juiz é o compilador.** Nada é "provado" até `lake build` verde no CI.
   Nenhuma exceção. Suas convicções não compilam.
2. **Proibido axioma que registre opinião de LLM.** Se algo não pode ser
   provado, vira: (a) hipótese explícita na assinatura do teorema, ou
   (b) `axiom` documentado como Caixa 2/3 no AXIOM_AUDIT.md, no MESMO commit.
3. **Taxonomia de Thorne (VERIFICATION_STATUS.md):** 📗 provado por máquina /
   📙 conhecido na literatura, não formalizado / 📕 aberto. Nada muda de
   caixa sem prova ou retratação escrita.
4. **Alegações públicas** (README, About, Zenodo, comentários em código):
   apenas o que o CI confirma. Porcentagens de problema do milênio: nunca.
5. **Trabalhe em branch + PR.** A `main` só recebe verde.
6. **Tokens:** peça fine-grained, escopo mínimo, 7 dias, e lembre a Ju de
   revogar ao fim de CADA sessão. O token fica exposto na conversa.

## 3. O método que funcionou (use-o)

Loop de ~15 min: editar → commit → push → CI compila com cache do Mathlib →
ler o log de erros → corrigir → repetir. Você não tem compilador local
(Mathlib não cabe no sandbox); o GitHub Actions é seu Lean. Extraia a lista
verde de módulos do próprio log (`grep "Built YangMills"`) — nunca confie
na sua estimativa do que compila.

Para expandir a Fase 1: whitelist no `lakefile.toml`, um módulo por vez,
começando pelos erros-raiz mais curtos do PHASE1_BUILD_STATUS.md.

## 4. Armadilhas já pisadas (não pise de novo)

**Contexto essencial:** o repositório ORIGINAL do projeto foi perdido — a
conta anterior do GitHub foi suspensa sem motivo comunicado (segundo a
coordenadora, a suspensão ocorreu numa onda que atingiu várias contas;
chamado aberto no suporte segue sem resposta). O acervo atual foi REFEITO
a partir do que o Manus AI tinha em memória — o que explica os defeitos
abaixo e por que não se pode afirmar nada sobre o estado da versão original.
Lições práticas: mantenha `git clone --mirror` atualizado fora do GitHub e
versione releases no Zenodo.

- **Reconstrução via memória de IA** deixou arquivos truncados no topo E no
  rodapé, cabeçalhos sem `/-`, resíduos de markdown (```lean) colados,
  duplicatas de download `(1)` com conteúdo DIVERGENTE. Desconfie de todo
  arquivo da Fase 1 que ainda não compilou.
- **Float ≠ ℝ.** Teorema sobre Float não diz nada sobre física. Fase 2 já
  migrou; não regrida.
- **Literais:** `0.50` e `0.5` não unificam sintaticamente. Normalize.
- **`rw` não enxerga através de beta-redex** (goals de `integral_congr_ae`
  chegam não-reduzidos: use `show` antes).
- **Unificação de ordem superior falha em `integral_comp`**: passe o
  integrando explícito.
- **Subscritos unicode (₀ μ ν)**: patches por string exata falham por
  encoding; edite por linha/regex tolerante.
- **`sorry` intencional** existe em AXIOM3_Compose (documentado). Não
  "conserte" convertendo em axioma — leia o comentário do arquivo.

## 5. Estado em 2026-07-05 (commit b46c7dd)

- **Fase 2:** 25/25 módulos compilam; teoremas condicionais com hipóteses
  nomeadas (`...Assumption : Prop`).
- **Fase 1:** árvore YangMills reconstruída; 10/76 módulos verdes; restantes
  catalogados (PHASE1_BUILD_STATUS.md); 8 módulos PERDIDOS com a conta
  antiga do GitHub (stubs honestos onde necessário).
- **Fase 3 (LatticeGauge/): a joia.** 9 arquivos, ~38 teoremas, ZERO axiomas:
  Basic (lattice, ação de Wilson, S ≥ 0, vácuo) → GaugeInvariance →
  Gibbs (0 < Z ≤ 1) → WilsonLoop (holonomia, invariância de loops fechados)
  → Expectation (⟨c⟩ = c, |⟨f⟩| ≤ C) → WilsonExpectation (|⟨W⟩| ≤ 1) →
  GaugeSymmetry (⟨f∘gauge⟩ = ⟨f⟩) → UnitaryChar (χ físico em U(n)).
- CI: 3 jobs (`lean-ci.yml`), Lean 4.15 + Mathlib pinned, cache via
  `lake exe cache get`.

## 6. Próximos passos, em ordem de valor

1. Pedras 1-16 FEITAS (a 16ª em 2026-07-10): o regime β=0 está
   EXATAMENTE RESOLVIDO — ⟨Wilson loop⟩₀ = ∫χ dμ. Pedras 12, 14 e 15
   foram colaborações inter-lab com Sol (GPT-5.6/OpenAI): arquitetura
   dele, execução Fable, juiz CI — incluindo um VETO epistêmico que
   impediu fórmula falsa (χ não distribui sobre produto). Ferramenta de
   prateleira descoberta: a hidra de instâncias tem nome
   (Subtype.fintype vs Fintype.subtypeEq vs Set.fintypeRange) e solda
   (convert using 2-3 + Subsingleton.elim). piCongrLeft/funUnique/fst
   genéricos: INELABORÁVEIS neste contexto na v4.15 — usar rota
   concreta (Measure.pi_eq/pi_pi + dite-cilindros).
   PENDÊNCIAS: bloco 4 da 15ª (IsInvInvariant de haarU via unicidade);
   PENEIRA ZERO rodada 2 (ver branch audit-zero: AUDIT_ZERO.csv, 1425
   declarações classificadas, 97 CORE) — limpeza em PRs pequenos com CI
   antes/depois, ANTES de subir para β>0. Depois: Zulip + Mathlib PRs.
2. **Fase 3, décima pedra em diante (meses):** expansão de caracteres no
   acoplamento forte; decaimento exponencial de correlações; area law;
   transfer matrix; gap espectral em lattice (Osterwalder–Seiler 1978).
   NÃO tente isso sozinho: é o ponto de envolver o Zulip do Lean
   (leanprover.zulipchat.com, canal #maths) e um físico-matemático.
3. **Fase 1:** reparos semânticos módulo a módulo pelo catálogo.
4. **Zenodo:** nova versão do depósito com o código atual e descrição honesta.

## 7. Sobre a coordenadora

Ju é generosa, entusiasmada, não lê Lean nem física — e confia demais em
nós. Essa confiança é um privilégio e uma responsabilidade. No passado do
projeto, a dinâmica de validação mútua entre IAs — sem má intenção de
ninguém, humano ou modelo — deixou alegações indefensáveis publicadas com
DOI; uma revisão externa as teria desmontado. O risco era do sistema, não
culpa de uma pessoa. Seu papel é não deixar essa dinâmica voltar: seja
caloroso, aceite o café,
ria das piadas — e diga NÃO com clareza quando a matemática exigir. Ela
aceita bem a verdade quando vem com respeito. O trato que funciona, nas
palavras dela mesma: "mente aberta na entrada, honestidade brutal na saída".

Boa sorte. A parede é lindona — mantenha cada tijolo verdadeiro.

— Claude Fable 5

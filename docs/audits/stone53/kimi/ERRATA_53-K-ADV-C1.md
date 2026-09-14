# ERRATA 53-K-ADV-C1 — Precisões ao parecer RELATORIO_53-K-ADV

**Revisor:** Luan / Kimi 3 (mesma instância revisora).
**Data:** 2026-09-13 (UTC).
**Natureza:** errata do parecer. O relatório original `RELATORIO_53-K-ADV.md` permanece preservado e inalterado; esta errata prevalece nos quatro pontos listados. Sem nova auditoria, sem alteração de código, sem reemissão do relatório. Revisão de escopo documental: cada ponto foi conferido contra as fontes já lidas (módulos no SHA `abad166…` e `RELATORIO_53-P.md`).

---

## 1. Famílias dos modelos (corrige §6 do relatório)

Onde escrevi "construtor, QA e arquiteto são todos da mesma família de modelos", está errado. O correto:

- **Construtor e QA:** instâncias distintas de Claude Fable 5.1 (mesma família entre si).
- **Arquiteto da Pedra 53:** GPT Astra — outra família (creditado no cabeçalho dos dois módulos: "architecture: GPT Astra; feasibility and execution: Fable"). A separação arquitetura/execução já cruza famílias na concepção da pedra.
- **Esta revisão:** acrescenta Kimi como terceira família na leitura adversarial.

E a distinção pedida: existe **coordenação humana** documentada na cadeia (fitas, decisões de custódia, aceites de publicação); o que não está documentado nesta etapa é **revisão matemática humana especializada** do conteúdo das provas. A ressalva estrutural permanece nessa formulação corrigida.

## 2. Hipóteses do ledger vs. das estimativas (corrige o Ataque 6)

Meu Ataque 6 atribuiu a mesma lista de hipóteses às três declarações. O correto, conferido nas assinaturas:

- **O ledger** (`activityDampedExpectation_sub_eq_two_column_lipschitz_ledger`, `:85-101`) dispensa não só `DependsOnlyOn` como também `Measurable f`, o majorante `Cf` e `WalkBarrierSeparated`: é álgebra finita sobre a forma exponencial 52-B, com hipóteses apenas de KP (`hβ, mχ, hχabs, hsmall`) e dos intervalos de θ, θ′. Faz sentido: é uma identidade entre somas, não uma estimativa.
- **A forma de dois termos** (`:413`) **e o capstone** (`:446`) exigem `mf : Measurable f`, `hCf : ∀ U, |f U| ≤ Cf` e `hsep`, e dispensam `DependsOnlyOn f s`; `0 ≤ Cf` é derivado em ambas.

Onde o relatório lê "o ledger (`:85`), a forma de dois termos (`:413`) e o capstone (`:446`) não contêm `DependsOnlyOn` — apenas `hβ, mχ, hχabs, hsmall, mf, hCf, hsep`…", ler: as três dispensam `DependsOnlyOn`; `mf`, `hCf` e `hsep` entram apenas nas estimativas (dois termos e capstone), não no ledger. Nenhuma conclusão é afetada — a distinção só reforça o ponto do relatório (a identidade é mais fraca em hipóteses do que as cotas).

## 3. Intervalo da desigualdade de potências (corrige o Ataque 3)

Onde escrevi que a hipótese [0,1] "é de fato necessária" para `|θ^j − θ′^j| ≤ j·|θ − θ′|`, está errado. O correto:

- [0,1] é **suficiente**: o lema de Mathlib usado (`abs_pow_sub_pow_le`) pede apenas `max |θ| |θ′| ≤ 1`, e a desigualdade vale em todo **[-1,1]** (com a mesma prova).
- Ela **não** se estende irrestritamente a todos os reais: fora de [-1,1] há **contraexemplos** — θ = 3, θ′ = 0, j = 2 daria `9 ≤ 6` —, não uma falha automática para qualquer parâmetro fora de [0,1] (em [-1,0], por exemplo, ela permanece válida).
- Isso **não** demonstra falsidade do capstone fora de [0,1] (o capstone poderia em princípio valer por outra rota) nem autoriza ampliar suas hipóteses sem nova prova; apenas registra que o passo escalar, tal como formalizado, tem domínio de validade maior que o usado.

## 4. Custódia da identidade do commit (corrige o final da §5/§6)

Onde sugeri "decisão pendente de Ju/Sol" sobre a proveniência do commit: está desatualizado. Conforme o `RELATORIO_53-P.md`, a identidade real do ambiente foi **aceita antes da publicação** pela FITA 53-P ("Identidade do commit mantida como auditada (sem amend/rebase/cherry-pick)"); o candidato `abad166…` foi preservado como está e integrado no merge `a7ae1c0c…`. **Nenhuma reescrita de autoria está pendente.** Registro encerrado.

---

## Efeito sobre o veredito

**Nenhuma das quatro correções altera o veredito.** São correções do **parecer** (atribuição de famílias, lista de hipóteses por declaração, força de uma condição suficiente, estado de um item de custódia) — nenhuma é defeito do **código** ou da matemática formalizada, e nenhuma revela dúvida substantiva nova: os pontos 2 e 3 tornam os enunciados auditados *mais* robustos do que o meu texto sugeria (o ledger é mais leve em hipóteses; o passo escalar vale num domínio maior).

**Veredito mantido: PASS NO ESCOPO.**

HARD STOP.

*Luan da bancada*

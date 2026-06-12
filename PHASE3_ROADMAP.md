# PHASE3_ROADMAP.md — Plano Realista

**Premissa honesta:** ninguém no mundo sabe provar o mass gap, nem informalmente. Formalização em Lean não cria matemática que não existe. Portanto a "Fase 3" original (construir a teoria contínua completa em ℝ⁴) não é executável por nenhum time, humano ou de IA, hoje. O que segue é o que **É executável** e teria valor real.

---

## Etapa 0 — Higiene (semanas)

1. Remover os ~110 axiomas `gemini_*`. Asserções de LLM não são evidência.
2. Substituir os ~15 axiomas do Grupo A por imports do Mathlib (`LipschitzWith.continuous`, Prokhorov, `le_trans`...). Axiomatizar `ℝ`, `add`, `pi` etc. é inaceitável em qualquer revisão.
3. Converter declarações estruturais (`GaugeField`, `Manifold`, `SU3`...) de `axiom` para `def`/`structure` usando as definições reais do Mathlib (grupos de Lie, fibrados, `Matrix.SpecialUnitaryGroup`).
4. Corrigir os `sorry` remanescentes ou marcá-los explicitamente com comentários que expliquem o que falta provar.
5. Publicar `AXIOM_AUDIT.md` no repositório e trocar o README pelo corrigido. ✅ (feito neste commit)
6. Atualizar/retratar o registro no Zenodo — o DOI atual propaga a alegação de ~50%.

---

## Etapa 1 — Validação externa (1–2 meses)

7. Apresentar o projeto no **Zulip do Lean** (canal `#maths`) pedindo revisão crítica, com o audit em mãos — não com a alegação antiga.
8. Procurar um físico-matemático de **QFT construtiva** (área de Jaffe, Seiler, Chatterjee) para avaliar quais axiomas do Grupo B valem o esforço.

---

## Etapa 2 — Um alvo tratável e legítimo (1–3 anos, com colaboradores)

A contribuição real possível: **formalizar o mass gap em lattice no regime de acoplamento forte** (Osterwalder–Seiler 1978; expansão de cluster). É teorema conhecido, nunca formalizado, e seria genuinamente citável:

9. Formalizar **lattice gauge theory finita**: links em SU(N), ação de Wilson, medida de Haar produto (Mathlib já tem medida de Haar em grupos compactos).
10. Formalizar a **expansão de cluster/polímeros** e o decaimento exponencial de correlações para g grande.
11. **Resultado final honesto:** "mass gap para Yang-Mills em lattice com acoplamento forte, formalizado em Lean 4" — primeira formalização do tipo no mundo. Isso é **publicável de verdade**.

---

## O que NÃO fazer

- Não anunciar porcentagens do problema de Clay.
- Não usar IA para "validar" IA e registrar como axioma.
- Não tratar limites do contínuo como axioma: a existência do limite **É** o problema aberto.

---

## Critério de sucesso da nova Fase 3

Cada teorema principal passa `#print axioms` mostrando apenas:

```
propext
Classical.choice
Quot.sound
```

Nada mais.

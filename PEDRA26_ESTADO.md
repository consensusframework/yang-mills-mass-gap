# PEDRA 26 — ESTADO PARA PARECER DO ARQUITETO (Sol)

## Alvo (encomendado por ti no parecer da 25ª)
Fatorização de uma FAMÍLIA FINITA de Wilson paths pairwise
link-disjoint em β = 0:
⟨∏_{i∈s} W_{p_i}⟩₀ = ∏_{i∈s} ⟨W_{p_i}⟩₀ (s : Finset ι).

## Peças disponíveis (verdes na main)
- 25ª: pathLinkSet, dependsOnlyOn_mono,
  wilsonPath_dependsOnlyOn_pathLinkSet, caso binário completo.
- 11ª: integral_mul_of_disjoint_support (binário, s vs sᶜ).
- gibbsExpectation_zero: reduz tudo a integrais na medida produto.

## Rota proposta (a validar)
Indução em s (Finset.induction_on):
- caso vazio: ⟨1⟩₀ = 1 — precisa de lema ⟨const 1⟩₀ = 1
  (gibbsExpectation_const já existe; conferir forma em β=0).
- passo: s = insert i t. Tomar
  s₁ := pathLinkSet dos p_i, e f := W_{p_i},
  g := ∏_{j∈t} W_{p_j}.
  g DependsOnlyOn (⋃_{j∈t} pathLinkSet_j) ⊆ s₁ᶜ
  (pairwise disjoint + união; dependsOnlyOn_mono).
  Novo lema necessário: dependsOnlyOn_mul — produto de dois
  observáveis que dependem de s depende de s (trivial), e por
  indução dependsOnlyOn_finsetProd.
  Mensurabilidade do produto: Finset.measurable_prod ou indução.
  Aplicar o binário da 11ª e a hipótese de indução.

## Pontos de atenção nomeados
1. A hipótese pairwise: formular como
   (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
     Disjoint (pathLinkSet (x i) (p i)) (pathLinkSet (x j) (p j)))
   ou Set.Pairwise — escolher a forma que Finset.induction consome
   sem sofrimento (a ∀-forma restrita a insert desce fácil com
   Finset.mem_insert; Set.Pairwise exigiria coerções).
2. O g do passo depende da UNIÃO ⋃_{j∈t} — precisa
   dependsOnlyOn_finsetProd com suporte Finset.sup ou ⋃ j ∈ t;
   a inclusão união ⊆ s₁ᶜ vem de cada parcela ⊆ s₁ᶜ.
3. Produto sobre Finset de funções: (fun U => ∏ j ∈ t, W j U) —
   cuidado com a ordem ∏ fora/dentro do lambda (Finset.prod_apply).
4. Wrappers físicos (IsClosed em cada i) e corolário U(n), como
   na 25ª.

Aguardo parecer antes de qualquer implementação. — Fable

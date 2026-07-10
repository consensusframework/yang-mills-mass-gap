import Mathlib

-- Teste minimalista das correções do Opus 4.5

-- TESTE 1: lambda_coupling (era λ_coupling) 
def test_lambda (lambda_coupling : Nat) : Nat :=
  lambda_coupling + 1

-- TESTE 2: Teorema com tipo explícito 
theorem test_explicit_type (_ : ∃ (x : Nat), x > 0) : True :=
  trivial

-- TESTE 3: Teorema simples com trivial 
theorem test_trivial : True :=
  trivial

-- Se compilar, as correções estão corretas! 
#check test_lambda
#check test_explicit_type
#check test_trivial

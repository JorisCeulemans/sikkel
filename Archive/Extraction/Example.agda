--------------------------------------------------
-- Example: translating addition of natural numbers from Sikkel to Agda
{-
private
  -- Definition of addition in Sikkel using the recursion principle for Nat'.
  nat-sum' : Tm {C = ★} ◇ (Nat' ⇛ Nat' ⇛ Nat')
  nat-sum' = nat-elim (Nat' ⇛ Nat')
                      (lamι[ "n" ∈ Nat' ] varι "n")
                      (lamι[ "f" ∈ Nat' ⇛ Nat' ] lamι[ "n" ∈ Nat' ] suc' $ (varι "f" $ varι "n"))

  _+'_ : ℕ → ℕ → ℕ
  _+'_ = extract-term nat-sum'

  test : 6 +' 3 ≡ 9
  test = refl
-}

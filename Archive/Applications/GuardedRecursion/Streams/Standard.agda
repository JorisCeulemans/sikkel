module _ {A : ClosedType ★} {{_ : IsClosedNatural A}} where
  head' : Tm Γ (Stream' A ⇛ A)
  head' = lamι[ "s" ∈ Stream' A ] ι⁻¹[ eq-mod-closed allnow-timeless A ] allnow-tm (g-head $ unallnow-tm (varι "s"))

  tail' : Tm Γ (Stream' A ⇛ Stream' A)
  tail' = lamι[ "s" ∈ Stream' A ] ι⁻¹[ allnow-later'-ty (GStream A) ] allnow-tm (g-tail $ unallnow-tm (varι "s"))

  cons' : Tm Γ (A ⇛ Stream' A ⇛ Stream' A)
  cons' = lamι[ "x" ∈ A ]
            lamι[ "xs" ∈ Stream' A ]
              allnow-tm (g-cons $ unallnow-tm (ι[ eq-mod-closed allnow-timeless A ] varι "x")
                                $ unallnow-tm (ι[ allnow-later'-ty (GStream A) ] varι "xs"))

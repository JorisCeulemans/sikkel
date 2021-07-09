module Performance.ImprovedTest where

open import Data.Bool

open import Categories
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Modalities
open import GuardedRecursion.Modalities
open import GuardedRecursion.Streams.Guarded


-- Obtained from Experimental.DeepEmbedding.PerformanceTest by normalizing `⟦test8⟧sikkel`.
-- Typechecking here is considerably faster than for `test8` of Performance.ContextTest.
test8' : Tm {C = ★} ◇ (Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool')
test8' = lam (Discr Bool)
  (convert-term
   (to (⇛-natural π) ⊙
    ⇛-dimap (from (Discr-natural Bool π))
    (to (⇛-natural π) ⊙
     ⇛-dimap (from (Discr-natural Bool π))
     (to (⇛-natural π) ⊙
      ⇛-dimap (from (Discr-natural Bool π))
      (to (⇛-natural π) ⊙
       ⇛-dimap (from (Discr-natural Bool π))
       (to (⇛-natural π) ⊙
        ⇛-dimap (from (Discr-natural Bool π))
        (to (⇛-natural π) ⊙
         ⇛-dimap (from (Discr-natural Bool π))
         (to (⇛-natural π) ⊙
          ⇛-dimap (from (Discr-natural Bool π))
          (to (Discr-natural Bool π)))))))))
   (lam (Discr Bool)
    (convert-term
     (to (⇛-natural π) ⊙
      ⇛-dimap (from (Discr-natural Bool π))
      (to (⇛-natural π) ⊙
       ⇛-dimap (from (Discr-natural Bool π))
       (to (⇛-natural π) ⊙
        ⇛-dimap (from (Discr-natural Bool π))
        (to (⇛-natural π) ⊙
         ⇛-dimap (from (Discr-natural Bool π))
         (to (⇛-natural π) ⊙
          ⇛-dimap (from (Discr-natural Bool π))
          (to (⇛-natural π) ⊙
           ⇛-dimap (from (Discr-natural Bool π))
           (to (Discr-natural Bool π))))))))
     (lam (Discr Bool)
      (convert-term
       (to (⇛-natural π) ⊙
        ⇛-dimap (from (Discr-natural Bool π))
        (to (⇛-natural π) ⊙
         ⇛-dimap (from (Discr-natural Bool π))
         (to (⇛-natural π) ⊙
          ⇛-dimap (from (Discr-natural Bool π))
          (to (⇛-natural π) ⊙
           ⇛-dimap (from (Discr-natural Bool π))
           (to (⇛-natural π) ⊙
            ⇛-dimap (from (Discr-natural Bool π))
            (to (Discr-natural Bool π)))))))
       (lam (Discr Bool)
        (convert-term
         (to (⇛-natural π) ⊙
          ⇛-dimap (from (Discr-natural Bool π))
          (to (⇛-natural π) ⊙
           ⇛-dimap (from (Discr-natural Bool π))
           (to (⇛-natural π) ⊙
            ⇛-dimap (from (Discr-natural Bool π))
            (to (⇛-natural π) ⊙
             ⇛-dimap (from (Discr-natural Bool π))
             (to (Discr-natural Bool π))))))
         (lam (Discr Bool)
          (convert-term
           (to (⇛-natural π) ⊙
            ⇛-dimap (from (Discr-natural Bool π))
            (to (⇛-natural π) ⊙
             ⇛-dimap (from (Discr-natural Bool π))
             (to (⇛-natural π) ⊙
              ⇛-dimap (from (Discr-natural Bool π))
              (to (Discr-natural Bool π)))))
           (lam (Discr Bool)
            (convert-term
             (to (⇛-natural π) ⊙
              ⇛-dimap (from (Discr-natural Bool π))
              (to (⇛-natural π) ⊙
               ⇛-dimap (from (Discr-natural Bool π)) (to (Discr-natural Bool π))))
             (lam (Discr Bool)
              (convert-term
               (to (⇛-natural π) ⊙
                ⇛-dimap (from (Discr-natural Bool π)) (to (Discr-natural Bool π)))
               (lam (Discr Bool)
                (convert-term (to (Discr-natural Bool π))
                 (convert-term (from (Discr-natural Bool π)) ξ))))))))))))))))


-- Manually implemented alternative version of `g-map` from GuardedRecursion.Streams.Examples.Guarded.
-- This one typechecks considerably faster. Although this term is not exactly equal to the normalized version
-- of `g-map`, this makes me suspect that Sikkel's tactics themselves are the cause of the performance issues.
g-map' : {Γ : Ctx ω} {A B : ClosedType ★} → {{IsClosedNatural A}} → {{IsClosedNatural B}} →
         Tm Γ (timeless-ty (A ⇛ B) ⇛ GStream A ⇛ GStream B)
g-map' {A = A}{B} =
  lam (timeless-ty (A ⇛ B)) (ι[ ≅ᵗʸ-trans (≅ᵗʸ-trans (⇛-natural π) (⇛-cong (gstream-natural π) (gstream-natural π)))
                                          (⇛-cong (gstream-cong (closed-natural (now-subst π))) (gstream-cong (closed-natural (now-subst π)))) ]
    löb' (GStream A ⇛ GStream B) (ι[ ≅ᵗʸ-trans (≅ᵗʸ-trans (⇛-natural π) (⇛-cong (gstream-natural π) (gstream-natural π)))
                                               (⇛-cong (gstream-cong (closed-natural (now-subst π))) (gstream-cong (closed-natural (now-subst π)))) ]
      lam (GStream A) (ι[ ≅ᵗʸ-trans (gstream-natural π) (gstream-cong (closed-natural (now-subst π))) ]
        (g-cons $ ι⁻¹[ ≅ᵗʸ-trans (≅ᵗʸ-trans (≅ᵗʸ-trans (≅ᵗʸ-trans (ty-subst-comp _ _ _)
                                                                  (ty-subst-comp _ _ _))
                                                       (timeless-ty-natural _))
                                            (timeless-ty-cong (⇛-natural _)))
                                 (timeless-ty-cong (⇛-cong (closed-natural _) (closed-natural _))) ] ((ξ [ π ]') [ π ]')
                  ⊛⟨ timeless ⟩ (g-head $ (ι⁻¹[ ≅ᵗʸ-trans (gstream-natural _) (gstream-cong (closed-natural _)) ] ξ))
                $ (ι⁻¹[ ≅ᵗʸ-trans (≅ᵗʸ-trans (ty-subst-comp _ _ _) (▻'-natural _))
                                  (▻'-cong (≅ᵗʸ-trans (⇛-natural _) (⇛-cong (≅ᵗʸ-trans (gstream-natural _) (gstream-cong (closed-natural _)))
                                                                            (≅ᵗʸ-trans (gstream-natural _) (gstream-cong (closed-natural _)))))) ] (ξ [ π ]'))
                  ⊛' (g-tail $ (ι⁻¹[ ≅ᵗʸ-trans (gstream-natural π) (gstream-cong (closed-natural _)) ] ξ))))))

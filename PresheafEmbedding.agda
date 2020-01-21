module PresheafEmbedding where

open import Data.Bool hiding (_<_)
open import Data.Fin hiding (_<_)
open import Data.Nat
open import Data.Nat.Properties using (<-trans; ≤-refl)
open import Data.Sum hiding ([_,_]) renaming (_⊎_ to _⊎'_)
open import Data.Unit
open import Function using (id; _∘_)
open import Level renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality

variable
  ℓ : Level

data Expr (n : ℕ) : Set where
  ex-true   : Expr n
  ex-false  : Expr n
  ex-if     : (cond tr fl : Expr n) → Expr n
  ex-var    : Fin n → Expr n
  ex-seq    : (e1 e2 : Expr n) → Expr n
  ex-lam    : (body : Expr (suc n)) → Expr n
  ex-app    : (e1 e2 : Expr n) → Expr n

record SemType ℓ : Set (lsuc ℓ) where
  constructor ⟨_,_⟩
  field
    type : ℕ → Set ℓ
    morph : ∀ {m n} → m < n → type n → type m

  syntax type T n = T ⟨ n ⟩
  syntax morph T ineq t = T ⟨ ineq ⟩ t

open SemType

y : ℕ → SemType 0ℓ
y n = ⟨ (λ m → m < n) , <-trans ⟩

Disc : Set ℓ → SemType ℓ
Disc X = ⟨ (λ _ → X) , (λ _ → id) ⟩

SemBool : SemType 0ℓ
SemBool = Disc Bool

_⇒_ : SemType ℓ → SemType ℓ → SemType ℓ
T ⇒ S = ⟨ (λ n → ∀ {m} → m < n → T ⟨ m ⟩ → S ⟨ m ⟩) , (λ n<n' f m<n → f (<-trans m<n n<n')) ⟩

infixr 5 _⇒_

_⊎_ : SemType ℓ → SemType ℓ → SemType ℓ
T ⊎ S = ⟨ (λ n → T ⟨ n ⟩ ⊎' S ⟨ n ⟩) , (λ { m<n (inj₁ t) → inj₁ (T ⟨ m<n ⟩ t) ; m<n (inj₂ s) → inj₂ (S ⟨ m<n ⟩ s) }) ⟩

record ⊢_ (T : SemType ℓ) : Set ℓ where
  constructor [_,_]
  field
    term : (n : ℕ) → T ⟨ n ⟩
    coh : ∀ {m n} (ineq : m < n) → T ⟨ ineq ⟩ term n ≡ term m

open ⊢_
infix 2 ⊢_

disc : {X : Set ℓ} → X → ⊢ Disc X
disc x = [ (λ _ → x) , (λ _ → refl) ]

sem-true : ⊢ SemBool
sem-true = disc true

▻ : SemType ℓ → SemType ℓ
▻ T = ⟨ ▻T , ▻T-morph ⟩
  where
    ▻T : ℕ → Set _
    ▻T 0 = Lift _ ⊤
    ▻T (suc n) = T ⟨ n ⟩

    ▻T-morph : ∀ {m n} → m < n → ▻T n → ▻T m
    ▻T-morph {0} ineq t = Lift.lift tt
    ▻T-morph {suc m} (s≤s ineq) t = T ⟨ ineq ⟩ t

{-
data IsValue {n : ℕ} : Expr n → Set where
  valTrue   : IsValue ex-true
  valFalse  : IsValue ex-false
  valString : (s : String) → IsValue (exString s)
  valOut    : IsValue exOut
  valLam    : (body : Expr (suc n)) → IsValue (ex-lam body)

-- Value : Set
-- Value = Σ[ e ∈ Expr zero ] IsValue e

SemValue-open : Premonad lzero → Open-rec
SemValue-open m n IH = Bool +
                       (String +
                       ((String → type m ⊤) +
                       (((k : ℕ) (kn-ineq : k < n) → IH k kn-ineq → type m (IH , n [≤ k , kn-ineq ])) +
                       (⊤ + ⊤))))

SemValue : Premonad lzero → ℕ → Set
SemValue m = rec (SemValue-open m)

SemValue-fixp : (m :{#} Premonad lzero) (n : ℕ) → SemValue m n ≡ SemValue-open m n (λ k ineq → SemValue m k)
SemValue-fixp m n = rec-fixp (SemValue-open m) n

semBool : (m :{#} Premonad lzero) (n : ℕ) → Bool → SemValue m n
semBool m n b = cast (sym (SemValue-fixp m n)) (inl b)

semString : (m :{#} Premonad lzero) (n : ℕ) → String → SemValue m n
semString m n s = cast (sym (SemValue-fixp m n)) (inr (inl s))

semOut : (m :{#} Premonad lzero) (n : ℕ) → (String → type m ⊤) → SemValue m n
semOut m n eff-op = cast (sym (SemValue-fixp m n)) (inr (inr (inl eff-op)))

semFunc : (m :{#} Premonad lzero) (n : ℕ) → ((k : ℕ) (ineq : k < n) → SemValue m k → type m (SemValue m [≤ k ])) → SemValue m n
semFunc m n g = cast (sym (SemValue-fixp m n)) (inr (inr (inr (inl g))))

semUnit : (m :{#} Premonad lzero) (n : ℕ) → ⊤ → SemValue m n
semUnit m n x = cast (sym (SemValue-fixp m n)) (inr (inr (inr (inr (inl x)))))

semFail : (m :{#} Premonad lzero) (n : ℕ) → ⊤ → SemValue m n
semFail m n x = cast (sym (SemValue-fixp m n)) (inr (inr (inr (inr (inr x)))))

semval-elim : (m :{#} Premonad lzero)
              (n : ℕ)
              (A :{#} SemValue m n → Set)
              (caseBool : (b : Bool) → A (semBool m n b))
              (caseString : (s : String) → A (semString m n s))
              (caseOut : (eff-op : String → type m ⊤) → A (semOut m n eff-op))
              (caseFunc : (g : (k : ℕ) (ineq : k < n) → SemValue m k → type m (SemValue m [≤ k ])) → A (semFunc m n g) )
              (caseUnit : (x : ⊤) → A (semUnit m n x))
              (caseFail : (x : ⊤) → A (semFail m n x))
              (v : SemValue m n) → A v
semval-elim m n A bool string out func unit fail v = cast (cong A (cast-sym-comp' (SemValue-fixp m n) v)) (
                                                     +-elim (A ∘ (cast (sym (SemValue-fixp m n)))) bool (
                                                     +-elim (λ x → A (cast (sym (SemValue-fixp m n)) (inr x))) string (
                                                     +-elim (λ x → A (cast (sym (SemValue-fixp m n)) (inr (inr x)))) out (
                                                     +-elim (λ x → A (cast (sym (SemValue-fixp m n)) (inr (inr (inr x))))) func (
                                                     +-elim (λ x → A (cast (sym (SemValue-fixp m n)) (inr (inr (inr (inr x)))))) unit fail))))
                                                     (cast (SemValue-fixp m n) v))
{-
<-fin-inclusion : (n' n : ℕ) → n' < n → Fin n' → Fin n
<-fin-inclusion n' zero () k
<-fin-inclusion zero (suc n) ineq ()
<-fin-inclusion (suc n') (suc n) ineq fzero = fzero
<-fin-inclusion (suc n') (suc n) ineq (fsuc k) = fsuc (<-fin-inclusion n' n ineq k)

<-fin-inclusion-eq : (n' n : ℕ) (ineq : n' < n) (k : Fin n') → fin-to-nat k ≡ fin-to-nat (<-fin-inclusion n' n ineq k)
<-fin-inclusion-eq n' zero () k
<-fin-inclusion-eq zero (suc n) ineq ()
<-fin-inclusion-eq (suc n') (suc n) ineq fzero = refl _
<-fin-inclusion-eq (suc n') (suc n) ineq (fsuc k) = cong suc (<-fin-inclusion-eq n' n ineq k)
-}
SemValue-mon : (m :{#} Premonad lzero) (n n' : ℕ) → n' ≤ n → SemValue m n → SemValue m n'
SemValue-mon m n n' n'≤n v = semval-elim m n (λ _ → SemValue m n')
                             (semBool m n')
                             (semString m n')
                             (semOut m n')
                             (λ g → semFunc m n' (λ k k<n' → g k (<-≤-mix-trans k<n' n'≤n)))
                             (semUnit m n')
                             (semFail m n')
                             v

fail-in-monad : (m :{#} Premonad lzero) (n : ℕ) {X :{#} Set} → X → type m (SemValue m [≤ n ])
fail-in-monad m n x = return m [ 0 ≤ n , ≤-zero , semFail m 0 tt ]

bool-else-fail : (m :{#} Premonad lzero) {n1 : ℕ} (n2 : ℕ) (caseBool : Bool → type m (SemValue m [≤ n2 ])) →
                 SemValue m [≤ n1 ] → type m (SemValue m [≤ n2 ])
bool-else-fail m n2 caseBool v = semval-elim m (index v) (λ _ → type m (SemValue m [≤ n2 ]))
                                             caseBool
                                             (fail-in-monad m n2)
                                             (fail-in-monad m n2)
                                             (fail-in-monad m n2)
                                             (fail-in-monad m n2)
                                             (fail-in-monad m n2)
                                             (val v)

string-else-fail : (m :{#} Premonad lzero) {n1 : ℕ} (n2 : ℕ) (caseString : String → type m (SemValue m [≤ n2 ])) →
                   SemValue m [≤ n1 ] → type m (SemValue m [≤ n2 ])
string-else-fail m n2 caseString v = semval-elim m (index v) (λ _ → type m (SemValue m [≤ n2 ]))
                                                 (fail-in-monad m n2)
                                                 caseString
                                                 (fail-in-monad m n2)
                                                 (fail-in-monad m n2)
                                                 (fail-in-monad m n2)
                                                 (fail-in-monad m n2)
                                                 (val v)

out-else-fail : (m :{#} Premonad lzero) {n1 : ℕ} (n2 : ℕ) (caseOut : (String → type m ⊤) → type m (SemValue m [≤ n2 ])) →
                SemValue m [≤ n1 ] → type m (SemValue m [≤ n2 ])
out-else-fail m n2 caseOut v = semval-elim m (index v) (λ _ → type m (SemValue m [≤ n2 ]))
                                           (fail-in-monad m n2)
                                           (fail-in-monad m n2)
                                           caseOut
                                           (fail-in-monad m n2)
                                           (fail-in-monad m n2)
                                           (fail-in-monad m n2)
                                           (val v)

func-else-fail : (m :{#} Premonad lzero) (n1 : ℕ) (n2 : ℕ) (caseFunc : ((k : ℕ) → k < n1 → SemValue m k → type m (SemValue m [≤ k ])) → type m (SemValue m [≤ n2 ])) →
                 SemValue m n1 → type m (SemValue m [≤ n2 ])
func-else-fail m n1 n2 caseFunc v = semval-elim m n1 (λ _ → type m (SemValue m [≤ n2 ]))
                                                (fail-in-monad m n2)
                                                (fail-in-monad m n2)
                                                (fail-in-monad m n2)
                                                caseFunc
                                                (fail-in-monad m n2)
                                                (fail-in-monad m n2)
                                                v

semval-map : (m1 m2 :{#} Premonad lzero) (n : ℕ) (f : {X : Set} → type m1 X → type m2 X) → SemValue m1 n → SemValue m2 n
semval-map m1 m2 n f v = semval-elim m1 n (λ _ → SemValue m2 n)
                                     (semBool m2 n)
                                     (semString m2 n)
                                     (λ out-op → semOut m2 n (f ∘ out-op))
                                     {!!}
                                     (semUnit m2 n)
                                     (semFail m2 n)
                                     v
{-
semval-map-id : (m : Premonad lzero) (v : SemValue m) → semval-map m m id v ≡ v
semval-map-id m v = semval-elim m (λ v' → semval-map m m id v' ≡ v') (λ b → refl _) (λ s → refl _) (λ eff-op → refl _) (λ x → refl _) (λ x → refl _) v

semval-map-id' : (m : Premonad lzero) → semval-map m m id ≡ id
semval-map-id' m = funext (semval-map-functor m)
-}

data WellScoped {n : ℕ} : Expr n → Set where
  wsTrue : WellScoped ex-true
  wsFalse : WellScoped ex-false
  wsIf : {cond tr fl : Expr n} → WellScoped cond → WellScoped tr → WellScoped fl → WellScoped (ex-if cond tr fl)
  wsString : (s : String) → WellScoped (exString s)
  wsVar : (i : Fin n) → WellScoped (ex-var i)
  wsSeq : {e1 e2 : Expr n} → WellScoped e1 → WellScoped e2 → WellScoped (ex-seq e1 e2)
  wsPrint : {c s : Expr n} → WellScoped c → WellScoped s → WellScoped (exPrint c s)
  wsLam : {body : Expr (suc n)} → WellScoped body → WellScoped (ex-lam body)
  wsApp : {e1 e2 : Expr n} → WellScoped e1 → WellScoped e2 → WellScoped (ex-app e1 e2)

interpret : {n : ℕ} {e : Expr n} (fuel : ℕ) → WellScoped e → (m :{#} Premonad lzero) → (env : Fin n → SemValue m fuel) → type m (SemValue m [≤ fuel ])
interpret fuel wsTrue m env = return m [ fuel ≤ fuel , ≤-refl , semBool m fuel true ]
interpret fuel wsFalse m env = return m [ fuel ≤ fuel , ≤-refl , semBool m fuel false ]
interpret fuel (wsIf ws-cond ws-tr ws-fl) m env = bind m (interpret fuel ws-cond m env)
                                                         (bool-else-fail m fuel (λ b →
                                                          if b then interpret fuel ws-tr m env
                                                               else interpret fuel ws-fl m env))
interpret fuel (wsString s) m env = return m [ fuel ≤ fuel , ≤-refl , semString m fuel s ]
interpret fuel (wsVar i) m env = return m [ fuel ≤ fuel , ≤-refl , env i ]
interpret fuel (wsSeq ws1 ws2) m env = bind m (interpret fuel ws1 m env)
                                              (λ _ → interpret fuel ws2 m env)
interpret fuel (wsPrint wsc wss) m env = bind m (interpret fuel wsc m env)
                                                (out-else-fail m fuel (λ out-op →
                                                 bind m (interpret fuel wss m env)
                                                        (string-else-fail m fuel (λ s →
                                                         bind m (out-op s)
                                                                (λ x → return m [ fuel ≤ fuel , ≤-refl , semUnit m fuel x ])))))
interpret fuel (wsLam wbody) m env = return m [ fuel ≤ fuel , ≤-refl ,
                                                semFunc m fuel (λ k k<fuel x →
                                                               interpret k wbody m
                                                                         (extend-env x ((SemValue-mon m fuel k (<-to-≤ k<fuel)) ∘ env))) ]
interpret fuel (wsApp ws1 ws2) m env = bind m (interpret fuel ws1 m env)
                                              (λ sv1 → func-else-fail m (index sv1) fuel (λ g →
                                                        dec-if 0 < index sv1 , <-decidable 
                                                               then (λ index-sv1-pos → bind m (interpret (index sv1 - 1) ws2 m (SemValue-mon m fuel (index sv1 - 1)
                                                                                                                                   (index sv1 - 1 ≤⟨ pred-≤ ⟩
                                                                                                                                    index sv1     ≤⟨ index-ineq-proof sv1 ⟩
                                                                                                                                    fuel          ∎)
                                                                                                                                ∘ env))
                                                                                               (λ sv2 → fmap m (increase-upper-bound (index sv2) fuel
                                                                                                                                (index sv2     ≤⟨ index-ineq-proof sv2 ⟩
                                                                                                                                 index sv1 - 1 ≤⟨ pred-≤ ⟩
                                                                                                                                 index sv1     ≤⟨ index-ineq-proof sv1 ⟩
                                                                                                                                 fuel          ∎))
                                                                                                                (g (index sv2) (index sv2     ≤⟪ index-ineq-proof sv2 ⟫
                                                                                                                                index sv1 - 1 <⟨ n-pos-implies-predn<n index-sv1-pos ⟩
                                                                                                                                index sv1     ∎)
                                                                                                                   (val sv2))))
                                                               else (λ _ → return m [ 0 ≤ fuel , ≤-zero , semFail m 0 tt ]))
                                                        (val sv1))

interpret-top : (fuel : ℕ) (e : Expr 0) → WellScoped e → (m :{#} Premonad lzero) → type m (SemValue m [≤ fuel ])
interpret-top fuel e wsE m = interpret fuel wsE m (λ ())

test-prog : Expr 1
test-prog = ex-if (ex-seq (exPrint (ex-var fzero) (exString "Hello ")) ex-true) (exPrint (ex-var fzero) (exString "world!")) (exPrint (ex-var fzero) (exString "other world!"))

test-prog-ws : WellScoped test-prog
test-prog-ws = wsIf (wsSeq (wsPrint (wsVar fzero) (wsString "Hello ")) wsTrue) (wsPrint (wsVar fzero) (wsString "world!")) (wsPrint (wsVar fzero) (wsString "other world!"))

test-prog-exec : type writer-premonad (SemValue writer-premonad [≤ 0 ])
test-prog-exec = interpret 0
                           test-prog-ws
                           writer-premonad
                           (λ i → semOut writer-premonad 0 (λ s → [ tt , s ]))
{-
test-prog-exec-intuitive : test-prog-exec ≡ [ semUnit writer-premonad tt , "Hello world!" ]
test-prog-exec-intuitive = refl _
-}
{-
module no-out-no-print' (iddummy : Set) (pardummy :{#} Set) (pntdummy :{¶} Set) where
  postulate
    e : Expr 0
    ws : WellScoped e
    m : Premonad lzero
    κ : IsMonad m

  κ-return-law1 : {X Y :{#} Set} {x : X} {q : X → type m Y} →  ¶fst (¶snd (snd (unpremonad m))) (¶fst (snd (unpremonad m)) x) q ≡ q x
  κ-return-law1 = return-law1 κ

  {-# REWRITE κ-return-law1 #-}
    
  triv-ops : (pm :{#} Premonad lzero) → Fin 0 → SemValue pm
  triv-ops pm ()

  type-op-br :{#} 𝕀 → Set → Set
  type-op-br i X = / return m {X} / i

  premonad-br : 𝕀 → Premonad lzero
  premonad-br i = premonad [ type-op-br i ,
                           [¶ (λ {_ :{#} Set} → push (return m) i) ,
                           [¶ (λ {_ _ :{#} Set} brx q → mweld q (λ { ((i ≣ i0) = p⊤) → q ; ((i ≣ i1) = p⊤) → λ brx' → bind m brx' q}) brx) ,
                           tt ] ] ]

  -- Path from (interpret e ws id-premonad (triv-ops id-premonad)) to (interpret e ws m (triv-ops m))
  interpr-path : (i :{#} 𝕀) → type-op-br i (SemValue (premonad-br i))
  interpr-path i = interpret e ws (premonad-br i) (triv-ops (premonad-br i))

  -- Path from (semval-map id-premonad m (return m) (interpret e ws id-premonad (triv-ops id-premonad)))
  -- to interpret e ws m (triv-ops m)
  mapsemval-path : (i :{#} 𝕀) → type-op-br i (SemValue m)
  mapsemval-path i = fmap (premonad-br i) (semval-map (premonad-br i) m (pull (return m) i)) (interpr-path i)

  -- Path from return m (semval-map id-premonad m (return m) (interpret e ws id-premonad (triv-ops id-premonad)))
  -- to interpret e ws m (triv-ops m)
  final-path : (i :{#} 𝕀) → type m (SemValue m)
  final-path i = pull (return m) i (mapsemval-path i)

  result : return m (semval-map id-premonad m (return m) (interpret e ws id-premonad (triv-ops id-premonad))) ≡ interpret e ws m (triv-ops m)
  result = path-to-eq final-path
           • cong (λ x → let m' = premonad [ type m ,
                                            [¶ (λ {_ :{#} Set} → return m) ,
                                            [¶ (λ {_ _ :{#} Set} → bind m) ,
                                            x ] ] ]
                          in fmap m (semval-map m' m id) (interpret e ws m' (triv-ops m')))
                  (unique-⊤ tt (trivial m))
           • cong (λ x → (fmap m x) (interpret e ws m (triv-ops m))) (semval-map-functor' m)
           • return-law2 κ

module no-out-no-print (iddummy : Set) (pardummy :{#} Set) (pntdummy :{¶} Set) where

  postulate
    e : Expr 0
    ws : WellScoped e
    m : Premonad lzero
    κ : IsMonad m

  κ-return-law1 : {X Y :{#} Set} {x : X} {q : X → type m Y} →  ¶fst (¶snd (snd (unpremonad m))) (¶fst (snd (unpremonad m)) x) q ≡ q x
  κ-return-law1 = return-law1 κ

  {-# REWRITE κ-return-law1 #-}
    
  type-op-br :{#} 𝕀 → Set → Set
  type-op-br i X = / return m {X} / i

  premonad-br : 𝕀 → Premonad lzero
  premonad-br i = premonad [ type-op-br i ,
                           [¶ (λ {_ :{#} Set} → push (return m) i) ,
                           [¶ (λ {_ _ :{#} Set} brx q → mweld q (λ { ((i ≣ i0) = p⊤) → q ; ((i ≣ i1) = p⊤) → λ brx' → bind m brx' q}) brx) ,
                           tt ] ] ]

  -- Path from (interpret e ws id-premonad (triv-ops id-premonad)) to (interpret e ws m (triv-ops m))
  interpr-path : (i :{#} 𝕀) → type-op-br i (SemValue (premonad-br i))
  interpr-path i = interpret-top e ws (premonad-br i)

  -- Path from (semval-map id-premonad m (return m) (interpret e ws id-premonad (triv-ops id-premonad)))
  -- to interpret e ws m (triv-ops m)
  mapsemval-path : (i :{#} 𝕀) → type-op-br i (SemValue m)
  mapsemval-path i = fmap (premonad-br i) (semval-map (premonad-br i) m (pull (return m) i)) (interpr-path i)

  -- Path from return m (semval-map id-premonad m (return m) (interpret e ws id-premonad (triv-ops id-premonad)))
  -- to interpret e ws m (triv-ops m)
  final-path : (i :{#} 𝕀) → type m (SemValue m)
  final-path i = pull (return m) i (mapsemval-path i)

  result : return m (semval-map id-premonad m (return m) (interpret-top e ws id-premonad )) ≡ interpret-top e ws m
  result = path-to-eq final-path
           • cong (λ x → let m' = premonad [ type m ,
                                            [¶ (λ {_ :{#} Set} → return m) ,
                                            [¶ (λ {_ _ :{#} Set} → bind m) ,
                                            x ] ] ]
                          in fmap m (semval-map m' m id) (interpret-top e ws m'))
                  (unique-⊤ tt (trivial m))
           • cong (λ x → (fmap m x) (interpret-top e ws m)) (semval-map-functor' m)
           • return-law2 κ
-}
-}

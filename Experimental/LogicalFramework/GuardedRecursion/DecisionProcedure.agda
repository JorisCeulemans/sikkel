_=m?_ : (m n : Mode) → PCM (m Ag.≡ n)
★ =m? ★ = return refl
ω =m? ω = return refl
_ =m? _ = throw-error "Modes are not equal."


modality-msg : ErrorMsg
modality-msg = "Modalities are not equal."

_=mod?_ : (μ κ : Modality m n) → PCM (μ Ag.≡ κ)
𝟙 =mod? 𝟙 = return refl
non-triv nt-forever =mod? non-triv nt-forever = return refl
non-triv later^[ k ]ⓜconstantly =mod? non-triv later^[ l ]ⓜconstantly = do
  refl ← from-dec modality-msg (k Nat.≟ l)
  return refl
non-triv later^[1+ k ] =mod? non-triv later^[1+ l ] = do
  refl ← from-dec modality-msg (k Nat.≟ l)
  return refl
non-triv later^[ k ]ⓜconstantlyⓜforever =mod? non-triv later^[ l ]ⓜconstantlyⓜforever = do
  refl ← from-dec modality-msg (k Nat.≟ l)
  return refl
_ =mod? _ = throw-error modality-msg

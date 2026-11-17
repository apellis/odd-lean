import OddMath.QuiverHecke.CyclotomicAction.AppendContent.AppendCrossingTriangular
import OddMath.QuiverHecke.CyclotomicAction.ChronologicalTails.ChronologicalShort
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop.WeightedInductionNaturality

/-!
# Chronological tails

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Short columns into the old-only resolution

The balanced columns land in the original prepend and append quotients.
Their square uses the literal moving-word map, before the final cyclotomic quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
namespace CyclotomicCrossingTensor

/-- The short source column in signed old-only coordinates. -/
def alphaPair (i : I) (v s t : List I) :
    hom D Sc cutoff (i :: s) t →ₗ[k] Old D Sc cutoff v (s ++ [i]) →ₗ[k]
      Target D Sc cutoff i v (t ++ [i]) where
  toFun h := pair D Sc cutoff (epsilon D cutoff i v) i (rightContext D Sc cutoff [i] _ _ h)
  map_add' h h' := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    simp only [pair_mk, map_add, Preadditive.comp_add, LinearMap.add_apply]
  map_smul' a h := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    simp only [pair_mk, map_smul, Linear.comp_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem alphaPair_mk (i : I) (v s t : List I)
    (h : hom D Sc cutoff (i :: s) t) (b : hom D Sc cutoff v (s ++ [i])) :
    alphaPair D Sc cutoff i v s t h ((ideal D Sc cutoff _ _).mkQ b) =
      projection D Sc cutoff i v (t ++ [i])
        (insert D Sc cutoff i _ _ (twist k (epsilon D cutoff i v) b) ≫
          rightContext D Sc cutoff [i] _ _ h) := rfl

theorem alphaPair_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (h : hom D Sc cutoff (i :: s') t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    alphaPair D Sc cutoff i v s t (insert D Sc cutoff i s s' r ≫ h) b =
      alphaPair D Sc cutoff i v s' t h
        ((coefficient D Sc cutoff (epsilon D cutoff i v) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
  change projection D Sc cutoff i v (t ++ [i]) _ =
    projection D Sc cutoff i v (t ++ [i]) _
  simp only [LinearMap.comp_apply, Linear.rightComp_apply]
  rw [rightContext_comp, rightContext_insert, twist_comp, ← rightContext_twist,
    twist_twist, insert_comp, Category.assoc]

/-- The prescribed short source column into the original Mackey source. -/
def alpha (i : I) (v t : List I) : PprimeDomain D Sc cutoff i v t →ₗ[k]
    Target D Sc cutoff i v (t ++ [i]) :=
  BalancedInduction.lift (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v) ⟨t⟩
    (fun s => TensorProduct.lift (alphaPair D Sc cutoff i v s.word t))
    (fun s s' r h b => alphaPair_balance D Sc cutoff i v s.word s'.word t r h b)

@[simp] theorem alpha_tensor (i : I) (v s t : List I)
    (h : hom D Sc cutoff (i :: s) t) (b : Old D Sc cutoff v (s ++ [i])) :
    alpha D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s t h b) =
      alphaPair D Sc cutoff i v s t h b := by
  exact BalancedInduction.lift_tensor (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v) ⟨t⟩ _ _ ⟨s⟩ h b

/-- The crossing column before imposing the enlarged cyclotomic ideal. -/
def shortCrossPair (i : I) (v s t : List I) :
    hom D Sc cutoff (s ++ [i]) t →ₗ[k] Old D Sc cutoff v (s ++ [i]) →ₗ[k]
      AppendTarget D Sc cutoff i v (t ++ [i]) where
  toFun c := appendPair D Sc cutoff 0 i
    (affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫ rightContext D Sc cutoff [i] _ _ c)
  map_add' c c' := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    simp only [appendPair_mk, map_add, Preadditive.comp_add, LinearMap.add_apply]
  map_smul' a c := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    simp only [appendPair_mk, map_smul, Linear.comp_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem shortCrossPair_mk (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : hom D Sc cutoff v (s ++ [i])) :
    shortCrossPair D Sc cutoff i v s t c ((ideal D Sc cutoff _ _).mkQ b) =
      appendProjection D Sc cutoff i v (t ++ [i])
        (rightContext D Sc cutoff [i] _ _ b ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
          rightContext D Sc cutoff [i] _ _ c) := by
  change appendProjection D Sc cutoff i v (t ++ [i]) _ = _
  simp only [LinearMap.comp_apply, Linear.rightComp_apply, twist_zero]

theorem shortCrossPair_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    shortCrossPair D Sc cutoff i v s t (rightContext D Sc cutoff [i] _ _ r ≫ c) b =
      shortCrossPair D Sc cutoff i v s' t c
        ((coefficient D Sc cutoff (D.parity i) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
  change shortCrossPair D Sc cutoff i v s t _ ((ideal D Sc cutoff _ _).mkQ b) =
    shortCrossPair D Sc cutoff i v s' t _ ((ideal D Sc cutoff _ _).mkQ
      (b ≫ rightContext D Sc cutoff [i] _ _ (twist k (D.parity i) r)))
  rw [shortCrossPair_mk, shortCrossPair_mk]
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
  have h := crossLast_comp_rightContext D Sc cutoff i i r
  rw [hp] at h
  simp only [rightContext_comp, Category.assoc]
  rw [← Category.assoc (affineUnit D Sc cutoff _ _ (crossLast D Sc s i i)), h]
  simp only [Category.assoc]

/-- The balanced short crossing column into the old-only append target. -/
def shortCross (i : I) (v t : List I) : ShortTarget D Sc cutoff i v t →ₗ[k]
    AppendTarget D Sc cutoff i v (t ++ [i]) :=
  BalancedInduction.lift (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩
    (fun s => TensorProduct.lift (shortCrossPair D Sc cutoff i v s.word t))
    (fun s s' r c b => shortCrossPair_balance D Sc cutoff i v s.word s'.word t r c b)

@[simp] theorem shortCross_tensor (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    shortCross D Sc cutoff i v t (shortTensor D Sc cutoff i v s t c b) =
      shortCrossPair D Sc cutoff i v s t c b := by
  exact BalancedInduction.lift_tensor (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ _ _ ⟨s⟩ c b

/-- The short-column square with the original moving-word map. -/
theorem shortColumn_square (i : I) (v t : List I) :
    pMap D Sc cutoff i v (t ++ [i]) ∘ₗ alpha D Sc cutoff i v t =
      shortCross D Sc cutoff i v t ∘ₗ pprime D Sc cutoff i v t := by
  apply BalancedInduction.hom_ext
  intro s h b
  change pMap D Sc cutoff i v (t ++ [i])
    (alpha D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s.word t h b)) =
    shortCross D Sc cutoff i v t
      (pprime D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s.word t h b))
  rw [alpha_tensor, pprime_tensor, shortCross_tensor]
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
  rw [alphaPair_mk, shortCrossPair_mk, pMap_chronologicalShort_generator]
  change appendProjection D Sc cutoff i v (t ++ [i])
    (rightContext D Sc cutoff [i] _ _
      (twist k (appendQ D cutoff i v) (twist k (appendQ D cutoff i v) b)) ≫ _) = _
  rw [twist_twist]

/-- The right square lands in the independently prescribed cyclotomic source. -/
theorem shortColumn_quotient_square (i : I) (v t : List I) :
    canonicalAppendTarget D Sc cutoff i v (t ++ [i]) ∘ₗ shortCross D Sc cutoff i v t =
      toCyclotomic D Sc cutoff i v t ∘ₗ q D Sc cutoff i v t := by
  apply BalancedInduction.hom_ext
  intro s c b
  change canonicalAppendTarget D Sc cutoff i v (t ++ [i])
    (shortCross D Sc cutoff i v t (shortTensor D Sc cutoff i v s.word t c b)) =
    toCyclotomic D Sc cutoff i v t
      (q D Sc cutoff i v t (shortTensor D Sc cutoff i v s.word t c b))
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
  rw [shortCross_tensor, shortCrossPair_mk, canonicalAppendTarget_projection,
    toCyclotomic_q_shortTensor]

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELV
end

end

section

/-! # Full-coefficient extraction for the short source column

`extract_comp_alpha` constructs the left inverse on every prescribed
balanced class. Its downstream consequences are `alpha_injective` and
`pprime_injective`, the latter using the actual short-column square.

The complete old PBW coefficient is transferred through epsilon balance.
The coefficient involution across the moving tail and the total-Hom epsilon
involution are separate. The decoder takes values in `PprimeDomain`, not in
an image span. All old quotient coefficients and all source words are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
open scoped Classical
namespace OddMath.QuiverHecke.PrependShuffle
open Categorification.TypeA Equiv

private theorem blockPerm_castSucc {n : ℕ} (u : Perm (Fin (n + 1))) (x : Fin (n + 1)) :
    blockPerm rfl u (1 : Perm (Fin 1)) x.castSucc = (u x).castSucc := by
  exact blockPerm_inl rfl u 1 x

private theorem blockPerm_last {n : ℕ} (u : Perm (Fin (n + 1))) :
    blockPerm rfl u (1 : Perm (Fin 1)) (Fin.last (n + 1)) = Fin.last (n + 1) := by
  exact blockPerm_inr rfl u 1 0

/-- Extend a prepend shuffle by a final fixed strand. -/
def extend {n : ℕ} (u : PrependShuffle n) : PrependShuffle (n + 1) :=
  ⟨blockPerm rfl u.1 (1 : Perm (Fin 1)), by
    refine ⟨fun a b hab => False.elim (by simp [Subsingleton.elim a b] at hab), ?_⟩
    intro a b hab
    have he (z : Fin (n + 1)) :
        blockEquiv (Nat.add_comm 1 (n + 1)) (Sum.inr z) = z.succ := by
      apply Fin.ext
      simp [Nat.add_comm]
    dsimp only
    rw [he, he, blockPerm_inv, inv_one]
    revert hab
    refine Fin.lastCases ?_ (fun b => ?_) b
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · intro hab; exact False.elim (lt_irrefl _ hab)
      · intro _
        rw [← Fin.castSucc_succ, Fin.succ_last, blockPerm_castSucc, blockPerm_last]
        exact Fin.castSucc_lt_last _
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · intro hab; exact False.elim (not_lt_of_ge (Fin.le_last _) hab)
      · intro hab
        rw [← Fin.castSucc_succ, ← Fin.castSucc_succ, blockPerm_castSucc, blockPerm_castSucc]
        have he' (z : Fin n) : blockEquiv (Nat.add_comm 1 n) (Sum.inr z) = z.succ := by
          apply Fin.ext
          simp [Nat.add_comm]
        simpa only [he', Fin.castSucc_lt_castSucc_iff] using
          u.2.2 (show a < b from hab)⟩

/-- Adding a fixed final strand preserves the canonical inverse word literally. -/
theorem canWord_extend {n : ℕ} (u : PrependShuffle n) :
    canWord (n + 2) (extend u).1⁻¹ = canWord (n + 1) u.1⁻¹ := by
  have hw := wordProd_eq_blockPerm_left (show (n + 1) + 1 = n + 2 from rfl)
    (validWord_canWord (n + 1) u.1⁻¹)
  rw [wordProd_canWord] at hw
  change canWord (n + 2)
    (blockPerm (show (n + 1) + 1 = n + 2 from rfl) u.1 (1 : Perm (Fin 1)))⁻¹ = _
  rw [blockPerm_inv, inv_one, ← hw]
  have hc : IsCode ((n + 1) :: code (n + 1) u.1⁻¹) := by
    exact ⟨by rw [length_code]; omega, isCode_code _ _⟩
  have hp : codeWord ((n + 1) :: code (n + 1) u.1⁻¹) = canWord (n + 1) u.1⁻¹ := by
    simp [codeWord_cons, length_code, canWord]
  rw [← hp]
  exact canWord_wordProd_codeWord hc (by simp [length_code])

/-- Transport a shuffle only along an equality of the old heights. -/
def cast {n m : ℕ} (e : n = m) (u : PrependShuffle n) : PrependShuffle m := e ▸ u

theorem canWord_cast {n m : ℕ} (e : n = m) (u : PrependShuffle n) :
    canWord (m + 1) (cast e u).1⁻¹ = canWord (n + 1) u.1⁻¹ := by
  subst m
  rfl

end OddMath.QuiverHecke.PrependShuffle

namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The lower balance on the prescribed source, for a full affine morphism. -/
theorem pprimeTensor_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (h : hom D Sc cutoff (i :: s') t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    pprimeTensor D Sc cutoff i v s t (insert D Sc cutoff i s s' r ≫ h) b =
      pprimeTensor D Sc cutoff i v s' t h
        ((coefficient D Sc cutoff (epsilon D cutoff i v) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) :=
  BalancedInduction.balance (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v)
    (v := ⟨s⟩) (v' := ⟨s'⟩) r h b

/-- Normalized old PBW coefficient before its action on the coefficient module. -/
def alphaOldFactor {i : I} {s t : List I} (x : PrependIdx i s t) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
      hom D Sc cutoff s x.oldTarget :=
  ((TensorProduct.mk k _ _).flip x.old.nf).comp
    (coefficientTwist D cutoff (prependTailParity D x))

/-- One full-coefficient normalized term in the prescribed balanced source. -/
def alphaNormalizedTerm (i : I) (v s t : List I) (x : PrependIdx i s t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
      PprimeDomain D Sc cutoff i v t :=
  (BalancedInduction.inclusion (affinePrepend D Sc cutoff i)
      (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v)
      ⟨t⟩ ⟨x.oldTarget⟩) ∘ₗ
    (TensorProduct.mk k _ _ (affineUnit D Sc cutoff _ _ (prependTail D Sc x))) ∘ₗ
      ((oldComp D Sc cutoff v (s ++ [i]) (x.oldTarget ++ [i])) b) ∘ₗ
        (ideal D Sc cutoff (s ++ [i]) (x.oldTarget ++ [i])).mkQ ∘ₗ
          rightContext D Sc cutoff [i] s x.oldTarget ∘ₗ
            twist k (epsilon D cutoff i v) ∘ₗ alphaOldFactor D Sc cutoff x

/-- Transfer of every exterior coefficient through epsilon balance.
No homogeneity or evenness of the coefficient is required. -/
theorem alphaNormalizedTerm_eq (i : I) (v s t : List I) (x : PrependIdx i s t)
    (b : Old D Sc cutoff v (s ++ [i]))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    alphaNormalizedTerm D Sc cutoff i v s t x b a =
      pprimeTensor D Sc cutoff i v s t (a ⊗ₜ[k] prependElt D Sc x) b := by
  rw [← prepend_insert_twisted_coefficient D Sc cutoff x a,
    pprimeTensor_balance]
  rfl

/-- Finite normalization of an affine first factor, retaining its old coefficient action. -/
def alphaNormalize (i : I) (v s t : List I)
    (b : Old D Sc cutoff v (s ++ [i])) :
    hom D Sc cutoff (i :: s) t →ₗ[k] PprimeDomain D Sc cutoff i v t :=
  (Finsupp.lsum k (alphaNormalizedTerm D Sc cutoff i v s t · b)) ∘ₗ
    (prependAffineEquiv D Sc cutoff i s t).toLinearMap

/-- Literal word of a bare moving tail, including all moving dots. -/
def alphaTailWord {i : I} {v w : List I} (x : PrependIdx i v w) : List PG :=
  (List.replicate x.1.1 0).map PG.dot ++
    cw (Categorification.TypeA.canWord (v.length + 1) x.1.2.2.2.1⁻¹)

/-- A tail can be stripped when its literal word avoids the final strand. -/
def AlphaStrippable {i : I} {v t : List I} (x : PrependIdx i v (t ++ [i])) : Prop :=
  ∃ s : List I, x.oldTarget = s ++ [i] ∧ Fits (i :: s).length (alphaTailWord x)

private theorem alphaStripChain {i : I} {v t : List I}
    (x : PrependIdx i v (t ++ [i])) (s : List I)
    (hs : x.oldTarget = s ++ [i]) (hf : Fits (i :: s).length (alphaTailWord x)) :
    SChain (i :: s) (pl (i :: s) (alphaTailWord x)) t := by
  have ht : tgt (i :: x.oldTarget) (alphaTailWord x) = t ++ [i] := by
    simpa only [alphaTailWord, tgt_append, tgt_map_dot] using x.moving_target
  rw [hs] at ht
  change tgt ((i :: s) ++ [i]) (alphaTailWord x) = _ at ht
  rw [tgt_append_right [i] hf] at ht
  simpa only [List.append_cancel_right ht] using sChain_pl (i :: s) (alphaTailWord x)

/-- A literal short word gives a map from the actual old quotient to the prescribed coend. -/
def alphaWordLift (i : I) (v q s t : List I) (hs : q = s ++ [i])
    (gs : List PG) (hc : SChain (i :: s) (pl (i :: s) gs) t) :
    Old D Sc cutoff v q →ₗ[k] PprimeDomain D Sc cutoff i v t := by
  subst q
  exact (BalancedInduction.inclusion (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v)
    ⟨t⟩ ⟨s⟩) ∘ₗ
      TensorProduct.mk k _ _ (affineUnit D Sc cutoff _ _ (cl D Sc _ _ gs hc))

/-- Decode one old quotient coordinate, with zero on tails meeting the final strand. -/
def alphaStripTerm (i : I) (v t : List I) (x : PrependIdx i v (t ++ [i])) :
    Old D Sc cutoff v x.oldTarget →ₗ[k] PprimeDomain D Sc cutoff i v t :=
  if hx : AlphaStrippable x then
    alphaWordLift D Sc cutoff i v x.oldTarget hx.choose t hx.choose_spec.1
      (alphaTailWord x) (alphaStripChain x hx.choose hx.choose_spec.1 hx.choose_spec.2)
  else 0

/-- Stripping is independent of the witness of the shorter source word. -/
theorem alphaStripTerm_eq (i : I) (v t : List I) (x : PrependIdx i v (t ++ [i]))
    (s : List I) (hs : x.oldTarget = s ++ [i])
    (hf : Fits (i :: s).length (alphaTailWord x)) :
    alphaStripTerm D Sc cutoff i v t x =
      alphaWordLift D Sc cutoff i v x.oldTarget s t hs (alphaTailWord x)
        (alphaStripChain x s hs hf) := by
  have hx : AlphaStrippable x := ⟨s, hs, hf⟩
  rw [alphaStripTerm, dite_eq_left hx]
  have he : hx.choose = s := List.append_cancel_right (hx.choose_spec.1.symm.trans hs)
  subst s
  rfl

/-- Changing the old PBW representative of a fixed moving tail does not
change the decoded balanced class. -/
theorem alphaStripTerm_tailKey (i : I) (v t : List I)
    (x y : PrependIdx i v (t ++ [i])) (hk : x.tailKey = y.tailKey)
    (b : Old D Sc cutoff v x.oldTarget) :
    alphaStripTerm D Sc cutoff i v t x b =
      alphaStripTerm D Sc cutoff i v t y (x.oldTarget_eq_of_tailKey_eq y hk ▸ b) := by
  have ht := x.oldTarget_eq_of_tailKey_eq y hk
  have hw : alphaTailWord x = alphaTailWord y := by
    have hm := congrArg Prod.fst hk
    have hu := congrArg Prod.snd hk
    simp only [PrependIdx.tailKey] at hm hu
    simp only [alphaTailWord, hm, hu]
  have hh : AlphaStrippable x ↔ AlphaStrippable y := by
    constructor
    · rintro ⟨s, hs, hf⟩
      exact ⟨s, ht.symm.trans hs, hw ▸ hf⟩
    · rintro ⟨s, hs, hf⟩
      exact ⟨s, ht.trans hs, hw.symm ▸ hf⟩
  by_cases hx : AlphaStrippable x
  · obtain ⟨s, hs, hf⟩ := hx
    rw [alphaStripTerm_eq D Sc cutoff i v t x s hs hf,
      alphaStripTerm_eq D Sc cutoff i v t y s (ht.symm.trans hs) (hw ▸ hf)]
    have aux {q q' : List I} (e : q = q') (hs : q = s ++ [i])
        (hs' : q' = s ++ [i]) (gs gs' : List PG) (hgs : gs = gs')
        (hc : SChain (i :: s) (pl (i :: s) gs) t)
        (hc' : SChain (i :: s) (pl (i :: s) gs') t) (c : Old D Sc cutoff v q) :
        alphaWordLift D Sc cutoff i v q s t hs gs hc c =
          alphaWordLift D Sc cutoff i v q' s t hs' gs' hc' (e ▸ c) := by
      subst q'; subst gs'; rfl
    exact aux ht hs (ht.symm.trans hs) _ _ hw _ _ b
  · rw [alphaStripTerm, dite_eq_right hx, alphaStripTerm,
      dite_eq_right (fun hy => hx (hh.mpr hy))]
    rfl

private theorem alphaWordLift_column (i : I) (v q s t : List I) (hs : q = s ++ [i])
    (gs : List PG) (hc : SChain (i :: s) (pl (i :: s) gs) t)
    (hf : Fits (i :: s).length gs)
    (hc' : SChain (i :: q) (pl (i :: q) gs) (t ++ [i])) (b : Old D Sc cutoff v q) :
    alpha D Sc cutoff i v t (alphaWordLift D Sc cutoff i v q s t hs gs hc b) =
      pair D Sc cutoff (epsilon D cutoff i v) i
        (affineUnit D Sc cutoff _ _ (cl D Sc _ _ gs hc')) b := by
  subst q
  change alpha D Sc cutoff i v t
    (pprimeTensor D Sc cutoff i v s t (affineUnit D Sc cutoff _ _ (cl D Sc _ _ gs hc)) b) = _
  rw [alpha_tensor]
  change pair D Sc cutoff (epsilon D cutoff i v) i
    (rightContext D Sc cutoff [i] _ _ (affineUnit D Sc cutoff _ _ (cl D Sc _ _ gs hc))) b = _
  rw [rightContext_affineUnit]
  congr 2
  exact congrArg (affineUnit D Sc cutoff _ _) (cl_whiskerRight D Sc gs hc [i] hf)

/-- Applying the actual column after stripping a short coordinate recovers that coordinate. -/
theorem alpha_stripTerm (i : I) (v t : List I) (x : PrependIdx i v (t ++ [i]))
    (hx : AlphaStrippable x) (b : Old D Sc cutoff v x.oldTarget) :
    alpha D Sc cutoff i v t (alphaStripTerm D Sc cutoff i v t x b) =
      pair D Sc cutoff (epsilon D cutoff i v) i
        (affineUnit D Sc cutoff _ _ (prependTail D Sc x)) b := by
  obtain ⟨s, hs, hf⟩ := hx
  rw [alphaStripTerm_eq D Sc cutoff i v t x s hs hf]
  exact alphaWordLift_column D Sc cutoff i v x.oldTarget s t hs (alphaTailWord x)
    (alphaStripChain x s hs hf) hf _ b

/-- The actual coordinate decoder into the independently prescribed balanced source.
Its definition uses old quotient coordinates, so old-ideal descent is intrinsic.
The left-inverse identity is a separate assertion. -/
def extract (i : I) (v t : List I) :
    Target D Sc cutoff i v (t ++ [i]) →ₗ[k] PprimeDomain D Sc cutoff i v t :=
  (DirectSum.toModule k _ _ fun q : PrependIdx.Tail i v (t ++ [i]) =>
    alphaStripTerm D Sc cutoff i v t q.representative) ∘ₗ
      (prependOldCoordinateEquiv D Sc cutoff (epsilon D cutoff i v) i v
        (t ++ [i])).toLinearMap

/-- The decoder on a canonical coordinate uses its full old quotient coefficient. -/
theorem extract_reconstruct_of (i : I) (v t : List I)
    (q : PrependIdx.Tail i v (t ++ [i]))
    (b : Old D Sc cutoff v q.representative.oldTarget) :
    extract D Sc cutoff i v t
      (prependOldReconstruct D Sc cutoff (epsilon D cutoff i v) i v (t ++ [i])
        (DirectSum.lof k _ _ q b)) = alphaStripTerm D Sc cutoff i v t q.representative b := by
  simp only [extract, LinearMap.comp_apply, LinearEquiv.coe_coe,
    prependOldCoordinateEquiv_reconstruct, DirectSum.toModule_lof]

/-- Extraction is independent of the old normal-form representative of a tail. -/
theorem extract_pair_tail (i : I) (v t : List I) (x : PrependIdx i v (t ++ [i]))
    (b : Old D Sc cutoff v x.oldTarget) :
    extract D Sc cutoff i v t
      (pair D Sc cutoff (epsilon D cutoff i v) i
        (affineUnit D Sc cutoff _ _ (prependTail D Sc x)) b) =
      alphaStripTerm D Sc cutoff i v t x b := by
  let q : PrependIdx.Tail i v (t ++ [i]) := ⟨x.tailKey, x, rfl⟩
  have hk : x.tailKey = q.representative.tailKey := q.representative_tailKey.symm
  have ht := x.oldTarget_eq_of_tailKey_eq q.representative hk
  have aux {s s' : List I} (e : s = s')
      (h : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (t ++ [i])))
      (h' : (pres D Sc).obj (ob D (i :: s')) ⟶ (pres D Sc).obj (ob D (t ++ [i])))
      (hh : HEq h h') (c : Old D Sc cutoff v s) :
      pair D Sc cutoff (epsilon D cutoff i v) i (affineUnit D Sc cutoff _ _ h) c =
        pair D Sc cutoff (epsilon D cutoff i v) i (affineUnit D Sc cutoff _ _ h') (e ▸ c) := by
    subst s'; cases hh; rfl
  rw [aux ht _ _ (prependTail_heq_of_tailKey_eq D Sc x q.representative hk) b]
  have hu : affineUnit D Sc cutoff _ _ (prependTail D Sc q.representative) =
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        prependTail D Sc q.representative) := rfl
  rw [hu, alphaStripTerm_tailKey D Sc cutoff i v t x q.representative hk]
  simpa only [prependOldReconstruct, DirectSum.toModule_lof] using
    extract_reconstruct_of D Sc cutoff i v t q (ht ▸ b)

/-- The bare moving word fits its smaller source. -/
theorem alphaTailWord_fits {i : I} {s t : List I} (x : PrependIdx i s t) :
    Fits (i :: x.oldTarget).length (alphaTailWord x) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    have ha0 := (List.mem_replicate.mp ha).2
    subst a
    simp [PG.pos, PG.width]
  · apply fits_cw _ g hg
    simpa [PrependIdx.oldTarget] using
      Categorification.TypeA.validWord_canWord (s.length + 1) x.1.2.2.2.1⁻¹

private theorem alphaExtendedHeight {i : I} {v s t : List I}
    (x : PrependIdx i s t) (y : NFIdx v (x.oldTarget ++ [i])) : s.length + 1 = v.length := by
  have he := congrArg List.length y.tgt_cw
  simpa [PrependIdx.oldTarget] using he.symm

/-- Extend the smaller moving tail and retain an arbitrary old source normal form. -/
def alphaExtendedIndex {i : I} {v s t : List I} (x : PrependIdx i s t)
    (y : NFIdx v (x.oldTarget ++ [i])) : PrependIdx i v (t ++ [i]) :=
  ⟨(x.1.1, y.1.1, y.1.2,
    PrependShuffle.cast (alphaExtendedHeight x y) (PrependShuffle.extend x.1.2.2.2)),
    y.2.1, y.2.2.1, by
      have he := tgt_shift [i] v (cw (Categorification.TypeA.canWord v.length y.1.2))
      simp only [List.length_singleton, cw_map_shift, List.singleton_append] at he
      simp only [prependCrossingWord, cw_append, tgt_append, he, y.tgt_cw,
        PrependShuffle.canWord_cast, PrependShuffle.canWord_extend]
      change tgt ((i :: x.oldTarget) ++ [i]) _ = _
      rw [tgt_append_right [i]]
      · rw [x.moving_target]
      · simpa [PrependIdx.oldTarget] using
          fits_cw (Categorification.TypeA.validWord_canWord (s.length + 1) x.1.2.2.2.1⁻¹)⟩

@[simp] theorem alphaExtendedIndex_target {i : I} {v s t : List I}
    (x : PrependIdx i s t) (y : NFIdx v (x.oldTarget ++ [i])) :
    (alphaExtendedIndex x y).oldTarget = x.oldTarget ++ [i] := y.tgt_cw

@[simp] theorem alphaExtendedIndex_word {i : I} {v s t : List I}
    (x : PrependIdx i s t) (y : NFIdx v (x.oldTarget ++ [i])) :
    alphaTailWord (alphaExtendedIndex x y) = alphaTailWord x := by
  simp only [alphaTailWord, alphaExtendedIndex,
    PrependShuffle.canWord_cast, PrependShuffle.canWord_extend]

/-- Every extended smaller tail satisfies the literal stripping condition. -/
theorem alphaExtendedIndex_strippable {i : I} {v s t : List I}
    (x : PrependIdx i s t) (y : NFIdx v (x.oldTarget ++ [i])) :
    AlphaStrippable (alphaExtendedIndex x y) := by
  refine ⟨x.oldTarget, alphaExtendedIndex_target x y, ?_⟩
  rw [alphaExtendedIndex_word]
  exact alphaTailWord_fits x

/-- Stripping an extended tail returns the smaller bare tail in the actual coend. -/
theorem alphaStripTerm_extended (i : I) (v s t : List I) (x : PrependIdx i s t)
    (y : NFIdx v (x.oldTarget ++ [i])) (b : Old D Sc cutoff v (x.oldTarget ++ [i])) :
    alphaStripTerm D Sc cutoff i v t (alphaExtendedIndex x y)
      ((alphaExtendedIndex_target x y).symm ▸ b) =
        pprimeTensor D Sc cutoff i v x.oldTarget t
          (affineUnit D Sc cutoff _ _ (prependTail D Sc x)) b := by
  have hf : Fits (i :: x.oldTarget).length (alphaTailWord (alphaExtendedIndex x y)) := by
    rw [alphaExtendedIndex_word]
    exact alphaTailWord_fits x
  rw [alphaStripTerm_eq D Sc cutoff i v t (alphaExtendedIndex x y) x.oldTarget
    (alphaExtendedIndex_target x y) hf]
  have aux {q : List I} (hs : q = x.oldTarget ++ [i]) (gs : List PG)
      (hgs : gs = alphaTailWord x)
      (hc : SChain (i :: x.oldTarget) (pl (i :: x.oldTarget) gs) t) :
      alphaWordLift D Sc cutoff i v q x.oldTarget t hs gs hc (hs.symm ▸ b) =
        pprimeTensor D Sc cutoff i v x.oldTarget t
          (affineUnit D Sc cutoff _ _ (prependTail D Sc x)) b := by
    subst q; subst gs; rfl
  exact aux _ _ (alphaExtendedIndex_word x y) _

/-- The decoder recovers every smaller bare tail, for every coefficient source
and every full old quotient coefficient, including empty Hom corners. -/
theorem extract_alpha_tail (i : I) (v s t : List I) (x : PrependIdx i s t)
    (b : Old D Sc cutoff v (x.oldTarget ++ [i])) :
    extract D Sc cutoff i v t (alpha D Sc cutoff i v t
      (pprimeTensor D Sc cutoff i v x.oldTarget t
        (affineUnit D Sc cutoff _ _ (prependTail D Sc x)) b)) =
      pprimeTensor D Sc cutoff i v x.oldTarget t
        (affineUnit D Sc cutoff _ _ (prependTail D Sc x)) b := by
  by_cases hy : Nonempty (NFIdx v (x.oldTarget ++ [i]))
  · obtain ⟨y⟩ := hy
    rw [← alphaStripTerm_extended D Sc cutoff i v s t x y b,
      alpha_stripTerm D Sc cutoff i v t (alphaExtendedIndex x y)
        (alphaExtendedIndex_strippable x y), extract_pair_tail]
  · have hb : b = 0 := by
      obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (x.oldTarget ++ [i])).mkQ_surjective b
      have hr : r = 0 := by
        apply (oldAffineEquiv D Sc cutoff v (x.oldTarget ++ [i])).injective
        apply Finsupp.ext
        intro y
        exact (hy ⟨y⟩).elim
      rw [hr, map_zero]
    rw [hb]
    simp only [pprimeTensor, BalancedInduction.tensor, tmul_zero, map_zero]

/-- The full coefficient transfer is used by extraction, not merely in the image. -/
theorem extract_alpha_normalizedTerm (i : I) (v s t : List I)
    (x : PrependIdx i s t) (b : Old D Sc cutoff v (s ++ [i]))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    extract D Sc cutoff i v t
      (alpha D Sc cutoff i v t (alphaNormalizedTerm D Sc cutoff i v s t x b a)) =
        alphaNormalizedTerm D Sc cutoff i v s t x b a := by
  change extract D Sc cutoff i v t (alpha D Sc cutoff i v t
    (pprimeTensor D Sc cutoff i v x.oldTarget t
      (affineUnit D Sc cutoff _ _ (prependTail D Sc x)) _)) = _
  exact extract_alpha_tail D Sc cutoff i v s t x _

/-- Extraction recovers every prescribed pure balanced class. -/
theorem extract_alpha_tensor (i : I) (v s t : List I)
    (h : hom D Sc cutoff (i :: s) t) (b : Old D Sc cutoff v (s ++ [i])) :
    extract D Sc cutoff i v t (alpha D Sc cutoff i v t
      (pprimeTensor D Sc cutoff i v s t h b)) = pprimeTensor D Sc cutoff i v s t h b := by
  obtain ⟨f, rfl⟩ := (prependAffineEquiv D Sc cutoff i s t).symm.surjective h
  induction f using Finsupp.induction_linear with
  | zero => simp [pprimeTensor, BalancedInduction.tensor]
  | add f g hf hg =>
    have hadd (h h' : hom D Sc cutoff (i :: s) t) :
        pprimeTensor D Sc cutoff i v s t (h + h') b =
          pprimeTensor D Sc cutoff i v s t h b + pprimeTensor D Sc cutoff i v s t h' b := by
      simp only [pprimeTensor, BalancedInduction.tensor, add_tmul, map_add]
    simp only [map_add, hadd, hf, hg]
  | single x a =>
    rw [prependAffineEquiv_symm_single, ← alphaNormalizedTerm_eq]
    exact extract_alpha_normalizedTerm D Sc cutoff i v s t x b a

/-- The full-coefficient decoder is a left inverse on every balanced class. -/
theorem extract_comp_alpha (i : I) (v t : List I) :
    extract D Sc cutoff i v t ∘ₗ alpha D Sc cutoff i v t = LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro s h b
  exact extract_alpha_tensor D Sc cutoff i v s.word t h b

@[simp] theorem extract_alpha (i : I) (v t : List I)
    (z : PprimeDomain D Sc cutoff i v t) :
    extract D Sc cutoff i v t (alpha D Sc cutoff i v t z) = z :=
  LinearMap.congr_fun (extract_comp_alpha D Sc cutoff i v t) z

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Balanced crossing-column coordinates

`decode_comp_shortCross` proves a left inverse on every balanced class.
`range_shortCross` and `crossingEquiv` identify that independently prescribed
source with the original append crossing span. These are the crossing-column
prerequisites for the short-column diagram in `DeformedCyclotomicTopRow.md`.

The decoder takes values in the prescribed balanced short source. On a
nonidentity append tail it retains the crossing term of the triangular
crossing/dot identity, including its self-crossing sign. The polynomial
correction is killed only after its separate vanishing law is proved.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped Classical DirectSum TensorProduct
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
namespace ShortCrossCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Insert a shorter crossing word with its unchanged old quotient coefficient. -/
def wordLift (i : I) (v q s t : List I) (hs : q = s ++ [i])
    (L : List PG) (m : ℕ) (ht : SChain (s ++ [i]) (pl (s ++ [i]) L) t) :
    Old D Sc cutoff v q →ₗ[k] ShortTarget D Sc cutoff i v t := by
  subst q
  exact (BalancedInduction.inclusion (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ ⟨s⟩) ∘ₗ
      TensorProduct.mk k _ _ (appendMovingPower D Sc cutoff i s m ≫
        affineUnit D Sc cutoff _ _ (cl D Sc _ _ L ht))

/-- Decode the crossing part of a normalized append tail. -/
def data (i : I) (v q t : List I) (L : List PG) (m : ℕ) :
    Old D Sc cutoff v q →ₗ[k] ShortTarget D Sc cutoff i v t := by
  by_cases hL : L = []
  · exact 0
  · by_cases hs : q = q.dropLast ++ [i]
    · by_cases ht : SChain (q.dropLast ++ [i]) (pl (q.dropLast ++ [i]) L.tail) t
      · exact SKM.zsign k (D.parity i * D.parity i) ^ m •
          wordLift D Sc cutoff i v q q.dropLast t hs L.tail m ht
      · exact 0
    · exact 0

/-- Full old quotient coordinates are decoded without choosing representatives in the ideal. -/
def decode (i : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [i]) →ₗ[k] ShortTarget D Sc cutoff i v t :=
  (DirectSum.toModule k _ _ fun q : AppendIdx.Tail i v (t ++ [i]) =>
    data D Sc cutoff i v q.representative.oldTarget t
      (cw (Categorification.TypeA.canWord (v ++ [i]).length
        q.representative.1.2.2.2.1⁻¹)) q.representative.1.1) ∘ₗ
      (appendOldCoordinateEquiv D Sc cutoff 0 i v (t ++ [i])).toLinearMap

@[simp] theorem data_nil (i : I) (v q t : List I) (m : ℕ) :
    data D Sc cutoff i v q t [] m = 0 := by
  simp [data]

private theorem appendTailPair_transport {i : I} {v s s' w : List I}
    (e : s = s') (r : hom D Sc cutoff v s)
    (a : (pres D Sc).obj (ob D (s ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (b : (pres D Sc).obj (ob D (s' ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (hab : HEq a b) :
    appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ a)
      ((ideal D Sc cutoff v s).mkQ r) =
    appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ b)
      ((ideal D Sc cutoff v s').mkQ (e ▸ r)) := by
  subst s'
  cases hab
  rfl

private def appendIdentityShuffle (i : I) (v : List I) : AppendShuffle (appendLen v i) :=
  AppendShuffle.cast rfl (appendLen v i) (appendRun v.length (Fin.last v.length))

private theorem appendIdentityShuffle_word (i : I) (v : List I) :
    Categorification.TypeA.canWord (v ++ [i]).length (appendIdentityShuffle i v).1⁻¹ = [] := by
  rw [appendIdentityShuffle, AppendShuffle.canWord_cast, canWord_appendRun]
  simp

private def appendIdentityIndex (i : I) {v t : List I} (y : NFIdx v t) (m : ℕ) :
    AppendIdx i v (t ++ [i]) :=
  ⟨(m, y.1.1, y.1.2, appendIdentityShuffle i v), y.2.1, y.2.2.1, by
    have he := tgt_append_right [i] (t := v)
      (fits_cw (Categorification.TypeA.validWord_canWord v.length y.1.2))
    simpa only [appendCrossingWord, appendIdentityShuffle_word, List.append_nil,
      cw_append, tgt_append, cw, List.reverse_nil, List.map_nil,
      List.nil_append] using he.trans (congrArg (· ++ [i]) y.tgt_cw)⟩

private theorem appendIdentityIndex_target (i : I) {v t : List I} (y : NFIdx v t) (m : ℕ) :
    (appendIdentityIndex i y m).oldTarget = t := y.tgt_cw

private theorem append_cl_heq {s s' t t' : List I} {L L' : List PG}
    (hs : s = s') (ht : t = t') (hL : L = L')
    (h : SChain s (pl s L) t) (h' : SChain s' (pl s' L') t') :
    HEq (cl D Sc s t L h) (cl D Sc s' t' L' h') := by
  subst s'
  subst t'
  subst L'
  rfl

private theorem appendIdentityIndex_tail (i : I) {v t : List I}
    (y : NFIdx v t) (m : ℕ) :
    HEq (appendTail D Sc (appendIdentityIndex i y m))
      ((dotE D Sc (t ++ [i]) t.length) ^ m) := by
  have ht := appendIdentityIndex_target i y m
  have hl : v.length = t.length := by
    have he := congrArg List.length y.tgt_cw
    simpa only [length_tgt] using he
  unfold appendTail
  rw [dotE_pow]
  apply append_cl_heq D Sc (congrArg (· ++ [i]) ht) rfl
  simp only [appendIdentityIndex, appendIdentityShuffle_word, cw,
    List.reverse_nil, List.map_nil, List.append_nil, List.map_replicate, hl]

private theorem appendTail_cross_heq (i : I) (v s t : List I)
    (x : AppendIdx i v (t ++ [i])) (e : x.oldTarget = s ++ [i])
    (L : List PG)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross s.length :: L)
    (hf : Fits (s ++ [i]).length L)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t) :
    HEq (appendTail D Sc x)
      (((dotE D Sc (s ++ [i] ++ [i]) (s.length + 1)) ^ x.1.1) ≫
        crossLast D Sc s i i ≫ affineRightContext D Sc [i] _ _ (cl D Sc _ _ L h)) := by
  have hl : v.length = s.length + 1 := by
    have hh := congrArg List.length e
    simpa only [AppendIdx.oldTarget, length_tgt, List.length_append,
      List.length_singleton] using hh
  change HEq (appendTail D Sc x)
    (_ ≫ crossLast D Sc s i i ≫ (cl D Sc _ _ L h ▷ (pres D Sc).obj (ob D [i])))
  rw [dotE_pow, crossLast, cl_whiskerRight D Sc _ _ [i] hf, cl_comp, cl_comp]
  unfold appendTail
  apply append_cl_heq D Sc (congrArg (· ++ [i]) e) rfl
  simp only [hw, hl, List.map_replicate, List.singleton_append]

private def appendShuffleSizeCast {n n' : ℕ} (e : n = n') :
    AppendShuffle (show n + 1 = n + 1 from rfl) ≃
      AppendShuffle (show n' + 1 = n' + 1 from rfl) := by
  subst n'
  exact Equiv.refl _

private theorem appendShuffleSizeCast_word {n n' : ℕ} (e : n = n')
    (d : AppendShuffle (show n + 1 = n + 1 from rfl)) :
    Categorification.TypeA.canWord (n' + 1) (appendShuffleSizeCast e d).1⁻¹ =
    Categorification.TypeA.canWord (n + 1) d.1⁻¹ := by
  subst n'
  rfl

private def appendIndexWithTail (i : I) {v u w : List I} (y : NFIdx v u)
    (d : AppendShuffle (appendLen v i)) (m : ℕ)
    (h : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = w) :
    AppendIdx i v w :=
  ⟨(m, y.1.1, y.1.2, d), y.2.1, y.2.2.1, by
    rw [appendCrossingWord, cw_append, tgt_append,
      tgt_append_right [i] (fits_cw (Categorification.TypeA.validWord_canWord v.length y.1.2)),
      y.tgt_cw]
    exact h⟩

private theorem appendIndexWithTail_target (i : I) {v u w : List I} (y : NFIdx v u)
    (d : AppendShuffle (appendLen v i)) (m : ℕ)
    (h : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = w) :
    (appendIndexWithTail i y d m h).oldTarget = u := y.tgt_cw

private theorem appendTail_cross_chain {i : I} {s t : List I} (z : AppendIdx i s t) :
    SChain (z.oldTarget ++ [i])
      (pl (z.oldTarget ++ [i]) (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))) t := by
  have hz := z.2.2.2
  rw [appendCrossingWord, cw_append, tgt_append,
    tgt_append_right [i] (fits_cw (Categorification.TypeA.validWord_canWord s.length z.1.2.2.1))] at hz
  change tgt (z.oldTarget ++ [i])
    (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)) = t at hz
  simpa only [hz] using sChain_pl (z.oldTarget ++ [i])
    (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))

private theorem appendTail_cross_fits {i : I} {s t : List I} (z : AppendIdx i s t) :
    Fits (z.oldTarget ++ [i]).length
      (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)) := by
  simpa only [AppendIdx.oldTarget, List.length_append, length_tgt] using
    fits_cw (Categorification.TypeA.validWord_canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)

private theorem appendRunWord_castSucc (n : ℕ) (j : Fin (n + 1)) :
    cw (Categorification.TypeA.canWord (n + 2) (appendRun (n + 1) j.castSucc).1⁻¹) =
      PG.cross n :: cw (Categorification.TypeA.canWord (n + 1) (appendRun n j).1⁻¹) := by
  rw [canWord_appendRun, canWord_appendRun, Fin.val_castSucc]
  have hj : j.val ≤ n := Nat.lt_succ_iff.mp j.2
  rw [show n + 1 - j.val = (n - j.val) + 1 by omega, List.range'_concat, cw_append]
  simp only [cw, List.reverse_singleton, List.map_singleton, List.cons_append, List.nil_append]
  congr 2
  omega

private theorem appendCrossingShuffle_exists (i : I) (v s t : List I)
    (z : AppendIdx i s t) (hv : s.length + 1 = v.length) :
    ∃ d : AppendShuffle (appendLen v i),
      cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹) =
        PG.cross s.length ::
          cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹) := by
  let d0 := AppendShuffle.cast (appendLen s i) rfl z.1.2.2.2
  let j := (appendRunEquiv s.length).symm d0
  let d1 := appendShuffleSizeCast hv (appendRun (s.length + 1) j.castSucc)
  refine ⟨AppendShuffle.cast rfl (appendLen v i) d1, ?_⟩
  rw [AppendShuffle.canWord_cast, appendShuffleSizeCast_word]
  rw [appendRunWord_castSucc]
  have hj : appendRun s.length j = d0 := (appendRunEquiv s.length).apply_symm_apply d0
  rw [hj, AppendShuffle.canWord_cast]

private theorem appendTail_power_cross (i : I) (s t : List I) (z : AppendIdx i s t) :
    affineUnit D Sc cutoff _ _ (appendTail D Sc z) =
      appendMovingPower D Sc cutoff i z.oldTarget z.1.1 ≫
        affineUnit D Sc cutoff _ _
          (cl D Sc _ _ (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))
            (appendTail_cross_chain z)) := by
  have hl : z.oldTarget.length = s.length := by simp only [AppendIdx.oldTarget, length_tgt]
  unfold appendMovingPower
  rw [← affineUnit_comp]
  apply congrArg (affineUnit D Sc cutoff _ _)
  unfold appendTail
  rw [dotE_pow, cl_comp]
  apply eq_of_heq
  apply append_cl_heq D Sc rfl rfl
  simp only [hl, List.map_replicate]

@[simp] theorem data_cross (i : I) (v s t : List I) (L : List PG) (m : ℕ)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    data D Sc cutoff i v (s ++ [i]) t (PG.cross s.length :: L) m b =
      SKM.zsign k (D.parity i * D.parity i) ^ m •
        shortTensor D Sc cutoff i v s t
          (appendMovingPower D Sc cutoff i s m ≫
            affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h)) b := by
  dsimp only [data]
  rw [dite_eq_right (List.cons_ne_nil _ _)]
  have he : (s ++ [i]).dropLast = s := List.dropLast_concat
  rw [dite_eq_left (congrArg (· ++ [i]) he).symm]
  have ht : SChain ((s ++ [i]).dropLast ++ [i])
      (pl ((s ++ [i]).dropLast ++ [i]) (PG.cross s.length :: L).tail) t := by
    simpa only [he, List.tail_cons] using h
  rw [dite_eq_left ht, LinearMap.smul_apply]
  congr 1
  have aux (s' : List I) (e : s' = s) (hs : s ++ [i] = s' ++ [i])
      (hc : SChain (s' ++ [i]) (pl (s' ++ [i]) L) t) :
      wordLift D Sc cutoff i v (s ++ [i]) s' t hs L m hc b =
        shortTensor D Sc cutoff i v s t
          (appendMovingPower D Sc cutoff i s m ≫
            affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h)) b := by
    subst s'; rfl
  exact aux _ he _ ht

theorem decode_pair_representative (i : I) (v t : List I)
    (q : AppendIdx.Tail i v (t ++ [i]))
    (b : Old D Sc cutoff v q.representative.oldTarget) :
    decode D Sc cutoff i v t
      (appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _
        (appendTail D Sc q.representative)) b) =
    data D Sc cutoff i v q.representative.oldTarget t
      (cw (Categorification.TypeA.canWord (v ++ [i]).length
        q.representative.1.2.2.2.1⁻¹)) q.representative.1.1 b := by
  have he : decode D Sc cutoff i v t
      (appendOldReconstruct D Sc cutoff 0 i v (t ++ [i]) (DirectSum.lof k _ _ q b)) =
      data D Sc cutoff i v q.representative.oldTarget t
        (cw (Categorification.TypeA.canWord (v ++ [i]).length
          q.representative.1.2.2.2.1⁻¹)) q.representative.1.1 b := by
    simp only [decode, LinearMap.comp_apply, LinearEquiv.coe_coe,
      appendOldCoordinateEquiv_reconstruct, DirectSum.toModule_lof]
  have hu : affineUnit D Sc cutoff _ _ (appendTail D Sc q.representative) =
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        appendTail D Sc q.representative : hom D Sc cutoff
          (q.representative.oldTarget ++ [i]) (t ++ [i])) := rfl
  rw [hu]
  simpa only [appendOldReconstruct, DirectSum.toModule_lof] using he

private theorem data_transport (i : I) {v s s' t : List I}
    (e : s = s') (L : List PG) (m : ℕ) (r : hom D Sc cutoff v s) :
    data D Sc cutoff i v s t L m ((ideal D Sc cutoff v s).mkQ r) =
    data D Sc cutoff i v s' t L m ((ideal D Sc cutoff v s').mkQ (e ▸ r)) := by
  subst s'; rfl

/-- Repeated old normal forms with the same tail give the same decoded balanced class. -/
theorem decode_pair (i : I) (v t : List I)
    (x : AppendIdx i v (t ++ [i])) (r : hom D Sc cutoff v x.oldTarget) :
    decode D Sc cutoff i v t
      (appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ (appendTail D Sc x))
        ((ideal D Sc cutoff v x.oldTarget).mkQ r)) =
    data D Sc cutoff i v x.oldTarget t
      (cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹)) x.1.1
        ((ideal D Sc cutoff v x.oldTarget).mkQ r) := by
  let q : AppendIdx.Tail i v (t ++ [i]) := ⟨x.tailKey, x, rfl⟩
  have hk : x.tailKey = q.representative.tailKey := q.representative_tailKey.symm
  have ht := x.oldTarget_eq_of_tailKey_eq q.representative hk
  rw [appendTailPair_transport D Sc cutoff ht r _ _
    (appendTail_heq_of_tailKey_eq D Sc x q.representative hk), decode_pair_representative]
  have hm := congrArg Prod.fst hk
  have hd := congrArg Prod.snd hk
  change x.1.1 = q.representative.1.1 at hm
  change x.1.2.2.2 = q.representative.1.2.2.2 at hd
  rw [← hm, ← hd]
  exact (data_transport D Sc cutoff i ht _ _ r).symm

/-- Identity output tails have zero crossing coordinate. -/
theorem decode_embedding_single (i : I) (v t : List I) (m : ℕ)
    (g : hom D Sc cutoff v t) :
    decode D Sc cutoff i v t
      (appendOutputEmbedding D Sc cutoff i v t
        (Finsupp.single m ((ideal D Sc cutoff v t).mkQ g))) = 0 := by
  by_cases hg : g = 0
  · simp [hg]
  obtain ⟨y⟩ := exists_oldIndex_of_ne_zero D Sc cutoff g hg
  let x := appendIdentityIndex i y m
  have ht : x.oldTarget = t := appendIdentityIndex_target i y m
  let r : hom D Sc cutoff v x.oldTarget := ht.symm ▸ g
  have hr : ht ▸ r = g := by
    exact (show ∀ {a b : List I} (e : a = b) (z : hom D Sc cutoff v b),
      e ▸ (e.symm ▸ z : hom D Sc cutoff v a) = z from
        by intro a b e z; cases e; rfl) ht g
  have he := appendTailPair_transport D Sc cutoff ht r
    (appendTail D Sc x) ((dotE D Sc (t ++ [i]) t.length) ^ m)
    (appendIdentityIndex_tail D Sc i y m)
  rw [hr] at he
  have hc := decode_pair D Sc cutoff i v t x r
  rw [he] at hc
  have hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) = [] := by
    simp only [x, appendIdentityIndex, appendIdentityShuffle_word, cw,
      List.reverse_nil, List.map_nil]
  rw [hw, data_nil, LinearMap.zero_apply] at hc
  simpa only [appendOutputEmbedding_single, appendPair_mk, twist_zero,
    appendMovingPower, x, appendIdentityIndex] using hc

theorem decode_embedding (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    decode D Sc cutoff i v t (appendOutputEmbedding D Sc cutoff i v t f) = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | single m b =>
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
    exact decode_embedding_single D Sc cutoff i v t m g

/-- The entire long correction vanishes under the decoder, with full old coefficients. -/
theorem decode_outputPolynomial_precomp (i : I) (v s t : List I)
    (r : hom D Sc cutoff v s) (f : ℕ →₀ hom D Sc cutoff s t) :
    decode D Sc cutoff i v t
      (appendProjection D Sc cutoff i v (t ++ [i])
        (rightContext D Sc cutoff [i] _ _ r ≫ appendOutputPolynomial D Sc cutoff i s t f)) = 0 := by
  rw [appendOutputPolynomial_precomp, ← appendOutputEmbedding_map, decode_embedding]

/-- Recover a canonical crossing only after applying the full triangular law.
The identity-row correction is present and is annihilated by the preceding theorem. -/
theorem decode_canonical_crossing (i : I) (v s t : List I)
    (x : AppendIdx i v (t ++ [i])) (e : x.oldTarget = s ++ [i])
    (L : List PG)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross s.length :: L)
    (hf : Fits (s ++ [i]).length L)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t)
    (r : hom D Sc cutoff v x.oldTarget) :
    decode D Sc cutoff i v t
      (appendCrossingClass D Sc cutoff i v s t (e ▸ r)
        (appendMovingPower D Sc cutoff i s x.1.1 ≫
          affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h))) =
      shortTensor D Sc cutoff i v s t
        (appendMovingPower D Sc cutoff i s x.1.1 ≫
          affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h))
        ((ideal D Sc cutoff v (s ++ [i])).mkQ (e ▸ r)) := by
  have he := appendTailPair_transport D Sc cutoff e r _ _
    (appendTail_cross_heq D Sc i v s t x e L hw hf h)
  have hc := decode_pair D Sc cutoff i v t x r
  rw [he, hw, data_transport D Sc cutoff i e, data_cross D Sc cutoff i v s t L x.1.1 h] at hc
  simp only [appendPair_mk, twist_zero, affineUnit_comp,
    ← rightContext_affineUnit] at hc
  have hp : appendMovingPower D Sc cutoff i (s ++ [i]) x.1.1 =
      affineUnit D Sc cutoff _ _ ((dotE D Sc (s ++ [i] ++ [i]) (s.length + 1)) ^ x.1.1) := by
    simp only [appendMovingPower, List.length_append, List.length_singleton]
  rw [← hp, appendProjection_crossing_power_triangular, map_add, map_smul,
    decode_outputPolynomial_precomp, add_zero] at hc
  have hu : IsUnit (SKM.zsign k (D.parity i * D.parity i) ^ x.1.1) := by
    apply IsUnit.pow
    unfold SKM.zsign
    split <;> simp
  exact hu.smul_left_cancel.mp hc

/-- Recover every smaller append tail, including zero Hom corners. -/
theorem decode_crossing_tail (i : I) (v s t : List I)
    (z : AppendIdx i s t) (r : hom D Sc cutoff v (z.oldTarget ++ [i])) :
    decode D Sc cutoff i v t
      (appendCrossingClass D Sc cutoff i v z.oldTarget t r
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z))) =
      shortTensor D Sc cutoff i v z.oldTarget t
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z))
        ((ideal D Sc cutoff v (z.oldTarget ++ [i])).mkQ r) := by
  by_cases hr : r = 0
  · simp [hr, appendCrossingClass, shortTensor, BalancedInduction.tensor]
  obtain ⟨y⟩ := exists_oldIndex_of_ne_zero D Sc cutoff r hr
  have hv : s.length + 1 = v.length := by
    have hh := congrArg List.length y.tgt_cw
    simpa only [length_tgt, List.length_append, List.length_singleton,
      AppendIdx.oldTarget] using hh.symm
  obtain ⟨d, hd⟩ := appendCrossingShuffle_exists i v s t z hv
  have hzlen : z.oldTarget.length = s.length := by simp only [AppendIdx.oldTarget, length_tgt]
  let L := cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)
  have hc := appendTail_cross_chain z
  have hf := appendTail_cross_fits z
  have htarget : tgt (z.oldTarget ++ [i] ++ [i])
      (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = t ++ [i] := by
    rw [hd, show PG.cross s.length = PG.cross z.oldTarget.length from congrArg PG.cross hzlen.symm,
      tgt_cons]
    have hcross : tgt (z.oldTarget ++ [i] ++ [i]) [PG.cross z.oldTarget.length] =
        z.oldTarget ++ [i] ++ [i] := tgt_eq (by simpa using sChain_crossAt z.oldTarget [] i i)
    simp only [tgt_cons, tgt_nil] at hcross
    rw [hcross]
    exact (tgt_append_right [i] hf).trans (congrArg (· ++ [i]) (tgt_eq hc))
  let x := appendIndexWithTail i y d z.1.1 htarget
  have he : x.oldTarget = z.oldTarget ++ [i] := appendIndexWithTail_target i y d z.1.1 htarget
  let r' : hom D Sc cutoff v x.oldTarget := he.symm ▸ r
  have hr' : he ▸ r' = r := by
    exact (show ∀ {a b : List I} (e : a = b) (q : hom D Sc cutoff v b),
      e ▸ (e.symm ▸ q : hom D Sc cutoff v a) = q from
        by intro a b e q; cases e; rfl) he r
  have hword : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross z.oldTarget.length :: L := by simpa only [x, appendIndexWithTail, hzlen] using hd
  have hh := decode_canonical_crossing D Sc cutoff i v z.oldTarget t
    x he L hword hf hc r'
  rw [hr'] at hh
  rw [appendTail_power_cross]
  exact hh

/-- Full affine balance in the independently defined short source. -/
theorem tensor_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    shortTensor D Sc cutoff i v s t (rightContext D Sc cutoff [i] _ _ r ≫ c) b =
      shortTensor D Sc cutoff i v s' t c
        ((coefficient D Sc cutoff (D.parity i) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) :=
  BalancedInduction.balance (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v)
    (v := ⟨s⟩) (v' := ⟨s'⟩) r c b

/-- The prescribed column on an arbitrary lifted old quotient coefficient. -/
theorem column_mk (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (r : hom D Sc cutoff v (s ++ [i])) :
    shortCross D Sc cutoff i v t
      (shortTensor D Sc cutoff i v s t c ((ideal D Sc cutoff _ _).mkQ r)) =
      appendCrossingClass D Sc cutoff i v s t r c := by
  rw [shortCross_tensor, shortCrossPair_mk]
  rfl

/-- Recovery on a smaller tail for every old quotient coefficient. -/
theorem decode_short_tail (i : I) (v s t : List I) (z : AppendIdx i s t)
    (b : Old D Sc cutoff v (z.oldTarget ++ [i])) :
    decode D Sc cutoff i v t (shortCross D Sc cutoff i v t
      (shortTensor D Sc cutoff i v z.oldTarget t
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z)) b)) =
      shortTensor D Sc cutoff i v z.oldTarget t
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z)) b := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (z.oldTarget ++ [i])).mkQ_surjective b
  rw [column_mk]
  exact decode_crossing_tail D Sc cutoff i v s t z r

/-- Every full-coefficient balanced generator is recovered. -/
theorem decode_tensor (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    decode D Sc cutoff i v t (shortCross D Sc cutoff i v t
      (shortTensor D Sc cutoff i v s t c b)) = shortTensor D Sc cutoff i v s t c b := by
  obtain ⟨f, rfl⟩ := (appendAffineEquiv D Sc cutoff i s t).symm.surjective c
  induction f using Finsupp.induction_linear with
  | zero => simp [shortTensor, BalancedInduction.tensor]
  | add f g hf hg =>
    have hadd (c c' : hom D Sc cutoff (s ++ [i]) t) :
        shortTensor D Sc cutoff i v s t (c + c') b =
          shortTensor D Sc cutoff i v s t c b + shortTensor D Sc cutoff i v s t c' b := by
      simp only [shortTensor, BalancedInduction.tensor, TensorProduct.add_tmul, map_add]
    simp only [map_add, hadd, hf, hg]
  | single z a =>
    rw [appendAffineEquiv_symm_single]
    have hfactor : (a ⊗ₜ[k] appendElt D Sc z : hom D Sc cutoff (s ++ [i]) t) =
        rightContext D Sc cutoff [i] _ _
          (coefficientTwist D cutoff (appendTailParity D z) a ⊗ₜ[k] z.old.nf) ≫
            affineUnit D Sc cutoff _ _ (appendTail D Sc z) := by
      have he : affineUnit D Sc cutoff _ _ (appendTail D Sc z) =
          ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc z :
            hom D Sc cutoff (z.oldTarget ++ [i]) t) := rfl
      rw [he]
      exact (append_insert_twisted_coefficient D Sc cutoff z a).symm
    rw [hfactor, tensor_balance]
    exact decode_short_tail D Sc cutoff i v s t z _

/-- Left inverse on all balanced classes, not only their chosen representatives. -/
theorem decode_comp_shortCross (i : I) (v t : List I) :
    decode D Sc cutoff i v t ∘ₗ shortCross D Sc cutoff i v t = LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro s c b
  exact decode_tensor D Sc cutoff i v s.word t c b

@[simp] theorem decode_shortCross (i : I) (v t : List I)
    (z : ShortTarget D Sc cutoff i v t) :
    decode D Sc cutoff i v t (shortCross D Sc cutoff i v t z) = z :=
  LinearMap.congr_fun (decode_comp_shortCross D Sc cutoff i v t) z

theorem shortCross_injective (i : I) (v t : List I) :
    Function.Injective (shortCross D Sc cutoff i v t) :=
  Function.LeftInverse.injective (decode_shortCross D Sc cutoff i v t)

/-- The range is the original crossing span with arbitrary full old arrows on both sides. -/
theorem range_shortCross (i : I) (v t : List I) :
    LinearMap.range (shortCross D Sc cutoff i v t) = appendCrossingSpan D Sc cutoff i v t := by
  apply le_antisymm
  · have hc : appendC0 D Sc cutoff i v t ∘ₗ shortCross D Sc cutoff i v t = 0 := by
      apply BalancedInduction.hom_ext
      intro s c b
      obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
      change appendC0 D Sc cutoff i v t
        (shortCross D Sc cutoff i v t (shortTensor D Sc cutoff i v s.word t c
          ((ideal D Sc cutoff _ _).mkQ r))) = 0
      rw [column_mk, appendC0_crossing]
    rintro z ⟨a, rfl⟩
    rw [← appendC0_ker]
    exact LinearMap.congr_fun hc a
  · apply Submodule.span_le.mpr
    rintro z ⟨s, r, c, rfl⟩
    exact ⟨shortTensor D Sc cutoff i v s t c ((ideal D Sc cutoff _ _).mkQ r),
      column_mk D Sc cutoff i v s t c r⟩

/-- The independently balanced short source identifies with the genuine crossing span. -/
def crossingEquiv (i : I) (v t : List I) :
    ShortTarget D Sc cutoff i v t ≃ₗ[k] appendCrossingSpan D Sc cutoff i v t where
  toFun z := ⟨shortCross D Sc cutoff i v t z, by
    rw [← range_shortCross]; exact ⟨z, rfl⟩⟩
  invFun z := decode D Sc cutoff i v t z.1
  left_inv := decode_shortCross D Sc cutoff i v t
  right_inv z := by
    apply Subtype.ext
    have hz : z.1 ∈ LinearMap.range (shortCross D Sc cutoff i v t) := by
      rw [range_shortCross]; exact z.2
    obtain ⟨a, ha⟩ := hz
    change shortCross D Sc cutoff i v t (decode D Sc cutoff i v t z.1) = z.1
    rw [← ha, decode_shortCross]
  map_add' a b := Subtype.ext (map_add _ a b)
  map_smul' a b := Subtype.ext (map_smul _ a b)

end ShortCrossCoordinates
end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

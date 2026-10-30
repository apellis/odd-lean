/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicShortColumns
import OddMath.QuiverHecke.CyclotomicAction.ELVPrependDescent
import OddMath.QuiverHecke.CyclotomicAction.ELVPInjective

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

namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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

/-- Full PBW normalization is the original balanced class, on every source object. -/
theorem alphaNormalize_eq_tensor (i : I) (v s t : List I)
    (h : hom D Sc cutoff (i :: s) t) (b : Old D Sc cutoff v (s ++ [i])) :
    alphaNormalize D Sc cutoff i v s t b h = pprimeTensor D Sc cutoff i v s t h b := by
  obtain ⟨f, rfl⟩ := (prependAffineEquiv D Sc cutoff i s t).symm.surjective h
  induction f using Finsupp.induction_linear with
  | zero => simp [alphaNormalize, pprimeTensor, BalancedInduction.tensor]
  | add f g hf hg =>
    simp only [map_add, hf, hg, pprimeTensor, BalancedInduction.tensor,
      TensorProduct.add_tmul]
  | single x a =>
    change Finsupp.lsum k (alphaNormalizedTerm D Sc cutoff i v s t · b)
      ((prependAffineEquiv D Sc cutoff i s t)
        ((prependAffineEquiv D Sc cutoff i s t).symm (Finsupp.single x a))) = _
    rw [LinearEquiv.apply_symm_apply, Finsupp.lsum_single,
      prependAffineEquiv_symm_single, alphaNormalizedTerm_eq]

/-- Cross-source independence of the finite normalization under the full lower balance. -/
theorem alphaNormalize_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (h : hom D Sc cutoff (i :: s') t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    alphaNormalize D Sc cutoff i v s t b (insert D Sc cutoff i s s' r ≫ h) =
      alphaNormalize D Sc cutoff i v s' t
        ((coefficient D Sc cutoff (epsilon D cutoff i v) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) h := by
  rw [alphaNormalize_eq_tensor, alphaNormalize_eq_tensor, pprimeTensor_balance]

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

/-- The decoder is a left inverse on every canonical short-tail balanced class,
with arbitrary old quotient coefficient. The comparison with all smaller
tails is supplied by `alphaExtendedIndex` and `extract_alpha_tail` below. -/
theorem extract_alpha_stripTerm (i : I) (v t : List I)
    (q : PrependIdx.Tail i v (t ++ [i])) (hq : AlphaStrippable q.representative)
    (b : Old D Sc cutoff v q.representative.oldTarget) :
    extract D Sc cutoff i v t
      (alpha D Sc cutoff i v t (alphaStripTerm D Sc cutoff i v t q.representative b)) =
        alphaStripTerm D Sc cutoff i v t q.representative b := by
  rw [alpha_stripTerm D Sc cutoff i v t q.representative hq]
  have hu : affineUnit D Sc cutoff _ _ (prependTail D Sc q.representative) =
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        prependTail D Sc q.representative) := rfl
  rw [hu]
  simpa only [prependOldReconstruct, DirectSum.toModule_lof] using
    extract_reconstruct_of D Sc cutoff i v t q b

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

/-- The actual short source column is injective, without an independence premise. -/
theorem alpha_injective (i : I) (v t : List I) :
    Function.Injective (alpha D Sc cutoff i v t) :=
  Function.LeftInverse.injective (extract_alpha D Sc cutoff i v t)

/-- The actual short moving-word map is injective by the actual column square.
No injectivity of the crossing column is needed for this implication. -/
theorem pprime_injective (i : I) (v t : List I) :
    Function.Injective (pprime D Sc cutoff i v t) := by
  intro z z' h
  apply alpha_injective D Sc cutoff i v t
  apply pMap_injective D Sc cutoff i v (t ++ [i])
  have hz := LinearMap.congr_fun (shortColumn_square D Sc cutoff i v t) z
  have hz' := LinearMap.congr_fun (shortColumn_square D Sc cutoff i v t) z'
  change pMap D Sc cutoff i v (t ++ [i]) (alpha D Sc cutoff i v t z) =
    shortCross D Sc cutoff i v t (pprime D Sc cutoff i v t z) at hz
  change pMap D Sc cutoff i v (t ++ [i]) (alpha D Sc cutoff i v t z') =
    shortCross D Sc cutoff i v t (pprime D Sc cutoff i v t z') at hz'
  rw [hz, hz', h]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

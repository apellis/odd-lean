import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import OddMath.QuiverHecke.ShuffleBasis
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import OddMath.QuiverHecke.CyclotomicAction.MovingShiftRelations
import OddMath.QuiverHecke.CentreFinite
import OddMath.QuiverHecke.CyclotomicAction.EndpointPolynomials
import OddMath.QuiverHecke.CyclotomicAction.AppendBalance

/-!
# Parabolic transport

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Output-parabolic spanning over full ELV coefficients

The affine spanning input (C) of `DeformedIdealSum.md`, in matrix-Hom
coordinates. The shuffle precedes the two parabolic normal forms in diagram
order; hence it follows the parabolic factor in algebra order. Tensoring the
proved affine basis equivalence retains the whole exterior coefficient algebra
and requires no flatness. No cyclotomic polynomial is moved through a factor.

`ideal_le_of_parabolic_terms` is the consumer for (IS2): it reduces containment
of the full cyclotomic ideal to the explicitly displayed shuffle/parabolic
terms. Parabolic normality and the short/long shuffle calculation are still
required to put these terms in the append-old span plus the prescribed W image.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Full-coefficient output-parabolic coordinates, before any cyclotomic quotient. -/
def shuffleAffineEquiv {t l r : List I} (hN : l.length + r.length = t.length) :
    hom D Sc cutoff t (l ++ r) ≃ₗ[k]
      (ShIdx hN →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
  (TensorProduct.congr (LinearEquiv.refl k _) (shuffleBasis D Sc hN).repr).trans
    (TensorProduct.finsuppScalarRight k k _ _)

@[simp] theorem shuffleAffineEquiv_symm_single {t l r : List I}
    (hN : l.length + r.length = t.length) (x : ShIdx hN)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (shuffleAffineEquiv D Sc cutoff hN).symm (Finsupp.single x a) =
      a ⊗ₜ[k] shElt D Sc x := by
  change (TensorProduct.congr (LinearEquiv.refl k _) (shuffleBasis D Sc hN).repr).symm
    ((TensorProduct.finsuppScalarRight k k _ _).symm (Finsupp.single x a)) = _
  rw [TensorProduct.finsuppScalarRight_symm_apply_single, TensorProduct.congr_symm_tmul]
  simp only [LinearEquiv.refl_symm, LinearEquiv.refl_apply, Module.Basis.repr_symm_single,
    one_smul, shuffleBasis_apply]

/-- A unit-coefficient affine prefix introduces no coefficient sign. -/
theorem affineUnit_comp_coefficient {v w z : List I}
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w))
    (g : (pres D Sc).obj (ob D w) ⟶ (pres D Sc).obj (ob D z))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    affineUnit D Sc cutoff v w f ≫ (a ⊗ₜ[k] g : hom D Sc cutoff w z) =
      a ⊗ₜ[k] (f ≫ g) := by
  induction g using Supercategory.induction_on (R := k) (C := (pres D Sc).Presented) with
  | zero => simp only [TensorProduct.tmul_zero, Limits.comp_zero]
  | add g h hg hh =>
    have hadd := Preadditive.comp_add _ _ _ (affineUnit D Sc cutoff v w f)
      (a ⊗ₜ[k] g : hom D Sc cutoff w z) (a ⊗ₜ[k] h : hom D Sc cutoff w z)
    rw [TensorProduct.tmul_add, hadd, hg, hh, Preadditive.comp_add,
      TensorProduct.tmul_add]
  | hom q g hg =>
    change BoxProd.tmulHom (X := obj D Sc cutoff v) (Y := obj D Sc cutoff w)
      (SuperalgebraCat.ofElem 1) f ≫
        BoxProd.tmulHom (X := obj D Sc cutoff w) (Y := obj D Sc cutoff z)
          (SuperalgebraCat.ofElem a) g = _
    rw [BoxProd.tmulHom_comp_tmulHom
      (show (SuperalgebraCat.ofElem (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)) ∈
        parity (R := k) (obj D Sc cutoff v).fst (obj D Sc cutoff w).fst 0 from
        id_mem (R := k) _) f (SuperalgebraCat.ofElem a) hg]
    simp only [koszulSign_zero_left, one_smul]
    change (a * 1) ⊗ₜ[k] (f ≫ g) = _
    rw [mul_one]

/-- The two block normal forms with an arbitrary full ELV coefficient. -/
def shuffleParabolic {t l r : List I} {hN : l.length + r.length = t.length}
    (x : ShIdx hN) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    hom D Sc cutoff (shL t l.length x.1.1 ++ shR t l.length x.1.1) (l ++ r) :=
  a ⊗ₜ[k] (((pres D Sc).obj (ob D (shL t l.length x.1.1)) ◁ x.2.2.nf) ≫
    (x.2.1.nf ▷ (pres D Sc).obj (ob D r)))

/-- The coefficient stays in the parabolic factor, with the shuffle on the required side. -/
theorem shuffle_parabolic_factorization {t l r : List I}
    {hN : l.length + r.length = t.length} (x : ShIdx hN)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    affineUnit D Sc cutoff _ _ (shPsi D Sc l.length x.1.1) ≫
      shuffleParabolic D Sc cutoff x a = a ⊗ₜ[k] shElt D Sc x := by
  exact affineUnit_comp_coefficient D Sc cutoff _ _ a

/-- The concrete finite parabolic terms span the full Hom, including exterior coefficients. -/
theorem hom_mem_of_shuffle_parabolic {t l r : List I}
    (hN : l.length + r.length = t.length) (S : Submodule k (hom D Sc cutoff t (l ++ r)))
    (hS : ∀ (x : ShIdx hN) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff),
      affineUnit D Sc cutoff _ _ (shPsi D Sc l.length x.1.1) ≫
        shuffleParabolic D Sc cutoff x a ∈ S)
    (f : hom D Sc cutoff t (l ++ r)) : f ∈ S := by
  obtain ⟨c, rfl⟩ := (shuffleAffineEquiv D Sc cutoff hN).symm.surjective f
  induction c using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using S.zero_mem
  | add c d hc hd => simpa only [map_add] using S.add_mem hc hd
  | single x a =>
    rw [shuffleAffineEquiv_symm_single]
    rw [← shuffle_parabolic_factorization]
    exact hS x a

/-- Length-mismatched full coefficient Homs vanish; no finite colour type is needed. -/
theorem hom_eq_zero_of_length_ne {v w : List I} (h : v.length ≠ w.length)
    (f : hom D Sc cutoff v w) : f = 0 := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => rw [hf, hg, add_zero]
  | tmul a f =>
    have hf : f = 0 := hom_eq_zero_of_content_ne D Sc (fun hc => h (by
      have hh := congrArg Multiset.card hc
      simpa using hh)) f
    rw [hf, TensorProduct.tmul_zero]

/-- There is no old first-position relation at the empty word. -/
theorem ideal_nil (w : List I) : ideal D Sc cutoff [] w = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨j, t, a, b, rfl⟩
  rw [hom_eq_zero_of_length_ne D Sc cutoff (by simp : ([] : List I).length ≠
    (j :: t).length) a, Limits.zero_comp]
  exact Submodule.zero_mem _

/-- Output-parabolic reduction of full ideal containment. The remaining hypothesis is
on explicit shuffle terms, not on the ideal itself or a cyclotomic quotient. -/
theorem ideal_le_of_parabolic_terms (v w : List I)
    (S : Submodule k (hom D Sc cutoff v w))
    (hS : ∀ (j : I) (t : List I) (hN : [j].length + t.length = v.length)
      (x : ShIdx hN) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
      (b : hom D Sc cutoff (j :: t) w),
      (affineUnit D Sc cutoff _ _ (shPsi D Sc [j].length x.1.1) ≫
        shuffleParabolic D Sc cutoff x a) ≫ relation D Sc cutoff j t ≫ b ∈ S) :
    ideal D Sc cutoff v w ≤ S := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, t, f, b, rfl⟩
  by_cases hN : [j].length + t.length = v.length
  · let L : hom D Sc cutoff v (j :: t) →ₗ[k] hom D Sc cutoff v w :=
      (Linear.rightComp k _ b).comp (Linear.rightComp k _ (relation D Sc cutoff j t))
    rw [← Category.assoc]
    change f ∈ S.comap L
    apply hom_mem_of_shuffle_parabolic D Sc cutoff hN (S.comap L) _ f
    intro x a
    change ((_ ≫ _) ≫ relation D Sc cutoff j t) ≫ b ∈ S
    simpa only [Category.assoc] using hS j t hN x a b
  · have hlen : v.length ≠ (j :: t).length := by
      simp only [List.length_cons, List.length_nil] at hN ⊢
      omega
    have hf := hom_eq_zero_of_length_ne D Sc cutoff hlen f
    rw [hf, Limits.zero_comp]
    exact S.zero_mem

/-- The precise remaining shuffle calculation for (IS2), with its prescribed W image. -/
theorem ideal_le_appendRelations_sup_range_of_parabolic_terms (i : I) (v w : List I)
    (hS : ∀ (j : I) (t : List I) (hN : [j].length + t.length = (v ++ [i]).length)
      (x : ShIdx hN) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
      (b : hom D Sc cutoff (j :: t) w),
      (affineUnit D Sc cutoff _ _ (shPsi D Sc [j].length x.1.1) ≫
        shuffleParabolic D Sc cutoff x a) ≫ relation D Sc cutoff j t ≫ b ∈
          appendRelations D Sc cutoff i v w ⊔
            LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i v))) :
    ideal D Sc cutoff (v ++ [i]) w ≤ appendRelations D Sc cutoff i v w ⊔
      LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i v)) :=
  ideal_le_of_parabolic_terms D Sc cutoff (v ++ [i]) w _ hS

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Inverse first-dot transport over full ELV coefficients

The local first-dot step of `DeformedIdealSum.md`. In diagram order the inverse
normalizer translates by +2 delta at even cutoff and -2 delta at odd cutoff.
The coefficient boundary relation is used, including at cutoff zero.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def c (j : {j : I // D.parity j = 1}) (N r : ℕ) :=
  SKM.SYM.elvCoefficientQuotient (k := k) D cutoff
    (((-1 : k) ^ (N * (r + 1))) • SKM.SYM.elvCoefficient D k j (N-r))

private theorem c_form (j : {j : I // D.parity j = 1}) (N r : ℕ) (hr : r ≤ N) :
    c (k := k) D cutoff j N r =
      if (N-r)%2=0 then SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.elvChi D k j ((N-r)/2))
      else (-1 : k)^N • (SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j) *
        SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.elvChi D k j ((N-r)/2))) := by
  unfold c SKM.SYM.elvCoefficient
  rw [map_smul]
  by_cases h : (N-r)%2=0
  · rw [ite_eq_left h, ite_eq_left h]
    have hp : (N*(r+1))%2=0 := by
      rw [Nat.mul_mod]
      rcases Nat.mod_two_eq_zero_or_one N with hn | hn
      · simp [hn]
      · have h' : (r+1)%2=0 := by omega
        simp [h']
    rw [neg_one_pow_eq_pow_mod_two, hp, pow_zero, one_smul]
  · rw [ite_eq_right h, ite_eq_right h, map_mul]
    have hp : (N*(r+1))%2=N%2 := by
      rw [Nat.mul_mod]
      rcases Nat.mod_two_eq_zero_or_one N with hn | hn
      · simp [hn]
      · have h' : (r+1)%2=1 := by omega
        simp [hn, h']
    rw [neg_one_pow_eq_pow_mod_two (N*(r+1)), hp, ← neg_one_pow_eq_pow_mod_two N]

private theorem delta_c_step (j : {j : I // D.parity j = 1}) (N r : ℕ) (hr : r < N) :
    (if (N-r)%2=0 then 0 else (2 : k) • c D cutoff j N r) =
      (2 * (-1 : k)^N) •
        (SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j) * c D cutoff j N (r+1)) := by
  have hd : SKM.SYM.elvCoefficientQuotient (k := k) D cutoff (SKM.SYM.delta D k j) *
      SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j) = 0 := by
    rw [← map_mul, ← pow_two, SKM.SYM.delta_sq, map_zero]
  rw [c_form D cutoff j N r (by omega), c_form D cutoff j N (r+1) (by omega)]
  by_cases h : (N-r)%2=0
  · have h' : (N-(r+1))%2≠0 := by omega
    simp [h, h', ← mul_assoc, hd]
  · have h' : (N-(r+1))%2=0 := by omega
    have he : (N-r)/2=(N-(r+1))/2 := by omega
    simp [h, h', he, smul_smul]

private theorem delta_c_zero (j : {j : I // D.parity j = 1}) :
    SKM.SYM.elvCoefficientQuotient (k := k) D cutoff (SKM.SYM.delta D k j) *
      c D cutoff j (cutoff j.1) 0 = 0 := by
  rw [c_form D cutoff j _ 0 (Nat.zero_le _)]
  simp only [Nat.sub_zero]
  split_ifs with h
  · rw [← map_mul]
    exact SKM.SYM.elvCoefficientQuotient_top D cutoff j h
  · rw [mul_smul_comm, ← mul_assoc, ← map_mul, ← pow_two, SKM.SYM.delta_sq, map_zero,
      zero_mul, smul_zero]

private def term (w : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    hom D Sc cutoff w w := a ⊗ₜ[k] (dotE D Sc w 0 ^ n : End _)

private theorem term_pre (w : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (m n : ℕ) :
    term D Sc cutoff w 1 m ≫ term D Sc cutoff w a n = term D Sc cutoff w a (n+m) := by
  change BoxProd.tmulHom (X := obj D Sc cutoff w) (Y := obj D Sc cutoff w)
    (𝟙 _) (dotE D Sc w 0 ^ m) ≫
    BoxProd.tmulHom (X := obj D Sc cutoff w) (Y := obj D Sc cutoff w) a (dotE D Sc w 0 ^ n) = _
  dsimp only [obj, elvQuotientObj, coefficientObj]
  rw [BoxProd.tmulHom_comp_tmulHom_eq]
  simp only [proj_id, ↓reduceIte, one_ne_zero, Category.id_comp, Limits.zero_comp,
    BoxProd.tmulHom_def, TensorProduct.zero_tmul]
  change a ⊗ₜ[k] ((dotE D Sc w 0 ^ n) * (dotE D Sc w 0 ^ m)) = _
  rw [← pow_add]
  rfl

private theorem term_post (w : List I)
    (a b : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    term D Sc cutoff w b n ≫ term D Sc cutoff w a 0 = term D Sc cutoff w (a*b) n := by
  change BoxProd.tmulHom (X := obj D Sc cutoff w) (Y := obj D Sc cutoff w)
    b (dotE D Sc w 0 ^ n) ≫
    BoxProd.tmulHom (X := obj D Sc cutoff w) (Y := obj D Sc cutoff w) a (𝟙 _) = _
  dsimp only [obj, elvQuotientObj, coefficientObj]
  rw [BoxProd.tmulHom_comp_tmulHom_eq]
  simp only [twist_id, Category.comp_id, ← BoxProd.tmulHom_add_left,
    ← Preadditive.add_comp, proj_add_proj]
  rfl

private theorem term_smul (w : List I) (s : k)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    term D Sc cutoff w (s • a) n = s • term D Sc cutoff w a n :=
  TensorProduct.smul_tmul' _ _ _

private theorem term_zero (w : List I) (n : ℕ) : term D Sc cutoff w 0 n = 0 :=
  TensorProduct.zero_tmul _ _

private theorem c_mem (j : {j : I // D.parity j = 1}) (N r : ℕ) :
    c (k := k) D cutoff j N r ∈ SKM.SYM.elvCoefficientParity D cutoff ((N-r : ℕ) : ZMod 2) := by
  have h := SKM.SYM.elvModelQuotient_mem D (cutoff := cutoff)
    (SKM.SYM.elvCoefficient_mem_parity (k := k) D j (N-r))
  have h' := (SKM.SYM.elvCoefficientParity (k := k) D cutoff ((N-r : ℕ) : ZMod 2)).smul_mem
    ((-1 : k)^(N*(r+1))) h
  simpa [SKM.SYM.elvModelQuotient, c] using h'

private theorem term_dot (j : {j : I // D.parity j = 1}) (v : List I) (N r : ℕ) :
    term D Sc cutoff (j.1::v) (c D cutoff j N r) r ≫ term D Sc cutoff (j.1::v) 1 1 =
      if (N-r)%2=0 then term D Sc cutoff (j.1::v) (c D cutoff j N r) (r+1)
      else -term D Sc cutoff (j.1::v) (c D cutoff j N r) (r+1) := by
  have hx : dotE D Sc (j.1::v) 0 ∈ parity (R := k) _ _ 1 := by
    simpa only [List.nil_append, List.length_nil, j.property] using positionedDot_parity D Sc [] v j.1
  change BoxProd.tmulHom (X := obj D Sc cutoff (j.1::v)) (Y := obj D Sc cutoff (j.1::v))
    (c D cutoff j N r) (dotE D Sc (j.1::v) 0 ^ r) ≫
    BoxProd.tmulHom (X := obj D Sc cutoff (j.1::v)) (Y := obj D Sc cutoff (j.1::v))
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (dotE D Sc (j.1::v) 0 ^ 1) = _
  rw [pow_one, BoxProd.tmulHom_comp_tmulHom (c_mem D cutoff j N r) _ _ hx]
  change koszulSign ((N-r : ℕ) : ZMod 2) 1 •
    ((1 * c D cutoff j N r) ⊗ₜ[k] (dotE D Sc (j.1::v) 0 * dotE D Sc (j.1::v) 0 ^ r)) = _
  rw [one_mul, ← pow_succ']
  have hp : ((N-r : ℕ) : ZMod 2) = ((N-r)%2 : ℕ) := by
    simpa only [ZMod.val_natCast] using (ZMod.natCast_zmod_val ((N-r : ℕ) : ZMod 2)).symm
  rw [hp]
  by_cases he : (N-r)%2=0
  · simp [he, koszulSign, term]
  · have ho : (N-r)%2=1 := by omega
    simp [ho, koszulSign, term]

private theorem term_difference (j : {j : I // D.parity j = 1}) (v : List I)
    (N r : ℕ) (hr : r < N) :
    term D Sc cutoff (j.1::v) 1 1 ≫ term D Sc cutoff (j.1::v) (c D cutoff j N r) r -
      term D Sc cutoff (j.1::v) (c D cutoff j N r) r ≫ term D Sc cutoff (j.1::v) 1 1 =
    (2 * (-1 : k)^N) • term D Sc cutoff (j.1::v)
      (SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j) * c D cutoff j N (r+1)) (r+1) := by
  rw [term_pre, term_dot]
  have hc := congrArg (fun a => term D Sc cutoff (j.1::v) a (r+1)) (delta_c_step D cutoff j N r hr)
  by_cases he : (N-r)%2=0
  · simpa only [he, ite_eq_left, term_zero, term_smul, sub_self] using hc
  · simp only [he, ↓reduceIte, term_smul] at hc
    simpa only [he, ↓reduceIte, sub_neg_eq_add, two_smul] using hc

private theorem relation_expansion (j : {j : I // D.parity j = 1}) (v : List I) :
    relation D Sc cutoff j.1 v = ∑ r : Fin (cutoff j.1 + 1),
      term D Sc cutoff (j.1::v) (c D cutoff j (cutoff j.1) r.val) r.val := by
  unfold relation
  rw [dite_eq_left j.property]
  change elvQuotientMap D Sc cutoff _ _ (elvCyclotomic D Sc j v (cutoff j.1)) = _
  rw [← elvDotPolynomial_first]
  simp only [elvDotPolynomial, coefficientDotPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact elvQuotientMap_source D Sc cutoff _ _

/-- First-dot transport in diagrammatic order. The shift is +2 delta for
    even cutoff and -2 delta for odd cutoff, in the full coefficient quotient. -/
theorem firstDot_relation_transport (j : {j : I // D.parity j = 1}) (v : List I) :
    let x : hom D Sc cutoff (j.1::v) (j.1::v) :=
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] dotE D Sc (j.1::v) 0
    let d : hom D Sc cutoff (j.1::v) (j.1::v) :=
      SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j) ⊗ₜ[k] (𝟙 _)
    x ≫ relation D Sc cutoff j.1 v =
      relation D Sc cutoff j.1 v ≫ (x + (2 * (-1 : k)^(cutoff j.1)) • d) := by
  classical
  suffices ht : term D Sc cutoff (j.1::v) 1 1 ≫ relation D Sc cutoff j.1 v =
    relation D Sc cutoff j.1 v ≫ (term D Sc cutoff (j.1::v) 1 1 +
      (2 * (-1 : k)^(cutoff j.1)) • term D Sc cutoff (j.1::v)
        (SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j)) 0) by
    simpa only [term, pow_one, pow_zero, End.one_def, obj, elvQuotientObj, coefficientObj] using ht
  rw [Preadditive.comp_add, Linear.comp_smul]
  apply sub_eq_iff_eq_add'.mp
  rw [relation_expansion, Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.sum_comp,
    ← Finset.sum_sub_distrib]
  simp only [term_post]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, term_pre, term_dot, Nat.sub_self, Nat.zero_mod,
    ite_eq_left, sub_self, add_zero]
  rw [Fin.sum_univ_succ (f := fun r : Fin (cutoff j.1 + 1) =>
    term D Sc cutoff (j.1::v)
      (SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j) *
        c D cutoff j (cutoff j.1) r.val) r.val)]
  simp only [Fin.val_zero, delta_c_zero, term_zero, zero_add, Fin.val_succ, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simpa only [term_pre, term_dot] using term_difference D Sc cutoff j v (cutoff j.1) r.val r.isLt

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Full output-parabolic transport

The first output block is a singleton. Its normal form is therefore a dot power.
Tail supernaturality and coefficient supercommutativity move the actual relation
past the remaining factors; odd first dots use `firstDot_relation_transport`,
with its cutoff-dependent +2(-1)^N delta shift. Even first dots commute.

The resulting `outputParabolic_relation_transport` has no normality, spanning,
flatness, finite-colour, or domain hypothesis. It retains the whole ELV
coefficient algebra. This module does not perform short/long shuffle reduction.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The first source block of an output-parabolic index really is [j]. -/
theorem outputParabolic_first_block {s t : List I} {j : I}
    {hlen : [j].length + t.length = s.length} (x : ShIdx hlen) :
    shL s [j].length x.1.1 = [j] := by
  have hp := tgt_perm (shL s [j].length x.1.1)
    (cw (Categorification.TypeA.canWord _ x.2.1.1.2))
  rw [x.2.1.tgt_cw] at hp
  exact (List.perm_singleton.mp hp.symm)

def parabolicTerm (j : I) (v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    hom D Sc cutoff (j :: v) (j :: v) := a ⊗ₜ[k] (dotE D Sc (j :: v) 0 ^ n : End _)

/-- Expansion of the actual relation, for every tail and cutoff, not just the one-strand corner. -/
theorem relation_full_expansion (j : I) (v : List I) :
    relation D Sc cutoff j v = ∑ r : Fin (cutoff j + 1),
      parabolicTerm D Sc cutoff j v (singleCoefficient D cutoff j r) r.val := by
  unfold relation singleCoefficient parabolicTerm
  dsimp only [elvQuotientFunctor]
  split_ifs with h
  · rw [← elvDotPolynomial_first]
    simp only [elvDotPolynomial, coefficientDotPolynomial, map_sum]
    apply Finset.sum_congr rfl
    intro r _
    exact elvQuotientMap_source D Sc cutoff _ _
  · unfold evenCyclotomic deformedCyclotomic
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [show firstDotPower D Sc (j :: v) r.val = dotE D Sc (j :: v) 0 ^ r.val by
      simp only [dotE_pow, firstDotPower, List.map_replicate]]
    exact elvQuotientMap_source D Sc cutoff _ _

/-- Exact source of the relation preceding the transported parabolic factor. -/
def outputParabolicSourceRelation {s t : List I} {j : I}
    {hlen : [j].length + t.length = s.length} (x : ShIdx hlen) :
    hom D Sc cutoff (shL s [j].length x.1.1 ++ shR s [j].length x.1.1)
      (shL s [j].length x.1.1 ++ shR s [j].length x.1.1) :=
  eqToHom (congrArg (obj D Sc cutoff)
    (congrArg (fun l => l ++ shR s [j].length x.1.1) (outputParabolic_first_block x))) ≫
  relation D Sc cutoff j (shR s [j].length x.1.1) ≫
  eqToHom (congrArg (obj D Sc cutoff)
    (congrArg (fun l => l ++ shR s [j].length x.1.1) (outputParabolic_first_block x)).symm)

theorem parabolic_dotPower_whisker (j : I) (v : List I) (n : ℕ) :
    (dotE D Sc [j] 0 ^ n : End _) ▷ (pres D Sc).obj (ob D v) =
      dotE D Sc (j :: v) 0 ^ n := by
  change whiskerWordRingHom D Sc [j] v (_ ^ n) = _
  rw [map_pow, whiskerWordRingHom_apply, dotE_whiskerRight D Sc [j] v 0 (by simp)]
  rfl

theorem parabolic_dotPower_mem (j : I) (v : List I) (n : ℕ) :
    (dotE D Sc (j :: v) 0 ^ n : End _) ∈ parity (R := k) _ _ (n • D.parity j) := by
  induction n with
  | zero => simpa only [pow_zero, zero_nsmul, End.one_def] using id_mem (R := k) _
  | succ n ih =>
    simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm, List.nil_append, List.length_nil] using
      comp_mem (positionedDot_parity D Sc [] v j) ih

theorem singleCoefficient_mem (j : I) (r : Fin (cutoff j + 1)) :
    singleCoefficient (k := k) D cutoff j r ∈ SKM.SYM.elvCoefficientParity D cutoff
      ((cutoff j : ZMod 2) * D.parity j - r.val • D.parity j) := by
  unfold singleCoefficient
  split_ifs with hj
  · have h := SKM.SYM.elvModelQuotient_mem (cutoff := cutoff) D
      (SKM.SYM.elvMonicCoefficient_mem_parity (k := k) D ⟨j, hj⟩ (cutoff j) r)
    simpa [SKM.SYM.elvModelQuotient, hj] using h
  · have he := (parity_eq_zero_or_one (D.parity j)).resolve_right hj
    have h : SKM.SYM.polynomialExteriorEquiv D k
        (SKM.SYM.evenMonicCoefficient D k j (cutoff j) r) ∈
        SKM.SYM.polynomialExteriorParity D k 0 := by
      simp only [SKM.SYM.evenMonicCoefficient, map_smul]
      apply Submodule.smul_mem
      cases cutoff j - r.val with
      | zero => simpa only [SKM.SYM.evenCyclotomicCoefficient, map_one] using
          (SetLike.GradedOne.one_mem : (1 : SKM.SYM.PolynomialExterior D k) ∈
            SKM.SYM.polynomialExteriorParity D k 0)
      | succ n => exact SKM.SYM.polynomialExterior_e_mem_even D k j n
    have hh := SKM.SYM.elvModelQuotient_mem (cutoff := cutoff) D h
    simpa [SKM.SYM.elvModelQuotient, he] using hh

theorem tail_relation_homogeneous (j : I) {v w : List I} {q : ZMod 2}
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w))
    (hf : f ∈ parity (R := k) _ _ q) :
    affineUnit D Sc cutoff _ _ (affineInsert D Sc j v w f) ≫ relation D Sc cutoff j w =
      koszulSign ((cutoff j : ZMod 2) * D.parity j) q •
        (relation D Sc cutoff j v ≫ affineUnit D Sc cutoff _ _ (affineInsert D Sc j v w f)) := by
  rw [relation_full_expansion, relation_full_expansion, Preadditive.comp_sum,
    Preadditive.sum_comp, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  unfold parabolicTerm
  rw [affineUnit_comp_coefficient]
  have hi := MonoidalSupercategory.whiskerLeft_mem ((pres D Sc).obj (ob D [j])) hf
  change _ = koszulSign ((cutoff j : ZMod 2) * D.parity j) q •
    (BoxProd.tmulHom (X := obj D Sc cutoff (j::v)) (Y := obj D Sc cutoff (j::v))
      (singleCoefficient D cutoff j r) (dotE D Sc (j::v) 0 ^ r.val) ≫
    BoxProd.tmulHom (X := obj D Sc cutoff (j::v)) (Y := obj D Sc cutoff (j::w))
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (affineInsert D Sc j v w f))
  erw [BoxProd.tmulHom_comp_tmulHom
    (X := obj D Sc cutoff (j::v)) (Y := obj D Sc cutoff (j::v))
    (Z := obj D Sc cutoff (j::w)) (singleCoefficient_mem D cutoff j r) _ _ hi]
  change _ = koszulSign ((cutoff j : ZMod 2) * D.parity j) q •
    (koszulSign ((cutoff j : ZMod 2) * D.parity j - r.val • D.parity j) q •
      ((1 * singleCoefficient D cutoff j r) ⊗ₜ[k]
        ((dotE D Sc (j::v) 0 ^ r.val : End _) ≫ affineInsert D Sc j v w f)))
  rw [one_mul, ← parabolic_dotPower_whisker D Sc j v r.val,
    ← parabolic_dotPower_whisker D Sc j w r.val]
  dsimp only [affineInsert, LinearMap.coe_mk, AddHom.coe_mk]
  erw [MonoidalSupercategory.super_interchange (parabolic_dotPower_mem D Sc j [] r.val) hf]
  erw [show singleCoefficient D cutoff j r ⊗ₜ[k]
      (koszulSign (r.val • D.parity j) q •
        (((pres D Sc).obj (ob D [j]) ◁ f) ≫
          (dotE D Sc [j] 0 ^ r.val : End _) ▷ (pres D Sc).obj (ob D w))) =
      koszulSign (r.val • D.parity j) q • (singleCoefficient D cutoff j r ⊗ₜ[k]
        (((pres D Sc).obj (ob D [j]) ◁ f) ≫
          (dotE D Sc [j] 0 ^ r.val : End _) ▷ (pres D Sc).obj (ob D w))) from
      map_zsmul (TensorProduct.mk k _ _ (singleCoefficient D cutoff j r)) _ _]
  change (singleCoefficient D cutoff j r ⊗ₜ[k]
    (((pres D Sc).obj (ob D [j]) ◁ f) ≫
      (dotE D Sc [j] 0 ^ r.val : End _) ▷ (pres D Sc).obj (ob D w))) =
    koszulSign ((cutoff j : ZMod 2) * D.parity j) q •
    (koszulSign ((cutoff j : ZMod 2) * D.parity j - r.val • D.parity j) q •
    (koszulSign (r.val • D.parity j) q •
    (singleCoefficient D cutoff j r ⊗ₜ[k]
    (((pres D Sc).obj (ob D [j]) ◁ f) ≫
      (dotE D Sc [j] 0 ^ r.val : End _) ▷ (pres D Sc).obj (ob D w)))))
  simp only [smul_smul]
  have hs : koszulSign ((cutoff j : ZMod 2) * D.parity j) q *
      (koszulSign ((cutoff j : ZMod 2) * D.parity j - r.val • D.parity j) q *
        koszulSign (r.val • D.parity j) q) = 1 := by
    rw [← koszulSign_add_left, sub_add_cancel, koszulSign_mul_self]
  rw [hs, one_smul]

theorem tail_relation_transport (j : I) {v w : List I}
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    ∃ c : hom D Sc cutoff (j::v) (j::w),
      affineUnit D Sc cutoff _ _ (affineInsert D Sc j v w f) ≫ relation D Sc cutoff j w =
        relation D Sc cutoff j v ≫ c := by
  induction f using Supercategory.induction_on (R := k) (C := (pres D Sc).Presented) with
  | zero => exact ⟨0, by simp⟩
  | add f g hf hg =>
    obtain ⟨c, hc⟩ := hf
    obtain ⟨d, hd⟩ := hg
    exact ⟨c + d, by simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hc, hd]⟩
  | hom q f hf =>
    exact ⟨koszulSign ((cutoff j : ZMod 2) * D.parity j) q •
      affineUnit D Sc cutoff _ _ (affineInsert D Sc j v w f), by
        rw [Preadditive.comp_zsmul]; exact tail_relation_homogeneous D Sc cutoff j f hf⟩

theorem scalar_relation_transport (j : I) (v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    ∃ c : hom D Sc cutoff (j::v) (j::v),
      ELVPScalar.scalar D Sc cutoff (j::v) a ≫ relation D Sc cutoff j v =
        relation D Sc cutoff j v ≫ c := by
  refine DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cutoff) ?_ ?_ ?_ a
  · exact ⟨0, by simp⟩
  · intro p a
    refine ⟨koszulSign p ((cutoff j : ZMod 2) * D.parity j) •
      ELVPScalar.scalar D Sc cutoff (j::v) a, ?_⟩
    rw [Preadditive.comp_zsmul, ELVPScalar.scalar_slide_homogeneous D Sc cutoff a.property,
      twist_of_mem p (relation_mem_parity D Sc cutoff j v), ← koszulSign_smul,
      Preadditive.comp_zsmul, smul_smul, koszulSign_mul_self, one_smul]
  · intro a b ha hb
    obtain ⟨c, hc⟩ := ha
    obtain ⟨d, hd⟩ := hb
    exact ⟨c+d, by simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hc, hd]⟩

theorem even_firstDot_relation (j : I) (hj : D.parity j = 0) (v : List I) :
    parabolicTerm D Sc cutoff j v 1 1 ≫ relation D Sc cutoff j v =
      relation D Sc cutoff j v ≫ parabolicTerm D Sc cutoff j v 1 1 := by
  rw [relation_full_expansion, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro r _
  have hx : (dotE D Sc (j::v) 0 ^ 1 : End _) ∈ parity (R := k) _ _ 0 := by
    simpa only [hj, nsmul_zero] using parabolic_dotPower_mem D Sc j v 1
  change BoxProd.tmulHom (X := obj D Sc cutoff (j::v)) (Y := obj D Sc cutoff (j::v))
    (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (dotE D Sc (j::v) 0 ^ 1) ≫
      BoxProd.tmulHom (X := obj D Sc cutoff (j::v)) (Y := obj D Sc cutoff (j::v))
        (singleCoefficient D cutoff j r) (dotE D Sc (j::v) 0 ^ r.val) = _
  erw [BoxProd.tmulHom_comp_tmulHom
    (X := obj D Sc cutoff (j::v)) (Y := obj D Sc cutoff (j::v)) (Z := obj D Sc cutoff (j::v))
    (show (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
    parity (R := k) (obj D Sc cutoff (j::v)).fst (obj D Sc cutoff (j::v)).fst 0 from id_mem (R := k) _)
    _ _ (parabolic_dotPower_mem D Sc j v r.val)]
  change _ = BoxProd.tmulHom (X := obj D Sc cutoff (j::v)) (Y := obj D Sc cutoff (j::v))
    (singleCoefficient D cutoff j r) (dotE D Sc (j::v) 0 ^ r.val) ≫
      BoxProd.tmulHom (X := obj D Sc cutoff (j::v)) (Y := obj D Sc cutoff (j::v))
        (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (dotE D Sc (j::v) 0 ^ 1)
  erw [BoxProd.tmulHom_comp_tmulHom
    (X := obj D Sc cutoff (j::v)) (Y := obj D Sc cutoff (j::v)) (Z := obj D Sc cutoff (j::v))
    (singleCoefficient_mem D cutoff j r) _ _ hx]
  simp only [koszulSign_zero_left, koszulSign_zero_right, one_smul]
  change (singleCoefficient D cutoff j r * 1) ⊗ₜ[k]
      ((dotE D Sc (j::v) 0 ^ r.val) * (dotE D Sc (j::v) 0 ^ 1)) =
    (1 * singleCoefficient D cutoff j r) ⊗ₜ[k]
      ((dotE D Sc (j::v) 0 ^ 1) * (dotE D Sc (j::v) 0 ^ r.val))
  rw [mul_one, one_mul, ← pow_add, ← pow_add, Nat.add_comm]

theorem firstDot_power_transport (j : I) (v : List I) (n : ℕ) :
    ∃ c : hom D Sc cutoff (j::v) (j::v),
      parabolicTerm D Sc cutoff j v 1 n ≫ relation D Sc cutoff j v =
        relation D Sc cutoff j v ≫ c := by
  have h₁ : ∃ c : hom D Sc cutoff (j::v) (j::v),
      parabolicTerm D Sc cutoff j v 1 1 ≫ relation D Sc cutoff j v =
        relation D Sc cutoff j v ≫ c := by
    rcases parity_eq_zero_or_one (D.parity j) with hj | hj
    · exact ⟨_, even_firstDot_relation D Sc cutoff j hj v⟩
    · exact ⟨_, by
        simpa only [parabolicTerm, pow_one] using firstDot_relation_transport D Sc cutoff ⟨j,hj⟩ v⟩
  obtain ⟨c, hc⟩ := h₁
  induction n with
  | zero => exact ⟨𝟙 _, by change 𝟙 _ ≫ _ = _ ≫ 𝟙 _; simp⟩
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    have hs : parabolicTerm D Sc cutoff j v 1 (n+1) =
        parabolicTerm D Sc cutoff j v 1 1 ≫ parabolicTerm D Sc cutoff j v 1 n := by
      change _ = affineUnit D Sc cutoff _ _ (dotE D Sc (j::v) 0 ^ 1) ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] (dotE D Sc (j::v) 0 ^ n) : hom D Sc cutoff (j::v) (j::v))
      rw [affineUnit_comp_coefficient]
      change _ = (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] ((dotE D Sc (j::v) 0 ^ n) * (dotE D Sc (j::v) 0 ^ 1))
      rw [pow_one, ← pow_succ]
      rfl
    refine ⟨c ≫ d, ?_⟩
    rw [hs, Category.assoc, hd, ← Category.assoc, hc, Category.assoc]

theorem coefficient_tail_power_transport (j : I) {v w : List I}
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) (n : ℕ)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    ∃ c : hom D Sc cutoff (j::v) (j::w),
      (a ⊗ₜ[k] (affineInsert D Sc j v w f ≫ (dotE D Sc (j::w) 0 ^ n : End _)) :
        hom D Sc cutoff (j::v) (j::w)) ≫ relation D Sc cutoff j w =
      relation D Sc cutoff j v ≫ c := by
  obtain ⟨b, hb⟩ := scalar_relation_transport D Sc cutoff j w a
  obtain ⟨d, hd⟩ := firstDot_power_transport D Sc cutoff j w n
  obtain ⟨e, he⟩ := tail_relation_transport D Sc cutoff j f
  have hfactor : (a ⊗ₜ[k] (affineInsert D Sc j v w f ≫
      (dotE D Sc (j::w) 0 ^ n : End _)) : hom D Sc cutoff (j::v) (j::w)) =
      affineUnit D Sc cutoff _ _ (affineInsert D Sc j v w f) ≫
        parabolicTerm D Sc cutoff j w 1 n ≫ ELVPScalar.scalar D Sc cutoff (j::w) a := by
    rw [← Category.assoc]
    unfold parabolicTerm
    rw [affineUnit_comp_coefficient]
    change _ = affineUnit D Sc cutoff _ _
      (affineInsert D Sc j v w f ≫ (dotE D Sc (j::w) 0 ^ n : End _)) ≫
        (a ⊗ₜ[k] 𝟙 ((pres D Sc).obj (ob D (j::w))) : hom D Sc cutoff (j::w) (j::w))
    have hh := (affineUnit_comp_coefficient D Sc cutoff
      (affineInsert D Sc j v w f ≫ (dotE D Sc (j::w) 0 ^ n : End _))
      (𝟙 ((pres D Sc).obj (ob D (j::w)))) a).symm
    rw [Category.comp_id] at hh
    exact hh
  refine ⟨e ≫ d ≫ b, ?_⟩
  rw [hfactor, Category.assoc, Category.assoc, hb, ← Category.assoc _ (relation D Sc cutoff j w),
    hd, Category.assoc, ← Category.assoc _ (relation D Sc cutoff j w), he]
  simp only [Category.assoc]

/-- A singleton first normal form and an arbitrary tail transport the full relation. -/
theorem parabolic_nf_transport (j : I) {l v w : List I} (hl : l = [j])
    (b : NFIdx l [j])
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    ∃ c : hom D Sc cutoff (l ++ v) (j::w),
      (a ⊗ₜ[k] (((pres D Sc).obj (ob D l) ◁ f) ≫
        (b.nf (D := D) (Sc := Sc) ▷ (pres D Sc).obj (ob D w))) :
          hom D Sc cutoff (l ++ v) (j::w)) ≫ relation D Sc cutoff j w =
      (eqToHom (congrArg (obj D Sc cutoff) (congrArg (fun l => l ++ v) hl)) ≫
        relation D Sc cutoff j v ≫
        eqToHom (congrArg (obj D Sc cutoff) (congrArg (fun l => l ++ v) hl).symm)) ≫ c := by
  subst l
  obtain ⟨n, rfl⟩ := (singleNFIndex_bijective j).surjective b
  simp only [singleNFIndex_nf, parabolic_dotPower_whisker, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  exact coefficient_tail_power_transport D Sc cutoff j f n a

/-- Full output-parabolic transport over the original commutative ground ring,
with all exterior coefficients and arbitrary tails and cutoffs. -/
theorem outputParabolic_relation_transport {s t : List I} {j : I}
    {hlen : [j].length + t.length = s.length} (x : ShIdx hlen)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    ∃ c : hom D Sc cutoff
      (shL s [j].length x.1.1 ++ shR s [j].length x.1.1) (j :: t),
      shuffleParabolic D Sc cutoff x a ≫ relation D Sc cutoff j t =
        outputParabolicSourceRelation D Sc cutoff x ≫ c := by
  exact parabolic_nf_transport D Sc cutoff j (outputParabolic_first_block x) x.2.1 x.2.2.nf a

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Corrected odd moving dot on the ELV source

This constructs the first-order source operator in
`docs/Nondegeneracy/DeformedMackeyBoundary.md` §1 on the full coefficient
quotient. In diagrammatic order the normalizer is
`x + 2 (-1)^N delta`; the content sign is applied after this correction.
The downstream use is the first-order Mackey boundary recurrence, not just
central-square linearity. No inverse or boundary compatibility is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The exterior coefficient as an old endomorphism. -/
def boundaryDelta (j : {j : I // D.parity j = 1}) (v : List I) :
    hom D Sc cutoff v v :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j) ⊗ₜ[k] (𝟙 _)

@[simp] theorem insert_boundaryDelta (j : {j : I // D.parity j = 1}) (v : List I) :
    insert D Sc cutoff j.1 v v (boundaryDelta D Sc cutoff j v) =
      boundaryDelta D Sc cutoff j (j.1 :: v) := by
  rw [boundaryDelta, insert_tmul]
  change _ ⊗ₜ[k] ((pres D Sc).obj (ob D [j.1]) ◁ (𝟙 _)) = _
  rw [MonoidalSupercategory.whiskerLeft_id (R := k)]
  rfl

/-- The corrected first dot before the content sign. -/
def boundaryFirstDot (j : {j : I // D.parity j = 1}) (v : List I) :
    hom D Sc cutoff (j.1 :: v) (j.1 :: v) :=
  movingPower D Sc cutoff j.1 v 1 +
    (2 * (-1 : k) ^ cutoff j.1) • boundaryDelta D Sc cutoff j (j.1 :: v)

/-- The corrected first dot preserves every old cyclotomic relation. -/
theorem boundaryFirstDot_relations (j : {j : I // D.parity j = 1}) {v w : List I}
    {h : hom D Sc cutoff (j.1 :: v) w} (hh : h ∈ relations D Sc cutoff j.1 v w) :
    boundaryFirstDot D Sc cutoff j v ≫ h ∈ relations D Sc cutoff j.1 v w := by
  rw [boundaryFirstDot, Preadditive.add_comp, Linear.smul_comp]
  apply Submodule.add_mem
  · exact movingPower_relations_twist D Sc cutoff j.1 1 hh
  · apply Submodule.smul_mem
    rw [← insert_boundaryDelta]
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨t, r, hr, f, rfl⟩ := hh
      rw [← Category.assoc, ← insert_comp]
      exact Submodule.subset_span ⟨t, _, comp_ideal D Sc cutoff _ hr, f, rfl⟩
    | zero => simp only [Limits.comp_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact Submodule.add_mem _ ha hb
    | smul a b _ hb => rw [Linear.comp_smul]; exact Submodule.smul_mem _ a hb

/-- Corrected source operator, with total moving-content sign. -/
def boundaryRho (j : {j : I // D.parity j = 1}) (v w : List I) :
    Target D Sc cutoff j.1 v w →ₗ[k] Target D Sc cutoff j.1 v w :=
  SKM.zsign k (D.parity j.1 * wordSumParity D v) •
    (relations D Sc cutoff j.1 v w).mapQ (relations D Sc cutoff j.1 v w)
      (Linear.leftComp k _ (boundaryFirstDot D Sc cutoff j v))
      (fun _ hh => boundaryFirstDot_relations D Sc cutoff j hh)

@[simp] theorem boundaryRho_projection (j : {j : I // D.parity j = 1}) (v w : List I)
    (h : hom D Sc cutoff (j.1 :: v) w) :
    boundaryRho D Sc cutoff j v w (projection D Sc cutoff j.1 v w h) =
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        projection D Sc cutoff j.1 v w (boundaryFirstDot D Sc cutoff j v ≫ h) := rfl

/-- The decorated relation factors through the corrected first dot, with both
cutoff parities and every exterior coefficient retained. -/
theorem appendDecoratedW_one_boundaryFirstDot (j : {j : I // D.parity j = 1})
    (v : List I) :
    appendDecoratedW D Sc cutoff j.1 v 1 =
      appendW D Sc cutoff j.1 v ≫ boundaryFirstDot D Sc cutoff j v := by
  have ht : movingPower D Sc cutoff j.1 v 1 ≫ relation D Sc cutoff j.1 v =
      relation D Sc cutoff j.1 v ≫ boundaryFirstDot D Sc cutoff j v := by
    simpa only [boundaryFirstDot, movingPower, pow_one, boundaryDelta]
      using firstDot_relation_transport D Sc cutoff j v
  rw [appendDecoratedW, ht, appendW, Category.assoc]

/-- First-order intertwining for the full ELV quotient at every old word.
This is the corrected odd-dot identity, not unchanged odd-dot linearity. -/
theorem pMap_boundaryRho (j : {j : I // D.parity j = 1}) (v w : List I)
    (z : Target D Sc cutoff j.1 v w) :
    pMap D Sc cutoff j.1 v w (boundaryRho D Sc cutoff j v w z) =
      appendMovingPowerTarget D Sc cutoff j.1 v w 1 (pMap D Sc cutoff j.1 v w z) := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff j.1 v w z
  rw [boundaryRho_projection, map_smul]
  have he := lastDot_comp_appendDecoratedW_mem D Sc cutoff j.1 v 0
  rw [appendDecoratedW_zero, zero_add, appendDecoratedW_one_boundaryFirstDot] at he
  have hz := (appendProjection_eq_zero_iff D Sc cutoff j.1 v w _).mpr
    (appendRelations_comp D Sc cutoff j.1 he h)
  rw [Preadditive.sub_comp, Linear.smul_comp, map_sub, map_smul, sub_eq_zero] at hz
  simpa only [pMap_projection, appendMovingPowerTarget_projection,
    appendW, Category.assoc, appendMovingPower, pow_one] using hz.symm

/-- Moving powers compose on the append quotient without a parity restriction. -/
theorem appendMovingPowerTarget_add (i : I) (v w : List I) (d e : ℕ)
    (z : AppendTarget D Sc cutoff i v w) :
    appendMovingPowerTarget D Sc cutoff i v w d
        (appendMovingPowerTarget D Sc cutoff i v w e z) =
      appendMovingPowerTarget D Sc cutoff i v w (d + e) z := by
  obtain ⟨h, rfl⟩ := (appendRelations D Sc cutoff i v w).mkQ_surjective z
  change appendProjection D Sc cutoff i v w (_ ≫ (_ ≫ h)) =
    appendProjection D Sc cutoff i v w (_ ≫ h)
  rw [← Category.assoc]
  apply congrArg (appendProjection D Sc cutoff i v w)
  apply congrArg (fun a => a ≫ h)
  unfold appendMovingPower
  rw [← affineUnit_comp]
  change affineUnit D Sc cutoff _ _
    (dotE D Sc (v ++ [i]) v.length ^ e * dotE D Sc (v ++ [i]) v.length ^ d) = _
  rw [← pow_add, Nat.add_comm e d]

/-- The square of the corrected odd dot is the unchanged moving square.
Cancellation uses the proved full-ELV injectivity of P, not an inverse assumption. -/
theorem boundaryRho_square (j : {j : I // D.parity j = 1}) (v w : List I)
    (z : Target D Sc cutoff j.1 v w) :
    boundaryRho D Sc cutoff j v w (boundaryRho D Sc cutoff j v w z) =
      signedMovingPowerTarget D Sc cutoff j.1 v w 2 z := by
  apply pMap_injective D Sc cutoff j.1 v w
  rw [pMap_boundaryRho, pMap_boundaryRho, appendMovingPowerTarget_add]
  exact (pMap_movingSquare D Sc cutoff j.1 v w z).symm

/-- Every corrected iterate has the prescribed last-dot image under P.
The dot acts on the right in algebra notation; it is not moved through the ELV polynomial. -/
theorem pMap_boundaryRho_iterate (j : {j : I // D.parity j = 1}) (v w : List I)
    (d : ℕ) (z : Target D Sc cutoff j.1 v w) :
    pMap D Sc cutoff j.1 v w ((boundaryRho D Sc cutoff j v w)^[d] z) =
      appendMovingPowerTarget D Sc cutoff j.1 v w d (pMap D Sc cutoff j.1 v w z) := by
  induction d with
  | zero =>
    obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff j.1 v w z
    simp only [Function.iterate_zero, id_eq, pMap_projection,
      appendMovingPowerTarget_projection, appendMovingPower, pow_zero,
      End.one_def, affineUnit_id, Category.id_comp]
  | succ d ih =>
    rw [Function.iterate_succ_apply', pMap_boundaryRho, ih,
      appendMovingPowerTarget_add, Nat.add_comm 1 d]

/-- Unsigned moving powers add on the old quotient. -/
theorem signedMovingPowerTarget_add (i : I) (v w : List I) (d e : ℕ)
    (z : Target D Sc cutoff i v w) :
    signedMovingPowerTarget D Sc cutoff i v w d
        (signedMovingPowerTarget D Sc cutoff i v w e z) =
      signedMovingPowerTarget D Sc cutoff i v w (d + e) z := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  simp only [signedMovingPowerTarget_projection, ← Category.assoc,
    movingPower_comp_movingPower]

/-- All even corrected iterates are the literal moving powers. -/
theorem boundaryRho_iterate_even (j : {j : I // D.parity j = 1}) (v w : List I)
    (q : ℕ) (z : Target D Sc cutoff j.1 v w) :
    (boundaryRho D Sc cutoff j v w)^[2 * q] z =
      signedMovingPowerTarget D Sc cutoff j.1 v w (2 * q) z := by
  induction q with
  | zero =>
    obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff j.1 v w z
    simp only [mul_zero, Function.iterate_zero, id_eq, signedMovingPowerTarget_projection]
    change projection D Sc cutoff j.1 v w h =
      projection D Sc cutoff j.1 v w
        (affineUnit D Sc cutoff _ _ (dotE D Sc (j.1 :: v) 0 ^ 0) ≫ h)
    rw [pow_zero, End.one_def, affineUnit_id, Category.id_comp]
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 + 2 * q by omega, Function.iterate_add_apply,
      Function.iterate_succ_apply', Function.iterate_one, boundaryRho_square,
      ih, signedMovingPowerTarget_add]

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Full-coefficient PBW coordinates of the corrected source iterates

The input-first-dot PBW coordinates of the corrected operator are computed
on every moving tail and arbitrary old quotient coefficient. The parity twist
acts on the entire old coefficient, not just its diagram. This supplies an
explicit two-term formula for every odd iterate, including the delta term.
These are input PBW coordinates; the output-last-dot Mackey extraction still
requires its separate triangular coordinate comparison.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The quotient correction is the old delta action, not a discarded scalar. -/
theorem boundaryRho_eq_moving_add_old (j : {j : I // D.parity j = 1})
    (v w : List I) (z : Target D Sc cutoff j.1 v w) :
    boundaryRho D Sc cutoff j v w z =
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        (signedMovingPowerTarget D Sc cutoff j.1 v w 1 z +
          (2 * (-1 : k) ^ cutoff j.1) •
            oldSourceTarget D Sc cutoff j.1 v w (boundaryDelta D Sc cutoff j v) z) := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff j.1 v w z
  rw [boundaryRho_projection]
  change _ = _ • (projection D Sc cutoff j.1 v w (_ ≫ h) +
    _ • projection D Sc cutoff j.1 v w (_ ≫ h))
  rw [boundaryFirstDot, Preadditive.add_comp, Linear.smul_comp, map_add, map_smul,
    insert_boundaryDelta]

/-- Exact two-term action on an arbitrary input PBW tail with arbitrary full
old coefficient and arbitrary source balance parity. -/
theorem boundaryRho_pair (p : ZMod 2) (j : {j : I // D.parity j = 1})
    {v w : List I} (x : PrependIdx j.1 v w) (b : Old D Sc cutoff v x.oldTarget) :
    boundaryRho D Sc cutoff j v w
      (pair D Sc cutoff p j.1
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) b) =
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        (pair D Sc cutoff p j.1
          ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
            prependTail D Sc (x.shift 1))
          (oldTwist D Sc cutoff (D.parity j.1) v x.oldTarget b) +
        (2 * (-1 : k) ^ cutoff j.1) •
          pair D Sc cutoff p j.1
            ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x)
            (oldPrecomp D Sc cutoff v x.oldTarget
              (twist k p (boundaryDelta D Sc cutoff j v)) b)) := by
  rw [boundaryRho_eq_moving_add_old, signedMovingPower_pair_shift, oldSourceTarget_pair,
    one_nsmul]

/-- Every even corrected iterate on every PBW tail retains the old coefficient. -/
theorem boundaryRho_iterate_even_pair (p : ZMod 2) (j : {j : I // D.parity j = 1})
    {v w : List I} (x : PrependIdx j.1 v w) (q : ℕ)
    (b : Old D Sc cutoff v x.oldTarget) :
    (boundaryRho D Sc cutoff j v w)^[2 * q]
      (pair D Sc cutoff p j.1
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) b) =
      pair D Sc cutoff p j.1
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc (x.shift (2 * q))) b := by
  rw [boundaryRho_iterate_even, signedMovingPower_pair_shift]
  have hp : (2 * q) • D.parity j.1 = 0 := by
    rw [mul_nsmul]
    simp only [j.property]
    have ht : (2 : ℕ) • (1 : ZMod 2) = 0 := by decide
    rw [ht, smul_zero]
  rw [hp]
  congr 1
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v x.oldTarget).mkQ_surjective b
  change (ideal D Sc cutoff v x.oldTarget).mkQ (twist k 0 r) = _
  rw [twist_zero]

end OddMath.QuiverHecke.ELVOld
end

end

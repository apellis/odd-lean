/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CentreFinite
import OddMath.QuiverHecke.CyclotomicAction.ELVParabolicSpan
import OddMath.QuiverHecke.CyclotomicAction.ELVOneStrand
import OddMath.QuiverHecke.CyclotomicAction.ELVFirstDotTransport
import OddMath.QuiverHecke.CyclotomicAction.ELVPScalarBalance

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

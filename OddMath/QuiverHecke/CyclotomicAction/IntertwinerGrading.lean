/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerParity

/-!
# Total parity on the induced tensors of the moving-strand map

The source and target of KKO I, arXiv:1206.5933v2, Proposition 8.4 use
`InductionAlong.Ind`, whose underlying tensor is over the integers. We put the
sum parity on that integral tensor and prove the existing balancing submodule
is homogeneous. Restricting its scalars to `k` does not change the quotient
carrier. In particular no comparison equivalence or replacement tensor is assumed.

`qSourceSpace` and `qTargetSpace` equip the existing induced modules with their
parity grading; the latter uses the already constructed `Envelope.piPow`
coefficient. The component degrees and homogeneous left action are proved.
The grading hypotheses for the concrete modules follow from affine inclusion
parity and the actual coefficient actions. The finite-colour, positive-height,
and `CyclotomicPolynomialParity` restrictions are unchanged. These ordinary
polynomial coefficients do not cover arbitrary odd-coefficient deformations.

`contentMove_parity` derives the moving-strand degree from the local generators.
`parityCyclotomicContentQ_even` proves that Q preserves these gradings: the
corner degree and coefficient shift cancel. This does not establish full
Proposition 8.4, the full right-superalgebra action, or a QP formula.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.InducedParity
universe u
variable {k : Type u} [CommRing k] (V W : SVec k)

/-- The integral tensor map, linear for the scalar action on its first factor. -/
def tensorMap (f : V →ₗ[k] V) (g : W →ₗ[k] W) :
    (V ⊗[ℤ] W) →ₗ[k] (V ⊗[ℤ] W) where
  toFun := TensorProduct.map (InductionAlong.intLinear f.toAddMonoidHom)
    (InductionAlong.intLinear g.toAddMonoidHom)
  map_add' := map_add _
  map_smul' c t := by
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp [TensorProduct.smul_tmul', InductionAlong.intLinear]
    | add s t hs ht => simp only [smul_add, map_add, hs, ht]

@[simp] theorem tensorMap_tmul (f : V →ₗ[k] V) (g : W →ₗ[k] W) (x : V) (y : W) :
    tensorMap V W f g (x ⊗ₜ[ℤ] y) = f x ⊗ₜ[ℤ] g y := rfl

/-- Total parity on the integral tensor used by `InductionAlong.Ind`. -/
def tensorSpace : SVec k where
  carrier := V ⊗[ℤ] W
  odd := tensorMap V W (V.proj 0) (W.proj 1) + tensorMap V W (V.proj 1) (W.proj 0)
  odd_comp_odd := by
    ext x y
    simp [tensorMap_tmul, SVec.proj_proj_apply, SVec.proj_zero_proj_one,
      SVec.proj_one_proj_zero]

@[simp] theorem tensorSpace_odd_tmul (x : V) (y : W) :
    (tensorSpace V W).odd (x ⊗ₜ[ℤ] y) =
      V.proj 0 x ⊗ₜ[ℤ] W.proj 1 y + V.proj 1 x ⊗ₜ[ℤ] W.proj 0 y := rfl

theorem tensorSpace_tmul_mem {p q : ZMod 2} {x : V} {y : W}
    (hx : x ∈ V.part p) (hy : y ∈ W.part q) :
    x ⊗ₜ[ℤ] y ∈ (tensorSpace V W).part (p + q) := by
  have hx' := SVec.proj_apply_of_mem_part (p := 1) V hx
  have hy' := SVec.proj_apply_of_mem_part (p := 1) W hy
  rw [SVec.proj_one] at hx' hy'
  rw [SVec.mem_part_iff (tensorSpace V W)]
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    simp_all [SVec.proj, tensorSpace_odd_tmul]

theorem induction_on {P : V → Prop} (x : V)
    (hom : ∀ p x, x ∈ V.part p → P x)
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  rw [← V.proj_apply_add x]
  exact add _ _ (hom _ _ (V.proj_mem_part 0 x)) (hom _ _ (V.proj_mem_part 1 x))

section Balance
variable {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (𝒜 : ZMod 2 → Submodule k A) [GradedAlgebra 𝒜]
  [Module B V] [IsScalarTower k B V] [Module Aᵐᵒᵖ V] [Module A W]
  [SMulCommClass B Aᵐᵒᵖ V]
  (hR : ∀ (p q : ZMod 2) (a : A) (x : V), a ∈ 𝒜 p → x ∈ V.part q →
    MulOpposite.op a • x ∈ V.part (q + p))
  (hL : ∀ (p q : ZMod 2) (a : A) (y : W), a ∈ 𝒜 p → y ∈ W.part q →
    a • y ∈ W.part (p + q))

include hR hL in
omit [GradedAlgebra 𝒜] in
/-- Homogeneous balancing generators have the same total parity on both sides. -/
theorem relation_mem {p q r : ZMod 2} {a : A} {x : V} {y : W}
    (ha : a ∈ 𝒜 p) (hx : x ∈ V.part q) (hy : y ∈ W.part r) :
    (MulOpposite.op a • x) ⊗ₜ[ℤ] y - x ⊗ₜ[ℤ] (a • y) ∈
      (tensorSpace V W).part (q + p + r) := by
  apply Submodule.sub_mem
  · exact tensorSpace_tmul_mem V W (hR p q a x ha hx) hy
  · simpa only [add_assoc] using tensorSpace_tmul_mem V W hx (hL p r a y ha hy)

include hR hL in
omit [Algebra k B] [IsScalarTower k B V] in
/-- Stability of the original integral balancing submodule under total parity. -/
theorem relation_odd_mem (t : V ⊗[ℤ] W)
    (ht : t ∈ BalancedTensor.rel ℤ B A V W) :
    (tensorSpace V W).odd t ∈ BalancedTensor.rel ℤ B A V W := by
  have hs : ∀ x : V, ∀ a : A, ∀ y : W,
      (tensorSpace V W).odd ((MulOpposite.op a • x) ⊗ₜ[ℤ] y - x ⊗ₜ[ℤ] (a • y)) ∈
        BalancedTensor.rel ℤ B A V W := by
    intro x a y
    induction x using induction_on V with
    | add x x' hx hx' =>
      simpa only [smul_add, TensorProduct.add_tmul, add_sub_add_comm, map_add] using
        (BalancedTensor.rel ℤ B A V W).add_mem hx hx'
    | hom q x hx =>
      induction a using SuperBimodule.alg_induction_on 𝒜 with
      | zero => simp
      | add a a' ha ha' =>
        simpa only [MulOpposite.op_add, map_add, add_smul, TensorProduct.add_tmul, TensorProduct.tmul_add,
          add_sub_add_comm] using (BalancedTensor.rel ℤ B A V W).add_mem ha ha'
      | hom p a ha =>
        induction y using induction_on W with
        | add y y' hy hy' =>
          simpa only [smul_add, TensorProduct.tmul_add, add_sub_add_comm, map_add] using
            (BalancedTensor.rel ℤ B A V W).add_mem hy hy'
        | hom r y hy =>
          have hd := relation_mem V W 𝒜 hR hL ha hx hy
          have he := SVec.proj_apply_of_mem_part (p := 1) _ hd
          rw [SVec.proj_one] at he
          rw [he]
          split_ifs
          · exact Submodule.subset_span ⟨x, a, y, rfl⟩
          · exact Submodule.zero_mem _
  have ht' : t ∈ Submodule.span ℤ (BalancedTensor.relSet ℤ A V W) := by
    rw [← BalancedTensor.rel_restrictScalars ℤ B A V W]
    exact ht
  clear ht
  induction ht' using Submodule.span_induction with
  | mem t ht => obtain ⟨x, a, y, rfl⟩ := ht; exact hs x a y
  | zero => simp
  | add s t _ _ hs ht => simpa only [map_add] using (BalancedTensor.rel ℤ B A V W).add_mem hs ht
  | smul c t _ ht =>
    rw [map_zsmul]
    exact Submodule.smul_of_tower_mem _ c ht

/-- The same balancing relation, with its proved parity stability. -/
def balanceGraded : SVec.GradedSubmodule (tensorSpace V W) where
  toSubmodule := (BalancedTensor.rel ℤ B A V W).restrictScalars k
  odd_mem := relation_odd_mem V W 𝒜 hR hL

/-- Total parity descended to the existing balanced tensor carrier. -/
def balancedSpace : SVec k := SVec.quot (tensorSpace V W) (balanceGraded (B := B) V W 𝒜 hR hL)

end Balance
section Corner
variable {A B : Type u} [Ring A] [Ring B] [Algebra k B]
  (ℬ : ZMod 2 → Submodule k B) [GradedAlgebra ℬ]
  (φ : A →ₙ+* B) (he : φ 1 ∈ ℬ 0)

include he in
/-- The corner is stable under every parity projection since its idempotent is even. -/
theorem corner_proj_mem (p : ZMod 2) (x : InductionAlong.Corner φ) :
    SuperBimodule.algProj ℬ p x.val ∈ Categorification.lIdeal (φ 1) := by
  have h := SVec.apply_proj_of_mem ((SuperBimodule.regular ℬ).ract_mem 0 (φ 1) he) p x.val
  change (SuperBimodule.regularSVec ℬ).proj p x.val * φ 1 =
    (SuperBimodule.regularSVec ℬ).proj (p + 0) (x.val * φ 1) at h
  rw [add_zero, SuperBimodule.regularSVec_proj] at h
  change SuperBimodule.algProj ℬ p x.val * φ 1 = SuperBimodule.algProj ℬ p x.val
  rw [h, x.property]

/-- Parity on the original left-ideal subtype, without changing the corner carrier. -/
abbrev cornerSpace : SVec k where
  carrier := InductionAlong.Corner φ
  odd :=
    { toFun x := ⟨SuperBimodule.algProj ℬ 1 x.val, corner_proj_mem ℬ φ he 1 x⟩
      map_add' x y := Subtype.ext (map_add _ _ _)
      map_smul' c x := Subtype.ext (map_smul _ _ _) }
  odd_comp_odd := by
    ext x
    exact SuperBimodule.algProj_of_mem ℬ (SuperBimodule.algProj_mem ℬ 1 x.val)

theorem cornerSpace_proj (p : ZMod 2) (x : InductionAlong.Corner φ) :
    ((cornerSpace ℬ φ he).proj p x).val = SuperBimodule.algProj ℬ p x.val := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · change x.val - SuperBimodule.algProj ℬ 1 x.val = SuperBimodule.algProj ℬ 0 x.val
    exact sub_eq_iff_eq_add.mpr (SuperBimodule.algProj_add_algProj ℬ x.val).symm
  · rfl

theorem cornerSpace_mem {p : ZMod 2} {x : InductionAlong.Corner φ} :
    x ∈ (cornerSpace ℬ φ he).part p ↔ x.val ∈ ℬ p := by
  rw [SVec.mem_part_iff]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [cornerSpace_proj] at h'
    rw [← h']
    exact SuperBimodule.algProj_mem ℬ p x.val
  · intro h
    apply Subtype.ext
    rw [cornerSpace_proj, SuperBimodule.algProj_of_mem ℬ h]
end Corner
section Ind
variable {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (𝒜 : ZMod 2 → Submodule k A) [GradedAlgebra 𝒜]
  (ℬ : ZMod 2 → Submodule k B) [GradedAlgebra ℬ]
  (φ : A →ₙ+* B) (hφ : ∀ p a, a ∈ 𝒜 p → φ a ∈ ℬ p)
  [Module A W]
  (hW : ∀ (p q : ZMod 2) (a : A) (y : W), a ∈ 𝒜 p → y ∈ W.part q →
    a • y ∈ W.part (p + q))

abbrev indSpace : SVec k :=
  balancedSpace (B := B)
    (cornerSpace ℬ φ (hφ 0 1 (SetLike.one_mem_graded 𝒜))) W 𝒜
    (fun p _q a _x ha hx => (cornerSpace_mem ℬ φ _).mpr
      (SetLike.GradedMul.mul_mem ((cornerSpace_mem ℬ φ _).mp hx) (hφ p a ha))) hW

end Ind
end OddMath.QuiverHecke.InducedParity
namespace OddMath.QuiverHecke
universe v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

omit [Fintype I] in
/-- The prepend algebra map preserves affine parity. -/
theorem prependAlgebra_parity (i : I) (n : ℕ) {p : ZMod 2} {x : Hn D Sc n}
    (hx : x ∈ affineParity D Sc n p) :
    prependAlgebra D Sc i n x ∈ affineParity D Sc (n + 1) p := by
  classical
  change prependLinear D Sc i n x ∈ _
  rw [FiniteHomMatrix.eq_sum_single x, map_sum]
  apply Submodule.sum_mem
  intro q _
  rw [prependLinear_single]
  apply FiniteHomMatrix.single_mem_component
  exact MonoidalSupercategory.whiskerLeft_mem ((pres D Sc).obj (ob D [i])) (hx q)

/-- The coefficient action used by source induction respects quotient parity. -/
theorem cyclotomicCoefficient_smul_mem (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (p q : ZMod 2)
    (r : Hn D Sc (n + 1)) (b : CyclotomicAlgebra D Sc a n)
    (hr : r ∈ affineParity D Sc (n + 1) p) (hb : b ∈ cyclotomicParity D Sc a ha n q) :
    r • b ∈ cyclotomicParity D Sc a ha n (p + q) := by
  have h : r • b = cyclotomicMk D Sc a n r * b := by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
    rfl
  rw [h]
  exact SetLike.GradedMul.mul_mem (cyclotomicMk_parity D Sc a ha n hr) hb

/-- The shifted coefficient action respects its shifted grading. -/
theorem qCoefficient_smul_mem (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (p q : ZMod 2)
    (r : Hn D Sc (n + 1)) (b : (qCoefficient D Sc i β a ha n).toSVec)
    (hr : r ∈ affineParity D Sc (n + 1) p)
    (hb : b ∈ (qCoefficient D Sc i β a ha n).toSVec.part q) :
    r • b ∈ (qCoefficient D Sc i β a ha n).toSVec.part (p + q) := by
  have h := SVec.apply_mem_part ((qCoefficient D Sc i β a ha n).lact_mem p
    (cyclotomicMk D Sc a n r) (cyclotomicMk_parity D Sc a ha n hr)) hb
  rw [add_comm q p] at h
  convert h using 1

/-- Total parity on the source induced tensor of Q, on its existing carrier. -/
def qSourceSpace (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) : SVec k :=
  let : Module (Hn D Sc (n + 1)) (cyclotomicSuperspace D Sc a ha n) :=
    inferInstanceAs (Module (Hn D Sc (n + 1)) (CyclotomicAlgebra D Sc a n))
  InducedParity.indSpace (cyclotomicSuperspace D Sc a ha n)
    (affineParity D Sc (n + 1)) (affineParity D Sc (n + 1 + 1))
    (appendAlgebra D Sc i (n + 1)) (fun _ _ h => appendAlgebra_parity D Sc i (n + 1) h)
    (cyclotomicCoefficient_smul_mem D Sc a ha n)

/-- Total parity on the target with the canonical coefficient shift of Q. -/
def qTargetSpace (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) : SVec k :=
  InducedParity.indSpace (qCoefficient D Sc i β a ha n).toSVec
    (affineParity D Sc (n + 1)) (affineParity D Sc (n + 1 + 1))
    (prependAlgebra D Sc i (n + 1)) (fun _ _ h => prependAlgebra_parity D Sc i (n + 1) h)
    (qCoefficient_smul_mem D Sc i β a ha n)

omit [Fintype I] in
theorem positionedDot_parity (l r : List I) (i : I) :
    dotE D Sc (l ++ i :: r) l.length ∈ parity (R := k) _ _ (D.parity i) := by
  rw [dotE_eq]
  apply Presentation.diag_mem_homDeg'
  simp [degree_parity_mkD, pl, PG.ld, Shape.parity]

omit [Fintype I] in
theorem positionedCross_parity (l r : List I) (i j : I) :
    cl D Sc _ _ [.cross l.length] (sChain_crossAt l r i j) ∈
      parity (R := k) _ _ (D.parity i * D.parity j) := by
  apply Presentation.diag_mem_homDeg'
  simp [degree_parity_mkD, pl, PG.ld, Shape.parity]

private theorem end_mul_parity {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {A : C} {p q : ZMod 2} {x y : End A}
    (hx : x ∈ parity (R := k) A A p) (hy : y ∈ parity (R := k) A A q) :
    x * y ∈ parity (R := k) A A (p + q) := by
  simpa only [End.mul_def, add_comm] using Supercategory.comp_mem hy hx

private theorem gEven_parity {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {A : C} {x y t : End A}
    (hx : x ∈ parity (R := k) A A 0) (hy : y ∈ parity (R := k) A A 0)
    (ht : t ∈ parity (R := k) A A 0) :
    SignedNilHecke.gEven x y t ∈ parity (R := k) A A 0 := by
  have hd := Submodule.sub_mem _ hy hx
  have hp : (y - x) * t ∈ parity (R := k) A A 0 := end_mul_parity hd ht
  exact end_mul_parity hd (Submodule.add_mem _ (Supercategory.id_mem A) hp)

private theorem gOdd_parity {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {A : C} {x y t : End A}
    (hx : x ∈ parity (R := k) A A 1) (hy : y ∈ parity (R := k) A A 1)
    (ht : t ∈ parity (R := k) A A 1) :
    OddNilHecke.Intertwiner.element x y t ∈ parity (R := k) A A 1 := by
  have hs : OddNilHecke.Intertwiner.squareDiff x y ∈ parity (R := k) A A 0 := by
    simpa only [OddNilHecke.Intertwiner.squareDiff, pow_two,
      show (1 : ZMod 2) + 1 = 0 by decide] using
      Submodule.sub_mem _ (end_mul_parity hy hy) (end_mul_parity hx hx)
  exact Submodule.sub_mem _ (end_mul_parity hs (Submodule.sub_mem _ hy hx))
    (end_mul_parity (show OddNilHecke.Intertwiner.squareDiff x y ^ 2 ∈ parity (R := k) A A 0 by
      simpa only [pow_two, zero_add] using end_mul_parity hs hs) ht)

omit [Fintype I] in
theorem intertwinerHom_parity (l r : List I) (i j : I) :
    intertwinerHom D Sc l r i j ∈ parity (R := k) _ _ (D.parity i * D.parity j) := by
  classical
  by_cases hij : i = j
  · subst j
    rw [intertwinerHom_self]
    have hx := positionedDot_parity D Sc l (i :: r) i
    have hy : dotE D Sc (l ++ i :: i :: r) (l.length + 1) ∈
        parity (R := k) _ _ (D.parity i) := by
      have e : (l ++ [i]) ++ i :: r = l ++ i :: i :: r := by simp
      have h := positionedDot_parity D Sc (l ++ [i]) r i
      rw [e] at h
      simpa only [List.length_append, List.length_singleton] using h
    have ht := positionedCross_parity D Sc l r i i
    rw [← crossE_eq_cl] at ht
    have e : l ++ [i,i] ++ r = l ++ i :: i :: r := by simp
    rw [e] at ht ⊢
    rcases parity_eq_zero_or_one (D.parity i) with hp | hp
    · simp only [hp, mul_zero] at hx hy ht ⊢
      rw [sameIntertwiner, ite_eq_right (by simpa only [hp] using (zero_ne_one : (0 : ZMod 2) ≠ 1))]
      exact gEven_parity hx hy ht
    · simp only [hp, mul_one] at hx hy ht ⊢
      rw [sameIntertwiner, ite_eq_left hp]
      exact gOdd_parity hx hy ht
  · rw [intertwinerHom_of_ne D Sc l r hij]
    exact positionedCross_parity D Sc l r i j

omit [Fintype I] in
theorem moveHom_parity (i : I) (l ν : List I) :
    moveHom D Sc i l ν ∈ parity (R := k) _ _ (D.parity i * wordSumParity D ν) := by
  have he {A B : (pres D Sc).Presented} (h : A = B) :
      eqToHom h ∈ parity (R := k) A B 0 := by
    subst h
    exact Supercategory.id_mem _
  induction ν generalizing l with
  | nil => simpa only [moveHom, wordSumParity, List.map_nil, List.sum_nil, mul_zero] using he _
  | cons j ν ih =>
    simpa only [moveHom, wordSumParity, List.map_cons, List.sum_cons, mul_add,
      zero_add, add_zero] using Supercategory.comp_mem (he _)
        (Supercategory.comp_mem (intertwinerHom_parity D Sc l ν i j)
          (Supercategory.comp_mem (he _) (Supercategory.comp_mem (ih (l ++ [j])) (he _))))

end OddMath.QuiverHecke

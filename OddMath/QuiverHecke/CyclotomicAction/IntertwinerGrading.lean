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

This module does not yet prove that Q preserves these gradings or establish
full Proposition 8.4, the full right-superalgebra action, or a QP formula.
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
theorem balanced_tmul_mem {p q : ZMod 2} {x : V} {y : W}
    (hx : x ∈ V.part p) (hy : y ∈ W.part q) :
    (BalancedTensor.tmul x y : BalancedTensor ℤ B A V W) ∈
      (balancedSpace (B := B) V W 𝒜 hR hL).part (p + q) :=
  SVec.quotMkFun_mem_part _ _ (tensorSpace_tmul_mem V W hx hy)

/-- Test homogeneity on homogeneous pure tensors of the existing quotient. -/
theorem balanced_map_mem {U : SVec k} {d : ZMod 2}
    (f : balancedSpace (B := B) V W 𝒜 hR hL →ₗ[k] U)
    (hf : ∀ (p q : ZMod 2) (x : V) (y : W), x ∈ V.part p → y ∈ W.part q →
      f (BalancedTensor.tmul x y) ∈ U.part (p + q + d)) :
    SVec.ofHom f ∈ SVec.parityHom (balancedSpace (B := B) V W 𝒜 hR hL) U d := by
  intro s
  apply LinearMap.ext
  intro z
  obtain ⟨t, rfl⟩ := SVec.quotMkFun_surjective (tensorSpace V W)
    (balanceGraded (B := B) V W 𝒜 hR hL) z
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' =>
    change f ((balancedSpace (B := B) V W 𝒜 hR hL).proj s
      (SVec.quotMkFun _ _ (t + t'))) = _
    simpa only [LinearMap.comp_apply, SVec.toLinearMap_ofHom, SVec.quotMkFun_add (tensorSpace V W) (balanceGraded (B := B) V W 𝒜 hR hL), map_add] using congrArg₂ (· + ·) ht ht'
  | tmul x y =>
    induction x using induction_on V with
    | add x x' hx hx' =>
      simpa only [TensorProduct.add_tmul, SVec.quotMkFun_add (tensorSpace V W) (balanceGraded (B := B) V W 𝒜 hR hL), LinearMap.comp_apply,
        SVec.toLinearMap_ofHom, map_add] using congrArg₂ (· + ·) hx hx'
    | hom p x hx =>
      induction y using induction_on W with
      | add y y' hy hy' =>
        simpa only [TensorProduct.tmul_add, SVec.quotMkFun_add (tensorSpace V W) (balanceGraded (B := B) V W 𝒜 hR hL), LinearMap.comp_apply,
          SVec.toLinearMap_ofHom, map_add] using congrArg₂ (· + ·) hy hy'
      | hom q y hy =>
        change f ((balancedSpace (B := B) V W 𝒜 hR hL).proj s
          (BalancedTensor.tmul x y)) = U.proj (s + d) (f (BalancedTensor.tmul x y))
        rw [SVec.proj_apply_of_mem_part _ (balanced_tmul_mem (B := B) V W 𝒜 hR hL hx hy),
          SVec.proj_apply_of_mem_part _ (hf p q x y hx hy)]
        simp only [add_left_inj, apply_ite f, map_zero]
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

theorem ind_tmul_mem {p q : ZMod 2} {x : InductionAlong.Corner φ} {y : W}
    (hx : x.val ∈ ℬ p) (hy : y ∈ W.part q) :
    InductionAlong.Ind.tmul x y ∈ (indSpace W 𝒜 ℬ φ hφ hW).part (p + q) :=
  balanced_tmul_mem (B := B) _ _ _ _ _ ((cornerSpace_mem ℬ φ _).mpr hx) hy
/-- A homogeneous pure-tensor criterion for maps on the original induction quotient. -/
theorem ind_map_mem {U : SVec k} {d : ZMod 2}
    (f : indSpace W 𝒜 ℬ φ hφ hW →ₗ[k] U)
    (hf : ∀ (p q : ZMod 2) (x : InductionAlong.Corner φ) (y : W),
      x.val ∈ ℬ p → y ∈ W.part q → f (InductionAlong.Ind.tmul x y) ∈ U.part (p + q + d)) :
    SVec.ofHom f ∈ SVec.parityHom (indSpace W 𝒜 ℬ φ hφ hW) U d :=
  balanced_map_mem (B := B) _ _ _ _ _ f
    (fun p q x y hx hy => hf p q x y ((cornerSpace_mem ℬ φ _).mp hx) hy)

/-- The induced left action has the degree of its homogeneous algebra element. -/
theorem ind_smul_mem {d q : ZMod 2} {b : B} {z : InductionAlong.Ind W φ}
    (hb : b ∈ ℬ d) (hz : z ∈ (indSpace W 𝒜 ℬ φ hφ hW).part q) :
    b • z ∈ (indSpace W 𝒜 ℬ φ hφ hW).part (d + q) := by
  let : Module B (indSpace W 𝒜 ℬ φ hφ hW) := inferInstanceAs (Module B (InductionAlong.Ind W φ))
  let : IsScalarTower k B (indSpace W 𝒜 ℬ φ hφ hW) :=
    inferInstanceAs (IsScalarTower k B ((InductionAlong.Corner φ ⊗[ℤ] W) ⧸
      (BalancedTensor.rel ℤ B A (InductionAlong.Corner φ) W)))
  let f : indSpace W 𝒜 ℬ φ hφ hW →ₗ[k] indSpace W 𝒜 ℬ φ hφ hW :=
    { toFun := fun z => b • (show InductionAlong.Ind W φ from z)
      map_add' := smul_add b
      map_smul' := fun c z => smul_comm b c z }
  have hf : SVec.ofHom f ∈ SVec.parityHom _ _ d := by
    apply ind_map_mem W 𝒜 ℬ φ hφ hW f
    intro p r x y hx hy
    change b • InductionAlong.Ind.tmul x y ∈ _
    rw [InductionAlong.Ind.smul_tmul]
    have h := ind_tmul_mem W 𝒜 ℬ φ hφ hW (x := b • x) (SetLike.GradedMul.mul_mem hb hx) hy
    convert h using 1; abel_nf
  have h := SVec.apply_mem_part hf hz
  rw [add_comm q d] at h
  exact h
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
/-- Source tensor degrees add the affine corner and cyclotomic coefficient parities. -/
theorem qSourceSpace_tmul_mem (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) {p q : ZMod 2}
    {x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))}
    {b : CyclotomicAlgebra D Sc a n} (hx : x.val ∈ affineParity D Sc (n + 1 + 1) p)
    (hb : b ∈ cyclotomicParity D Sc a ha n q) :
    InductionAlong.Ind.tmul x b ∈ (qSourceSpace D Sc i a ha n).part (p + q) :=
  by
    let : Module (Hn D Sc (n + 1)) (cyclotomicSuperspace D Sc a ha n) :=
      inferInstanceAs (Module (Hn D Sc (n + 1)) (CyclotomicAlgebra D Sc a n))
    exact InducedParity.ind_tmul_mem _ _ _ _
      (fun _ _ h => appendAlgebra_parity D Sc i (n + 1) h)
      (cyclotomicCoefficient_smul_mem D Sc a ha n) hx hb

/-- Target tensor degrees use the canonical shifted coefficient, not the unshifted one. -/
theorem qTargetSpace_tmul_mem (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) {p q : ZMod 2}
    {x : InductionAlong.Corner (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))}
    {b : (qCoefficient D Sc i β a ha n).toSVec}
    (hx : x.val ∈ affineParity D Sc (n + 1 + 1) p)
    (hb : b ∈ (qCoefficient D Sc i β a ha n).toSVec.part q) :
    InductionAlong.Ind.tmul x b ∈ (qTargetSpace D Sc i β a ha n).part (p + q) :=
  InducedParity.ind_tmul_mem _ _ _ _
    (fun _ _ h => prependAlgebra_parity D Sc i (n + 1) h)
    (qCoefficient_smul_mem D Sc i β a ha n) hx hb
/-- The actual source induced action is graded, with no action-grading hypothesis. -/
theorem qSourceSpace_smul_mem (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) {p q : ZMod 2}
    {r : Hn D Sc (n + 1 + 1)}
    {z : InductionAlong.Ind (CyclotomicAlgebra D Sc a n)
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))}
    (hr : r ∈ affineParity D Sc (n + 1 + 1) p)
    (hz : z ∈ (qSourceSpace D Sc i a ha n).part q) :
    r • z ∈ (qSourceSpace D Sc i a ha n).part (p + q) := by
  let : Module (Hn D Sc (n + 1)) (cyclotomicSuperspace D Sc a ha n) :=
    inferInstanceAs (Module (Hn D Sc (n + 1)) (CyclotomicAlgebra D Sc a n))
  exact InducedParity.ind_smul_mem _ _ _ _
    (fun _ _ h => appendAlgebra_parity D Sc i (n + 1) h)
    (cyclotomicCoefficient_smul_mem D Sc a ha n) hr hz

/-- The shifted target induced action is graded, with no action-grading hypothesis. -/
theorem qTargetSpace_smul_mem (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) {p q : ZMod 2}
    {r : Hn D Sc (n + 1 + 1)}
    {z : InductionAlong.Ind (qCoefficient D Sc i β a ha n).toSVec
      (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))}
    (hr : r ∈ affineParity D Sc (n + 1 + 1) p)
    (hz : z ∈ (qTargetSpace D Sc i β a ha n).part q) :
    r • z ∈ (qTargetSpace D Sc i β a ha n).part (p + q) :=
  InducedParity.ind_smul_mem _ _ _ _
    (fun _ _ h => prependAlgebra_parity D Sc i (n + 1) h)
    (qCoefficient_smul_mem D Sc i β a ha n) hr hz
end OddMath.QuiverHecke

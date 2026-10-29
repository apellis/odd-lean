/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendLeftCrossing

/-!
# The two-sided append corner decomposition on induced modules

For a left `Hn (n+1)`-module `M`, the decomposition `appendCornerEquiv` of the two-sided
append corner `ψ(1) Hn (n+2) ψ(1)` descends along the balanced tensor product
`Ind M = Hn (n+2) ψ(1) ⊗_(Hn (n+1)) M`: the `ψ(1)`-fixed part of `Ind M` is

`⊕_(j ≤ n, m) ψ'(1) M  ⊕  ⊕_m M`,

with `(j, m, y) ↦ ψ(c'_j x^m) τ ⊗ y` and `(m, y) ↦ z^m ⊗ y`. Both round trips use only
`appendCornerEquiv` and the right `ψ(Hn (n+1))`-linearity of its summand maps, not
flatness of `M`. This is the module form of the append-side Mackey decomposition of
`AppendCoordinates.md` §4 (Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Lemma 8.1,
mirror form).
-/

noncomputable section
open Categorification MulOpposite
namespace OddMath.QuiverHecke
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (n : ℕ) (M : Type w) [AddCommGroup M] [Module (Hn D Sc (n + 1)) M]
local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
local notation "C" => InductionAlong.Corner ψ
local notation "T" => InductionAlong.Ind M ψ

/-! ## Finite sums of elementary tensors along an additive family of corner elements -/

section Family
variable {ι : Type*} (Φ : (ι →₀ Hn D Sc (n + 1)) →+ Hn D Sc (n + 1 + 1))
  (hΦ : ∀ x, Φ x * appendAlgebra D Sc i (n + 1) 1 = Φ x)

/-- The family `Φ` with values in the right corner. -/
def appendFamilyCorner : (ι →₀ Hn D Sc (n + 1)) →+ C :=
  AddMonoidHom.codRestrict Φ _ hΦ

/-- `Σ_q Φ(single q 1) ⊗ y_q`. -/
def appendFamilyTensor : (ι →₀ M) →+ T :=
  Finsupp.liftAddHom fun q =>
    { toFun := fun y => InductionAlong.Ind.tmul
        (appendFamilyCorner D Sc i n Φ hΦ (Finsupp.single q 1)) y
      map_zero' := InductionAlong.Ind.tmul_zero _
      map_add' := InductionAlong.Ind.tmul_add _ }

@[simp] theorem appendFamilyTensor_single (q : ι) (y : M) :
    appendFamilyTensor D Sc i n M Φ hΦ (Finsupp.single q y) =
      InductionAlong.Ind.tmul (appendFamilyCorner D Sc i n Φ hΦ (Finsupp.single q 1)) y :=
  Finsupp.liftAddHom_apply_single _ _ _

/-- Old-algebra coefficients move across the tensor sign. -/
theorem appendFamilyTensor_coefficients
    (hr : ∀ q c,
      Φ (Finsupp.single q c) = Φ (Finsupp.single q 1) * appendAlgebra D Sc i (n + 1) c)
    (b : ι →₀ Hn D Sc (n + 1)) (y : M) :
    appendFamilyTensor D Sc i n M Φ hΦ
        (Finsupp.mapRange (fun c : Hn D Sc (n + 1) => c • y) (zero_smul _ y) b) =
      InductionAlong.Ind.tmul (appendFamilyCorner D Sc i n Φ hΦ b) y := by
  induction b using Finsupp.induction with
  | zero => simp [InductionAlong.Ind.zero_tmul]
  | @single_add q c b _ _ hb =>
    rw [Finsupp.mapRange_add (fun a b => add_smul a b y), map_add,
      map_add, InductionAlong.Ind.add_tmul, hb]
    congr 1
    rw [Finsupp.mapRange_single, appendFamilyTensor_single,
      ← InductionAlong.Ind.op_smul_tmul]
    congr 1
    apply Subtype.ext
    change Φ (Finsupp.single q 1) * appendAlgebra D Sc i (n + 1) c = Φ (Finsupp.single q c)
    exact (hr q c).symm

/-- A family fixed by `ψ(1)` on the left gives `ψ(1)`-fixed tensors. -/
theorem appendFamilyTensor_fixed (hl : ∀ x, appendAlgebra D Sc i (n + 1) 1 * Φ x = Φ x)
    (x : ι →₀ M) :
    (appendAlgebra D Sc i (n + 1) 1 : Hn D Sc (n + 1 + 1)) •
        appendFamilyTensor D Sc i n M Φ hΦ x =
      appendFamilyTensor D Sc i n M Φ hΦ x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, smul_add, hf, hg]
  | single q y =>
    rw [appendFamilyTensor_single, InductionAlong.Ind.smul_tmul]
    congr 1
    exact Subtype.ext (hl _)

end Family

/-! ## The two summand families -/

theorem appendLeftSum_mul_appendOne
    (F : (Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) :
    appendLeftSum D Sc i n F * appendAlgebra D Sc i (n + 1) 1 = appendLeftSum D Sc i n F :=
  (appendLeftSum_mem_appendTwoSidedCorner D Sc i n F).2

theorem appendPolySum_mul_appendOne (G : ℕ →₀ Hn D Sc (n + 1)) :
    appendPolySum D Sc i n G * appendAlgebra D Sc i (n + 1) 1 = appendPolySum D Sc i n G :=
  (appendPolySum_mem_appendTwoSidedCorner D Sc i n G).2

theorem appendLeftSum_single_right (q : Fin (n + 1) × ℕ) (c : Hn D Sc (n + 1)) :
    appendLeftSum D Sc i n (Finsupp.single q c) =
      appendLeftSum D Sc i n (Finsupp.single q 1) * appendAlgebra D Sc i (n + 1) c := by
  obtain ⟨j, m⟩ := q
  rw [appendLeftSum_single, appendLeftSum_single,
    mul_assoc (_ * _) (appendAlgebra D Sc i (n + 1) 1),
    ← map_mul, one_mul]

theorem appendPolySum_single_right (m : ℕ) (c : Hn D Sc (n + 1)) :
    appendPolySum D Sc i n (Finsupp.single m c) =
      appendPolySum D Sc i n (Finsupp.single m 1) * appendAlgebra D Sc i (n + 1) c := by
  rw [appendPolySum_single, appendPolySum_single,
    mul_assoc (_ ^ _) (appendAlgebra D Sc i (n + 1) 1),
    ← map_mul, one_mul]

/-- The left-crossing tensors `Σ ψ(c'_j x^m) τ ⊗ y_(j,m)`. -/
abbrev appendLeftTensor : ((Fin (n + 1) × ℕ) →₀ M) →+ T :=
  appendFamilyTensor D Sc i n M (appendLeftSum D Sc i n) (appendLeftSum_mul_appendOne D Sc i n)

/-- The polynomial tensors `Σ z^m ⊗ y_m`. -/
abbrev appendPolyTensor : (ℕ →₀ M) →+ T :=
  appendFamilyTensor D Sc i n M (appendPolySum D Sc i n) (appendPolySum_mul_appendOne D Sc i n)

/-- Left-crossing coefficients in `ψ'(1) M`. -/
def appendTensorLeftCoordinates : AddSubgroup ((Fin (n + 1) × ℕ) →₀ M) where
  carrier := {f | ∀ q, (appendAlgebra D Sc i n 1 : Hn D Sc (n + 1)) • f q = f q}
  add_mem' {f g} hf hg q := by rw [Finsupp.add_apply, smul_add, hf, hg]
  zero_mem' q := by simp
  neg_mem' {f} hf q := by rw [Finsupp.neg_apply, smul_neg, hf]

/-- The `ψ(1)`-fixed part of the induced module. -/
def appendTensorFixed : AddSubgroup T where
  carrier := {t | (appendAlgebra D Sc i (n + 1) 1 : Hn D Sc (n + 1 + 1)) • t = t}
  add_mem' {s t} hs ht := by
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_add, hs, ht]
  zero_mem' := by simp
  neg_mem' {t} ht := by
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_neg, ht]

/-! ## Coordinates of a corner element -/

theorem appendOne_mul_corner_mem (z : C) :
    appendAlgebra D Sc i (n + 1) 1 * z.1 ∈ appendTwoSidedCorner D Sc i n :=
  ⟨by rw [← mul_assoc, ← map_mul, one_mul],
    by rw [mul_assoc]; exact congrArg _ z.2⟩

/-- The coordinates `(F, G)` of `ψ(1) z` in `appendCornerEquiv`. -/
def appendCornerCoords : C →+ appendLeftCoordinates D Sc i n × (ℕ →₀ Hn D Sc (n + 1)) :=
  (appendCornerEquiv D Sc i n).symm.toAddMonoidHom.comp
    { toFun := fun z =>
        ⟨appendAlgebra D Sc i (n + 1) 1 * z.1, appendOne_mul_corner_mem D Sc i n z⟩
      map_zero' := Subtype.ext (mul_zero _)
      map_add' := fun z z' => Subtype.ext (mul_add _ z.1 z'.1) }

theorem appendCornerCoords_spec (z : C) :
    appendLeftSum D Sc i n (appendCornerCoords D Sc i n z).1 +
      appendPolySum D Sc i n (appendCornerCoords D Sc i n z).2 =
        appendAlgebra D Sc i (n + 1) 1 * z.1 := by
  rw [← appendCornerEquiv_apply]
  exact congrArg Subtype.val ((appendCornerEquiv D Sc i n).apply_symm_apply _)

theorem appendCornerCoords_op_smul (z : C) (a : Hn D Sc (n + 1)) :
    appendCornerCoords D Sc i n (op a • z) =
      (⟨Finsupp.mapRange.addMonoidHom (AddMonoidHom.mulRight a)
          (appendCornerCoords D Sc i n z).1.1, fun q => by
          simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply,
            AddMonoidHom.coe_mulRight, ← mul_assoc, (appendCornerCoords D Sc i n z).1.2 q]⟩,
        Finsupp.mapRange.addMonoidHom (AddMonoidHom.mulRight a)
          (appendCornerCoords D Sc i n z).2) := by
  change (appendCornerEquiv D Sc i n).symm _ = _
  rw [AddEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [appendCornerEquiv_apply]
  change appendAlgebra D Sc i (n + 1) 1 * (z.1 * appendAlgebra D Sc i (n + 1) a) = _
  rw [appendLeftSum_mul_appendAlgebra, appendPolySum_mul_appendAlgebra, ← add_mul,
    appendCornerCoords_spec, mul_assoc]

theorem appendCornerCoords_leftSum (q : Fin (n + 1) × ℕ) :
    appendCornerCoords D Sc i n
        (appendFamilyCorner D Sc i n (appendLeftSum D Sc i n)
          (appendLeftSum_mul_appendOne D Sc i n) (Finsupp.single q 1)) =
      (⟨Finsupp.single q (appendAlgebra D Sc i n 1), fun p => by
          by_cases h : q = p
          · subst h; simp [← map_mul]
          · simp [Finsupp.single_eq_of_ne' h]⟩, 0) := by
  change (appendCornerEquiv D Sc i n).symm _ = _
  rw [AddEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [appendCornerEquiv_apply]
  change appendAlgebra D Sc i (n + 1) 1 * appendLeftSum D Sc i n (Finsupp.single q 1) = _
  rw [(appendLeftSum_mem_appendTwoSidedCorner D Sc i n _).1, map_zero, add_zero,
    ← appendLeftSum_appendLeftProj]
  simp only [appendLeftProj, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
    AddMonoidHom.coe_mulLeft, mul_one]

theorem appendCornerCoords_polySum (m : ℕ) :
    appendCornerCoords D Sc i n
        (appendFamilyCorner D Sc i n (appendPolySum D Sc i n)
          (appendPolySum_mul_appendOne D Sc i n) (Finsupp.single m 1)) =
      (0, Finsupp.single m 1) := by
  change (appendCornerEquiv D Sc i n).symm _ = _
  rw [AddEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [appendCornerEquiv_apply]
  change appendAlgebra D Sc i (n + 1) 1 * appendPolySum D Sc i n (Finsupp.single m 1) = _
  rw [(appendPolySum_mem_appendTwoSidedCorner D Sc i n _).1]
  simp

/-! ## The descent -/

/-- Coordinate extraction on the induced module, `z ⊗ y ↦ (F(ψ(1) z) y, G(ψ(1) z) y)`. -/
def appendTensorCornerBackward : T →+ ((Fin (n + 1) × ℕ) →₀ M) × (ℕ →₀ M) :=
  InductionAlong.Ind.liftAdd
    (fun z y =>
      (Finsupp.mapRange (fun b : Hn D Sc (n + 1) => b • y) (zero_smul _ y)
          (appendCornerCoords D Sc i n z).1.1,
        Finsupp.mapRange (fun b : Hn D Sc (n + 1) => b • y) (zero_smul _ y)
          (appendCornerCoords D Sc i n z).2))
    (by intros; ext q <;> simp [add_smul])
    (by intros; ext q <;> simp [smul_add])
    (by
      intro z a y
      rw [appendCornerCoords_op_smul]
      ext q <;> simp [mul_smul])

@[simp] theorem appendTensorCornerBackward_tmul (z : C) (y : M) :
    appendTensorCornerBackward D Sc i n M (InductionAlong.Ind.tmul z y) =
      (Finsupp.mapRange (fun b : Hn D Sc (n + 1) => b • y) (zero_smul _ y)
          (appendCornerCoords D Sc i n z).1.1,
        Finsupp.mapRange (fun b : Hn D Sc (n + 1) => b • y) (zero_smul _ y)
          (appendCornerCoords D Sc i n z).2) := rfl

theorem appendTensorCornerBackward_mem (t : T) :
    (appendTensorCornerBackward D Sc i n M t).1 ∈ appendTensorLeftCoordinates D Sc i n M := by
  induction t using InductionAlong.Ind.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add s t hs ht => rw [map_add]; exact add_mem hs ht
  | tmul z y =>
    intro q
    rw [appendTensorCornerBackward_tmul, Finsupp.mapRange_apply, ← mul_smul,
      (appendCornerCoords D Sc i n z).1.2 q]

/-- The forward sum `(f, g) ↦ Σ ψ(c'_j x^m) τ ⊗ f_(j,m) + Σ z^m ⊗ g_m`. -/
def appendTensorCornerForward : ((Fin (n + 1) × ℕ) →₀ M) × (ℕ →₀ M) →+ T :=
  (appendLeftTensor D Sc i n M).coprod (appendPolyTensor D Sc i n M)

theorem appendTensorCornerForward_backward (t : T) :
    appendTensorCornerForward D Sc i n M (appendTensorCornerBackward D Sc i n M t) =
      (appendAlgebra D Sc i (n + 1) 1 : Hn D Sc (n + 1 + 1)) • t := by
  induction t using InductionAlong.Ind.induction_on with
  | zero => simp
  | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add]
  | tmul z y =>
    rw [appendTensorCornerBackward_tmul, appendTensorCornerForward, AddMonoidHom.coprod_apply,
      appendFamilyTensor_coefficients _ _ _ _ _ _ _ (appendLeftSum_single_right D Sc i n),
      appendFamilyTensor_coefficients _ _ _ _ _ _ _ (appendPolySum_single_right D Sc i n),
      ← InductionAlong.Ind.add_tmul, InductionAlong.Ind.smul_tmul]
    congr 1
    apply Subtype.ext
    exact appendCornerCoords_spec D Sc i n z

theorem appendTensorCornerBackward_leftTensor (f : (Fin (n + 1) × ℕ) →₀ M) :
    appendTensorCornerBackward D Sc i n M (appendLeftTensor D Sc i n M f) =
      (Finsupp.mapRange (fun y : M => (appendAlgebra D Sc i n 1 : Hn D Sc (n + 1)) • y)
        (smul_zero _) f, 0) := by
  induction f using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, Finsupp.mapRange_zero]; rfl
  | add f g hf hg =>
    rw [map_add, map_add, hf, hg, Finsupp.mapRange_add (fun a b => smul_add _ a b),
      Prod.mk_add_mk, add_zero]
  | single q y =>
    rw [appendFamilyTensor_single, appendTensorCornerBackward_tmul, appendCornerCoords_leftSum]
    simp

theorem appendTensorCornerBackward_polyTensor (g : ℕ →₀ M) :
    appendTensorCornerBackward D Sc i n M (appendPolyTensor D Sc i n M g) = (0, g) := by
  induction g using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]; rfl
  | add f g hf hg => rw [map_add, map_add, hf, hg, Prod.mk_add_mk, add_zero]
  | single m y =>
    rw [appendFamilyTensor_single, appendTensorCornerBackward_tmul, appendCornerCoords_polySum]
    simp

theorem appendTensorCornerForward_mem
    (x : ((Fin (n + 1) × ℕ) →₀ M) × (ℕ →₀ M)) :
    appendTensorCornerForward D Sc i n M x ∈ appendTensorFixed D Sc i n M := by
  change (appendAlgebra D Sc i (n + 1) 1 : Hn D Sc (n + 1 + 1)) •
    (appendLeftTensor D Sc i n M x.1 + appendPolyTensor D Sc i n M x.2) = _
  rw [smul_add,
    appendFamilyTensor_fixed _ _ _ _ _ _ _
      (fun F => (appendLeftSum_mem_appendTwoSidedCorner D Sc i n F).1),
    appendFamilyTensor_fixed _ _ _ _ _ _ _
      (fun G => (appendPolySum_mem_appendTwoSidedCorner D Sc i n G).1)]
  rfl

/-- **Append-side Mackey decomposition of induced modules** (`AppendCoordinates.md` §4):
`ψ(1) (Hn (n+2) ψ(1) ⊗_(Hn (n+1)) M) ≅ ⊕_(j ≤ n, m) ψ'(1) M ⊕ ⊕_m M`, via
`(f, g) ↦ Σ ψ(c'_j x^m) τ ⊗ f_(j,m) + Σ z^m ⊗ g_m`. -/
def appendTensorCornerEquiv :
    appendTensorLeftCoordinates D Sc i n M × (ℕ →₀ M) ≃+ appendTensorFixed D Sc i n M where
  toFun x := ⟨appendTensorCornerForward D Sc i n M (x.1.1, x.2),
    appendTensorCornerForward_mem D Sc i n M _⟩
  invFun t := (⟨(appendTensorCornerBackward D Sc i n M t.1).1,
    appendTensorCornerBackward_mem D Sc i n M t.1⟩, (appendTensorCornerBackward D Sc i n M t.1).2)
  left_inv := by
    rintro ⟨⟨f, hf⟩, g⟩
    have h : appendTensorCornerBackward D Sc i n M
        (appendTensorCornerForward D Sc i n M (f, g)) = (f, g) := by
      rw [appendTensorCornerForward, AddMonoidHom.coprod_apply, map_add,
        appendTensorCornerBackward_leftTensor, appendTensorCornerBackward_polyTensor,
        Prod.mk_add_mk, zero_add, add_zero]
      congr 1
      ext q
      rw [Finsupp.mapRange_apply]
      exact hf q
    simp only [h]
  right_inv := by
    rintro ⟨t, ht⟩
    apply Subtype.ext
    change appendTensorCornerForward D Sc i n M (appendTensorCornerBackward D Sc i n M t) = t
    rw [appendTensorCornerForward_backward]
    exact ht
  map_add' x y := Subtype.ext (map_add (appendTensorCornerForward D Sc i n M) (x.1.1, x.2)
    (y.1.1, y.2))

theorem appendTensorCornerEquiv_apply
    (x : appendTensorLeftCoordinates D Sc i n M × (ℕ →₀ M)) :
    (appendTensorCornerEquiv D Sc i n M x : T) =
      appendLeftTensor D Sc i n M x.1 + appendPolyTensor D Sc i n M x.2 := rfl

end OddMath.QuiverHecke

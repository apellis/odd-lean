import OddMath.Frontier.OddLRMisc
import OddMath.Frontier.EKAntipodeControls

/-!
# `OΛ` is neither commutative nor cocommutative; `S ≠ ψ₁ψ₂R`

Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1 ("E"), §2.1, p. 5, on
`OΛ = EKRadicalQuotient.Q` with the coproduct `EKCoideal.quotientCoproduct`.

* "As a Hopf superalgebra, `OΛ` is neither commutative nor cocommutative." The `ℤ/2`-degree of an
  element of `EKIntegralBases.degreePiece d` is `d mod 2` (`deg h_k = (2k, k)`).
  - `superFlip` is the super flip `x ⊗ y ↦ (-1)^{|x||y|} y ⊗ x` on `OΛ ⊗ OΛ`
    (`superFlip_tmul` on homogeneous elements).
  - Not supercocommutative: `τΔ(h₂) ≠ Δ(h₂)`, since `Δ(h₂) = 1 ⊗ h₂ + h₁ ⊗ h₁ + h₂ ⊗ 1`
    and `τ(h₁ ⊗ h₁) = -h₁ ⊗ h₁` (`superFlip_coproduct_h_two`, `not_superCocommutative`).
  - Not cocommutative for the ordinary flip either: `Δ(h₂h₁)` contains `h₁ ⊗ h₁h₁ - h₁h₁ ⊗ h₁`
    (`comm_coproduct_h21`, `not_cocommutative`).
  - Not supercommutative: `h₁h₂ ≠ (-1)^{1·2} h₂h₁` (`not_superCommutative`).
* §2.1, p. 5, "the antipode is `S = ψ₁ψ₂ψ₃`": with `ψ₃` read as the ordinary anti-involution
  `R = EKAutomorphisms.reverseLinear`, this fails: `ψ₁ψ₂R(h₁²) = h₁²` (`psi12_reverse_square`)
  while `S(h₁²) = -h₁²` (`EKAntipode.S_square_word`), so `S ≠ ψ₁ψ₂R`
  (`antipode_ne_psi12_reverse`). Here `ψ₁ψ₂ = EKAutomorphisms.psi12` and `S = EKAntipode.S`
  (`= ψ₁ψ₂ψ₃` for EK's super anti-involution `ψ₃`).
-/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators TensorProduct

namespace OddMath.Frontier.OddLRGaps

open EKRadicalQuotient (Q)
open EKElementaryQuotient (h e)
open EKCoideal (quotientCoproduct)
open EKIntegralBases (hBasis degreePiece)
open OddLRMisc (leftCoord leftCoord_tmul shape1 hBasis_shape1 coord1_of_degree h_mem_degree
  hq_zero)

/-! ## The super flip -/

/-- The super flip `τ(x ⊗ y) = (-1)^{|x||y|} y ⊗ x` on `OΛ ⊗ OΛ`, defined on the basis
`h_μ ⊗ h_ν` (`|h_μ| = |μ| mod 2`). -/
def superFlip : Q ⊗[ℤ] Q →ₗ[ℤ] Q ⊗[ℤ] Q :=
  (hBasis.tensorProduct hBasis).constr ℤ
    (fun p => (-1 : ℤ) ^ (p.1.card * p.2.card) • (hBasis p.2 ⊗ₜ[ℤ] hBasis p.1))

theorem superFlip_basis (μ ν : YoungDiagram) :
    superFlip (hBasis μ ⊗ₜ[ℤ] hBasis ν) = (-1 : ℤ) ^ (μ.card * ν.card) • (hBasis ν ⊗ₜ[ℤ] hBasis μ) := by
  rw [← Basis.tensorProduct_apply, superFlip, Basis.constr_basis]

theorem word_eq_hBasis {d : ℕ} (μ : DegreeShapes.DegreeShape d) :
    EKPartitionSpanning.word false μ.val.rowLens = hBasis μ.val := by
  rw [EKIntegralBases.hBasis_apply]
  rfl

/-- The super flip on homogeneous elements: `τ(x ⊗ y) = (-1)^{ab} y ⊗ x` for `x, y` of degrees
`a, b`. -/
theorem superFlip_tmul {a b : ℕ} {x y : Q} (hx : x ∈ degreePiece a) (hy : y ∈ degreePiece b) :
    superFlip (x ⊗ₜ[ℤ] y) = (-1 : ℤ) ^ (a * b) • (y ⊗ₜ[ℤ] x) := by
  rw [EKIntegralBases.degreePiece_eq_hPartition_span] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨ν, rfl⟩ := hy
      dsimp only
      rw [word_eq_hBasis, word_eq_hBasis, superFlip_basis, μ.property, ν.property]
    | zero => simp
    | add y z _ _ hy hz =>
      rw [TensorProduct.tmul_add, map_add, hy, hz, TensorProduct.add_tmul, smul_add]
    | smul r y _ hy =>
      rw [TensorProduct.tmul_smul, map_smul, hy, ← TensorProduct.smul_tmul', smul_comm]
  | zero => simp
  | add x z _ _ hx hz =>
    rw [TensorProduct.add_tmul, map_add, hx, hz, TensorProduct.tmul_add, smul_add]
  | smul r x _ hx =>
    rw [← TensorProduct.smul_tmul', map_smul, hx, TensorProduct.tmul_smul, smul_comm]

/-! ## Coordinates -/

theorem coord_one : hBasis.repr (1 : Q) shape1 = 0 :=
  coord1_of_degree EKIntegralBases.unit_mem_degree_zero (by norm_num)

theorem coord_h1 : hBasis.repr (h 1) shape1 = 1 := by
  rw [← hBasis_shape1, Basis.repr_self, Finsupp.single_eq_same]

theorem coord_h2 : hBasis.repr (h 2) shape1 = 0 :=
  coord1_of_degree (h_mem_degree 2) (by norm_num)

theorem coord_h11 : hBasis.repr (h 1 * h 1) shape1 = 0 :=
  coord1_of_degree (EKIntegralBases.degreePiece_mul (h_mem_degree 1) (h_mem_degree 1))
    (by norm_num)

theorem coord_h21 : hBasis.repr (h 2 * h 1) shape1 = 0 :=
  coord1_of_degree (EKIntegralBases.degreePiece_mul (h_mem_degree 2) (h_mem_degree 1))
    (by norm_num)

theorem coproduct_h_two :
    quotientCoproduct (h 2) = (1 : Q) ⊗ₜ[ℤ] h 2 + h 1 ⊗ₜ[ℤ] h 1 + h 2 ⊗ₜ[ℤ] (1 : Q) := by
  rw [EKAutomorphisms.coproduct_h]
  simp [Fin.sum_univ_succ, hq_zero, add_assoc]

/-! ## Not cocommutative -/

/-- `τΔ(h₂) = 1 ⊗ h₂ - h₁ ⊗ h₁ + h₂ ⊗ 1`. -/
theorem superFlip_coproduct_h_two :
    superFlip (quotientCoproduct (h 2)) = h 2 ⊗ₜ[ℤ] (1 : Q) - h 1 ⊗ₜ[ℤ] h 1 + (1 : Q) ⊗ₜ[ℤ] h 2 := by
  rw [coproduct_h_two, map_add, map_add,
    superFlip_tmul EKIntegralBases.unit_mem_degree_zero (h_mem_degree 2),
    superFlip_tmul (h_mem_degree 1) (h_mem_degree 1),
    superFlip_tmul (h_mem_degree 2) EKIntegralBases.unit_mem_degree_zero]
  simp only [zero_mul, mul_zero, mul_one, pow_zero, pow_one, one_smul, neg_one_smul]
  abel

/-- E §2.1, p. 5: `τΔ(h₂) ≠ Δ(h₂)` for the super flip `τ`. -/
theorem superFlip_coproduct_h_two_ne :
    superFlip (quotientCoproduct (h 2)) ≠ quotientCoproduct (h 2) := by
  intro hc
  rw [superFlip_coproduct_h_two, coproduct_h_two] at hc
  have hm := congrArg (fun z => hBasis.repr (leftCoord z) shape1) hc
  simp only [map_add, map_sub, leftCoord_tmul,
    map_zsmul, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, coord_one, coord_h1,
    coord_h2, smul_eq_mul] at hm
  norm_num at hm

/-- E §2.1, p. 5: the Hopf superalgebra `OΛ` is not (super)cocommutative. -/
theorem not_superCocommutative :
    ¬ ∀ x : Q, superFlip (quotientCoproduct x) = quotientCoproduct x :=
  fun h' => superFlip_coproduct_h_two_ne (h' _)

/-- `Δ(h₂h₁)` under the ordinary flip. -/
theorem comm_coproduct_h21 :
    TensorProduct.comm ℤ Q Q (quotientCoproduct (h 2 * h 1)) =
      (h 2 * h 1) ⊗ₜ[ℤ] (1 : Q) + h 2 ⊗ₜ[ℤ] h 1 + (h 1 * h 1) ⊗ₜ[ℤ] h 1 -
        h 1 ⊗ₜ[ℤ] (h 1 * h 1) + h 1 ⊗ₜ[ℤ] h 2 + (1 : Q) ⊗ₜ[ℤ] (h 2 * h 1) := by
  rw [EKAntipodeControls.coproduct_mixed]
  simp only [map_add, map_sub, TensorProduct.comm_tmul]

/-- `Δ(h₂h₁)` is not fixed by the ordinary flip. -/
theorem comm_coproduct_h21_ne :
    TensorProduct.comm ℤ Q Q (quotientCoproduct (h 2 * h 1)) ≠ quotientCoproduct (h 2 * h 1) := by
  intro hc
  have hm := congrArg leftCoord hc
  rw [comm_coproduct_h21, EKAntipodeControls.coproduct_mixed] at hm
  simp only [map_add, map_sub, leftCoord_tmul, coord_one, coord_h1, coord_h2, coord_h11,
    coord_h21, zero_smul, one_smul, zero_add, add_zero, zero_sub, sub_zero] at hm
  have : -(h 1 * h 1) = h 1 * h 1 := by
    have h2 : h 2 + -(h 1 * h 1) = h 2 + h 1 * h 1 := by
      rw [← hm]; abel
    exact add_left_cancel h2
  exact EKAutomorphismsControls.super_square_not_ordinary this

/-- `OΛ` is not cocommutative for the ordinary flip either. -/
theorem not_cocommutative :
    ¬ ∀ x : Q, TensorProduct.comm ℤ Q Q (quotientCoproduct x) = quotientCoproduct x :=
  fun h' => comm_coproduct_h21_ne (h' _)

/-- `Δ(h₂h₁)` is not fixed by the super flip. -/
theorem superFlip_coproduct_h21_ne :
    superFlip (quotientCoproduct (h 2 * h 1)) ≠ quotientCoproduct (h 2 * h 1) := by
  have h21 := EKIntegralBases.degreePiece_mul (h_mem_degree 2) (h_mem_degree 1)
  have h11 := EKIntegralBases.degreePiece_mul (h_mem_degree 1) (h_mem_degree 1)
  have hflip : superFlip (quotientCoproduct (h 2 * h 1)) =
      TensorProduct.comm ℤ Q Q (quotientCoproduct (h 2 * h 1)) := by
    rw [comm_coproduct_h21, EKAntipodeControls.coproduct_mixed]
    simp only [map_add, map_sub]
    rw [superFlip_tmul EKIntegralBases.unit_mem_degree_zero h21,
      superFlip_tmul (h_mem_degree 1) (h_mem_degree 2), superFlip_tmul (h_mem_degree 1) h11,
      superFlip_tmul h11 (h_mem_degree 1), superFlip_tmul (h_mem_degree 2) (h_mem_degree 1),
      superFlip_tmul h21 EKIntegralBases.unit_mem_degree_zero]
    norm_num
  rw [hflip]
  exact comm_coproduct_h21_ne

/-! ## Not commutative -/

/-- Supercommutativity of `OΛ` for its `ℤ/2`-grading by `d mod 2`. -/
def SuperCommutativeQ : Prop :=
  ∀ a b : ℕ, ∀ x ∈ degreePiece a, ∀ y ∈ degreePiece b, x * y = (-1 : ℤ) ^ (a * b) • (y * x)

/-- E §2.1, p. 5: `OΛ` is not supercommutative (`h₁h₂ ≠ h₂h₁`, the super sign being `+1`). -/
theorem not_superCommutative_Q : ¬ SuperCommutativeQ := by
  intro hc
  have := hc 1 2 _ (h_mem_degree 1) _ (h_mem_degree 2)
  norm_num at this
  exact EKPresentationControls.noncommuting_control this

/-! ## `S ≠ ψ₁ψ₂R` -/

/-- `ψ₁ψ₂R(h₁²) = h₁²`. -/
theorem psi12_reverse_square :
    EKAutomorphisms.psi12 (EKAutomorphisms.reverseLinear (h 1 * h 1)) = h 1 * h 1 := by
  rw [EKAutomorphisms.reverse_mul, EKAutomorphisms.reverse_h, map_mul,
    EKAutomorphisms.psi12_h, EKPresentationControls.degree_one]
  simp [EKAutomorphisms.s]

/-- E §2.1, p. 5 (with `ψ₃` read as the ordinary anti-involution `R`): the antipode `S` of `OΛ`
is not `ψ₁ψ₂R`, as `S(h₁²) = -h₁²` but `ψ₁ψ₂R(h₁²) = h₁²`. -/
theorem antipode_ne_psi12_reverse :
    EKAntipode.S ≠ EKAutomorphisms.psi12.toRingHom.toIntAlgHom.toLinearMap.comp
      EKAutomorphisms.reverseLinear := by
  intro hS
  have := LinearMap.congr_fun hS (h 1 * h 1)
  rw [EKAntipode.S_square_word, LinearMap.comp_apply] at this
  change -(h 1 * h 1) = EKAutomorphisms.psi12 (EKAutomorphisms.reverseLinear (h 1 * h 1)) at this
  rw [psi12_reverse_square] at this
  exact EKAutomorphismsControls.super_square_not_ordinary this

end OddMath.Frontier.OddLRGaps

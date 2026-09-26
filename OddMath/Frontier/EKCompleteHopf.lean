import OddMath.Frontier.EKAntipode

/-!
# [EK] The Hopf superalgebra `Λ`, bundled

Source: Ellis–Khovanov, arXiv:1107.5610v2.
* §2.1, p. 5: the multiplication `(x₁ ⊗ x₂)(y₁ ⊗ y₂) = q^{deg(x₂)deg(y₁)} x₁y₁ ⊗ x₂y₂` on
  homogeneous elements; "bialgebra and Hopf algebra objects in `k-gmod_q`" are called
  `q`-bialgebras and `q`-Hopf algebras.
* §2.2, p. 11: at `q = −1` these are `ℤ`-graded (super)bialgebras and Hopf superalgebras.
* Cor 2.4 (p. 8) and Prop 2.17 (p. 20): `Λ` is a `ℤ`-graded Hopf superalgebra with antipode
  `S = ψ₁ψ₂ψ₃`, and `S² ≠ 1`.

Mathlib's `Bialgebra`/`HopfAlgebra` classes use the untwisted product on `H ⊗ H`, so they do
not apply. `QHopfAlgebra k q H` below records EK's notion: an `ℕ`-graded `k`-algebra `H`
(direct sum of the pieces, graded unit and product), the `q`-twisted product on `H ⊗ H`
(specified on homogeneous tensors), a graded coassociative counital coproduct that is
multiplicative for the twisted product, a counit that is an algebra map vanishing in positive
degree, and a graded antipode satisfying both convolution identities.

`lambdaQHopf : QHopfAlgebra ℤ (-1) Q` assembles the component theorems of `EKCoideal`,
`EKSignedQuotient`, `EKAutomorphisms`, `EKAntipode` and `EKIntegralBases`; the only new
ingredient is the gradedness of the coproduct (`coproduct_mem_tensorPiece`).
`proposition_2_17` states the bundled result together with `S = ψ₁ψ₂ψ₃`, `S² ≠ 1`,
associativity and unitality of the twisted product, and the super anti-multiplicativity of `S`.
Everything is over `ℤ` at `q = −1`.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped TensorProduct BigOperators
namespace OddMath.Frontier.EKComplete

/-- The degree-`d` part of `H ⊗ H`: the span of `y ⊗ z` with `y ∈ H_a`, `z ∈ H_b`, `a + b = d`. -/
def tensorPiece {k H : Type*} [CommRing k] [AddCommGroup H] [Module k H]
    (piece : ℕ → Submodule k H) (d : ℕ) : Submodule k (H ⊗[k] H) :=
  Submodule.span k {w | ∃ a b : ℕ, ∃ y z : H, a + b = d ∧ y ∈ piece a ∧ z ∈ piece b ∧
    w = y ⊗ₜ[k] z}

/-- A `q`-Hopf algebra in EK's sense (§2.1, p. 5): a Hopf algebra object in the category of
`ℕ`-graded `k`-modules with braiding `v ⊗ w ↦ q^{deg v · deg w} w ⊗ v`. -/
structure QHopfAlgebra (k : Type*) [CommRing k] (q : k) (H : Type*) [Ring H] [Algebra k H] where
  /-- The homogeneous pieces `H_d`. -/
  piece : ℕ → Submodule k H
  /-- `H = ⊕_d H_d`. -/
  decomposition : ∀ x : H, ∃! f : ℕ →₀ H, (∀ d, f d ∈ piece d) ∧ (f.sum fun _ y => y) = x
  one_mem : (1 : H) ∈ piece 0
  mul_mem : ∀ {a b : ℕ} {x y : H}, x ∈ piece a → y ∈ piece b → x * y ∈ piece (a + b)
  /-- The `q`-twisted product on `H ⊗ H`. -/
  tensorMul : H ⊗[k] H →ₗ[k] H ⊗[k] H →ₗ[k] H ⊗[k] H
  tensorMul_tmul : ∀ {a b c d : ℕ} {x y z t : H}, x ∈ piece a → y ∈ piece b → z ∈ piece c →
    t ∈ piece d → tensorMul (x ⊗ₜ[k] y) (z ⊗ₜ[k] t) = q ^ (b * c) • ((x * z) ⊗ₜ[k] (y * t))
  comul : H →ₗ[k] H ⊗[k] H
  counit : H →ₐ[k] k
  comul_mem : ∀ {d : ℕ} {x : H}, x ∈ piece d → comul x ∈ tensorPiece piece d
  counit_mem : ∀ {d : ℕ} {x : H}, 0 < d → x ∈ piece d → counit x = 0
  coassoc : ∀ x : H, TensorProduct.assoc k H H H (TensorProduct.map comul LinearMap.id (comul x)) =
    TensorProduct.map LinearMap.id comul (comul x)
  counit_left : ∀ x : H,
    TensorProduct.lid k H (TensorProduct.map counit.toLinearMap LinearMap.id (comul x)) = x
  counit_right : ∀ x : H,
    TensorProduct.rid k H (TensorProduct.map LinearMap.id counit.toLinearMap (comul x)) = x
  comul_one : comul 1 = (1 : H) ⊗ₜ[k] (1 : H)
  comul_mul : ∀ x y : H, comul (x * y) = tensorMul (comul x) (comul y)
  antipode : H →ₗ[k] H
  antipode_mem : ∀ {d : ℕ} {x : H}, x ∈ piece d → antipode x ∈ piece d
  antipode_left : ∀ x : H, TensorProduct.lift (LinearMap.mul k H)
    (TensorProduct.map antipode LinearMap.id (comul x)) = algebraMap k H (counit x)
  antipode_right : ∀ x : H, TensorProduct.lift (LinearMap.mul k H)
    (TensorProduct.map LinearMap.id antipode (comul x)) = algebraMap k H (counit x)

open EKRadicalQuotient (Q quotientCounit)
open EKIntegralBases (degreePiece)
open EKCoideal (quotientCoproduct)
open EKSignedQuotient (quotientTensorMul)
open EKElementaryQuotient (h)

/-! ## Gradedness of the coproduct of `Λ` -/

theorem tensorMul_tensorPiece {a b : ℕ} {u v : Q ⊗[ℤ] Q}
    (hu : u ∈ tensorPiece degreePiece a) (hv : v ∈ tensorPiece degreePiece b) :
    quotientTensorMul u v ∈ tensorPiece degreePiece (a + b) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a₁, a₂, y, z, ha, hy, hz, rfl⟩ := hu
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨b₁, b₂, y', z', hb, hy', hz', rfl⟩ := hv
      rw [EKAutomorphisms.tensorMul_homogeneous hy hz hy' hz']
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a₁ + b₁, a₂ + b₂, _, _, by omega,
        EKIntegralBases.degreePiece_mul hy hy', EKIntegralBases.degreePiece_mul hz hz', rfl⟩)
    | zero => simp
    | add v w _ _ hv hw => rw [map_add]; exact Submodule.add_mem _ hv hw
    | smul r v _ hv => rw [map_smul]; exact Submodule.smul_mem _ r hv
  | zero => simp
  | add u w _ _ hu hw => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hu hw
  | smul r u _ hu => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ r hu

theorem coproduct_h_mem (n : ℕ) : quotientCoproduct (h n) ∈ tensorPiece degreePiece n := by
  rw [EKAutomorphisms.coproduct_h]
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, n - i, _, _, by omega, ?_, ?_, rfl⟩
  · simpa using EKAutomorphisms.hWord_degree [(i : ℕ)]
  · simpa using EKAutomorphisms.hWord_degree [n - i]

theorem coproduct_word_mem (w : List ℕ) :
    quotientCoproduct ((w.map h).prod) ∈ tensorPiece degreePiece w.sum := by
  induction w with
  | nil =>
    rw [List.map_nil, List.prod_nil, EKSignedQuotient.quotient_coproduct_one]
    exact Submodule.subset_span ⟨0, 0, 1, 1, rfl, EKIntegralBases.unit_mem_degree_zero,
      EKIntegralBases.unit_mem_degree_zero, rfl⟩
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons, EKSignedQuotient.quotient_coproduct_mul, List.sum_cons]
    exact tensorMul_tensorPiece (coproduct_h_mem a) ih

/-- The coproduct of `Λ` is graded. -/
theorem coproduct_mem_tensorPiece {d : ℕ} {x : Q} (hx : x ∈ degreePiece d) :
    quotientCoproduct x ∈ tensorPiece degreePiece d := by
  rw [EKIntegralBases.degreePiece_eq_hPartition_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, rfl⟩ := hx
    have := coproduct_word_mem μ.val.rowLens
    rw [EKIntegralBases.rowLens_sum, μ.property] at this
    exact this
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-! ## The bundled structure -/

/-- **EK Cor 2.4 and Prop 2.17**: `Λ` (over `ℤ`, `q = −1`) is a `(−1)`-Hopf algebra, i.e. a
`ℤ`-graded Hopf superalgebra, with antipode `S = ψ₁ψ₂ψ₃`. -/
def lambdaQHopf : QHopfAlgebra ℤ (-1) Q where
  piece := degreePiece
  decomposition := EKIntegralBases.unique_homogeneous_decomposition
  one_mem := EKIntegralBases.unit_mem_degree_zero
  mul_mem := EKIntegralBases.degreePiece_mul
  tensorMul := quotientTensorMul
  tensorMul_tmul := EKAutomorphisms.tensorMul_homogeneous
  comul := quotientCoproduct
  counit := quotientCounit
  comul_mem := coproduct_mem_tensorPiece
  counit_mem := fun hd hx => EKAutomorphisms.counit_positive (Nat.pos_iff_ne_zero.mp hd) hx
  coassoc := EKCoideal.quotient_coassociativity
  counit_left := EKCoideal.quotient_counit_left
  counit_right := EKCoideal.quotient_counit_right
  comul_one := EKSignedQuotient.quotient_coproduct_one
  comul_mul := EKSignedQuotient.quotient_coproduct_mul
  antipode := EKAntipode.S
  antipode_mem := EKAntipode.S_degree
  antipode_left := fun x => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact EKAntipode.convolution_left x
  antipode_right := fun x => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact EKAntipode.convolution_right x

/-- **EK Prop 2.17, bundled.** `Λ` carries the `(−1)`-Hopf algebra structure `lambdaQHopf`
whose data are the coproduct, counit and antipode `S = ψ₁ψ₂ψ₃` of the component modules;
the twisted product on `Λ ⊗ Λ` is associative and unital; `S` is a super anti-homomorphism;
and `S² ≠ 1`. -/
theorem proposition_2_17 :
    lambdaQHopf.piece = degreePiece ∧
    lambdaQHopf.comul = quotientCoproduct ∧
    lambdaQHopf.counit = quotientCounit ∧
    (∀ x, lambdaQHopf.antipode x =
      EKPresentation.psi1 (EKAutomorphisms.psi2 (EKAutomorphisms.psi3 x))) ∧
    (∀ u v w, lambdaQHopf.tensorMul (lambdaQHopf.tensorMul u v) w =
      lambdaQHopf.tensorMul u (lambdaQHopf.tensorMul v w)) ∧
    (∀ u, lambdaQHopf.tensorMul ((1 : Q) ⊗ₜ[ℤ] (1 : Q)) u = u ∧
      lambdaQHopf.tensorMul u ((1 : Q) ⊗ₜ[ℤ] (1 : Q)) = u) ∧
    (∀ {a b : ℕ} {x y : Q}, x ∈ degreePiece a → y ∈ degreePiece b →
      lambdaQHopf.antipode (x * y) =
        (-1 : ℤ) ^ (a * b) • (lambdaQHopf.antipode y * lambdaQHopf.antipode x)) ∧
    lambdaQHopf.antipode 1 = 1 ∧
    lambdaQHopf.antipode.comp lambdaQHopf.antipode ≠ LinearMap.id :=
  ⟨rfl, rfl, rfl, fun _ => rfl, EKSignedQuotient.quotientTensorMul_assoc,
    fun u => ⟨EKSignedQuotient.quotientTensorMul_one_left u,
      EKSignedQuotient.quotientTensorMul_one_right u⟩,
    fun hx hy => EKAntipode.S_mul hx hy, EKAntipode.S_one,
    fun he => EKAntipode.S_not_involutive (LinearMap.congr_fun he (h 2))⟩

end OddMath.Frontier.EKComplete

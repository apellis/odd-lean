/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendMackeyTarget
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerSkewAction
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerContent

/-!
# The append Mackey target on the content corner of the cyclotomic quotient

Let `A = Hn (n+1) / I^Λ` be the cyclotomic quotient (`CyclotomicAlgebra`) and
`e = e(β)` the content idempotent of a multiset `β` (`cyclotomicContentIdempotent`), which is
central and even. The coefficient ring of the append-side Mackey boundary
(`DeformedMackeyBoundary.md`, append side; Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of
Lemma 8.1) is the corner `B_β = e A e` (`CyclotomicContentCorner`), a ring with unit `e`:

* `B_β` is a left `Hn (n+1)`-module through `A`, with `(r • y) b = r • (y b)`;
* the parity involution `φ_i = coefficientParityHom (D.parity i)` fixes `e` and restricts to a
  ring endomorphism `σ_β` of `B_β` (`contentCornerParity`) with
  `σ_β (r • y) = tw(r) • σ_β y` (`contentCornerParity_smul`), where `tw` is the parity twist of
  the appended colour; the identity `φ_i = rightDotCoefficient i`
  (`coefficientParityHom_parity_eq_rightDotCoefficient`) brings in `rightDotCoefficient_smul`.

`appendContentMackeyTarget` is then `appendMackeyTarget` at `B_β`, `σ_β`: the target side of
`MackeyCosets` on `L₀ = ψ(1) (Hn (n+2) ψ(1) ⊗_(Hn (n+1)) B_β)`, with `direct` and `span` the
decomposition `L₀ = F(L₀') ⊕ j(V₀)` of `appendTensorCornerEquiv`.
-/

noncomputable section
open StringDiagrams Categorification Supercategory

namespace OddMath.QuiverHecke

universe u v

variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (n : ℕ) (β : Multiset I)

theorem cyclotomicContentIdempotent_isIdempotentElem :
    IsIdempotentElem (cyclotomicContentIdempotent D Sc a n β) :=
  cyclotomicContentIdempotent_sq D Sc a n β

/-- The content-`β` corner `e(β) A e(β)` of the cyclotomic quotient `A`, a ring with unit
`e(β)`. -/
abbrev CyclotomicContentCorner :=
  (cyclotomicContentIdempotent_isIdempotentElem D Sc a n β).Corner

theorem cyclotomicContentCorner_mem_iff (x : CyclotomicAlgebra D Sc a n) :
    x ∈ Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) ↔
      cyclotomicContentIdempotent D Sc a n β * x = x :=
  (Subsemigroup.mem_corner_iff (cyclotomicContentIdempotent_isIdempotentElem D Sc a n β)).trans
    ⟨fun h => h.1, fun h => ⟨h, by rw [← cyclotomicContentIdempotent_central, h]⟩⟩

/-- The underlying element of the quotient. -/
def contentCornerVal (x : CyclotomicContentCorner D Sc a n β) : CyclotomicAlgebra D Sc a n :=
  (show Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) from x).1

theorem contentCornerVal_mem (x : CyclotomicContentCorner D Sc a n β) :
    contentCornerVal D Sc a n β x ∈ Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) :=
  (show Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) from x).2

/-- The corner element of an element of the corner subsemigroup. -/
def contentCornerMk (y : CyclotomicAlgebra D Sc a n)
    (hy : y ∈ Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β)) :
    CyclotomicContentCorner D Sc a n β :=
  show Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) from ⟨y, hy⟩

@[simp] theorem contentCornerVal_mk (y : CyclotomicAlgebra D Sc a n)
    (hy : y ∈ Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β)) :
    contentCornerVal D Sc a n β (contentCornerMk D Sc a n β y hy) = y := rfl

theorem contentCornerVal_injective : Function.Injective (contentCornerVal D Sc a n β) :=
  fun x y h => (Subtype.ext h :
    (show Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) from x) =
      show Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) from y)

theorem contentCornerVal_one :
    contentCornerVal D Sc a n β 1 = cyclotomicContentIdempotent D Sc a n β := rfl

theorem contentCornerVal_mul (x y : CyclotomicContentCorner D Sc a n β) :
    contentCornerVal D Sc a n β (x * y) =
      contentCornerVal D Sc a n β x * contentCornerVal D Sc a n β y := rfl

theorem contentCornerVal_e_mul (x : CyclotomicContentCorner D Sc a n β) :
    cyclotomicContentIdempotent D Sc a n β * contentCornerVal D Sc a n β x =
      contentCornerVal D Sc a n β x :=
  (cyclotomicContentCorner_mem_iff D Sc a n β _).mp (contentCornerVal_mem D Sc a n β x)

theorem cyclotomicContentCorner_mul_mem (z : CyclotomicAlgebra D Sc a n)
    (x : CyclotomicContentCorner D Sc a n β) :
    z * contentCornerVal D Sc a n β x ∈
      Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) := by
  rw [cyclotomicContentCorner_mem_iff, ← mul_assoc, cyclotomicContentIdempotent_central,
    mul_assoc, contentCornerVal_e_mul]

/-- The inclusion of the corner as an additive map. -/
def contentCornerValHom :
    CyclotomicContentCorner D Sc a n β →+ CyclotomicAlgebra D Sc a n where
  toFun := contentCornerVal D Sc a n β
  map_zero' := rfl
  map_add' _ _ := rfl

instance : SMul (Hn D Sc (n + 1)) (CyclotomicContentCorner D Sc a n β) :=
  ⟨fun r x => contentCornerMk D Sc a n β (r • contentCornerVal D Sc a n β x) (by
    exact cyclotomicContentCorner_mul_mem D Sc a n β (cyclotomicMk D Sc a n r) x)⟩

theorem contentCornerVal_smul (r : Hn D Sc (n + 1)) (x : CyclotomicContentCorner D Sc a n β) :
    contentCornerVal D Sc a n β (r • x) = r • contentCornerVal D Sc a n β x := rfl

instance : Module (Hn D Sc (n + 1)) (CyclotomicContentCorner D Sc a n β) :=
  Function.Injective.module _ (contentCornerValHom D Sc a n β)
    (contentCornerVal_injective D Sc a n β) fun _ _ => rfl

instance : IsScalarTower (Hn D Sc (n + 1)) (CyclotomicContentCorner D Sc a n β)
    (CyclotomicContentCorner D Sc a n β) :=
  ⟨fun r x y => contentCornerVal_injective D Sc a n β
    (smul_mul_assoc r (contentCornerVal D Sc a n β x) (contentCornerVal D Sc a n β y))⟩

variable (i : I) (ha : CyclotomicPolynomialParity D a)

/-- The parity involution of the appended colour is the coefficient involution `φ_i`. -/
theorem coefficientParityHom_parity_eq_rightDotCoefficient (c : CyclotomicAlgebra D Sc a n) :
    coefficientParityHom D Sc a ha n (D.parity i) c = rightDotCoefficient D Sc i a ha n c := by
  induction c using SuperBimodule.alg_induction_on (cyclotomicParity D Sc a ha n) with
  | zero => simp
  | add b c hb hc => rw [map_add, map_add, hb, hc]
  | hom q c hc =>
    rw [rightDotCoefficient_of_mem D Sc i a ha n q c hc]
    exact (SVec.sgn_apply_of_mem (D.parity i) hc).trans (by rw [mul_comm])

/-- The parity involution fixes the (even) content idempotent. -/
theorem coefficientParityHom_contentIdempotent (p : ZMod 2) :
    coefficientParityHom D Sc a ha n p (cyclotomicContentIdempotent D Sc a n β) =
      cyclotomicContentIdempotent D Sc a n β := by
  change (cyclotomicSuperspace D Sc a ha n).sgn p _ = _
  rw [SVec.sgn_apply_of_mem p (cyclotomicContentIdempotent_parity D Sc a ha n β)]
  simp

/-- The parity involution of the appended colour, restricted to the content corner. -/
def contentCornerParity :
    CyclotomicContentCorner D Sc a n β →+* CyclotomicContentCorner D Sc a n β where
  toFun x := contentCornerMk D Sc a n β
    (coefficientParityHom D Sc a ha n (D.parity i) (contentCornerVal D Sc a n β x)) (by
      rw [cyclotomicContentCorner_mem_iff, ← coefficientParityHom_contentIdempotent D Sc a n β ha
          (D.parity i), ← map_mul, contentCornerVal_e_mul])
  map_zero' := contentCornerVal_injective D Sc a n β (map_zero _)
  map_add' x y := contentCornerVal_injective D Sc a n β (map_add _ _ _)
  map_one' := contentCornerVal_injective D Sc a n β
    (coefficientParityHom_contentIdempotent D Sc a n β ha (D.parity i))
  map_mul' x y := contentCornerVal_injective D Sc a n β (map_mul _ _ _)

/-- `σ_β (r • y) = tw(r) • σ_β y`. -/
theorem contentCornerParity_smul (r : Hn D Sc (n + 1)) (y : CyclotomicContentCorner D Sc a n β) :
    contentCornerParity D Sc a n β i ha (r • y) =
      homMatrixTwist D Sc (n + 1) (D.parity i) r • contentCornerParity D Sc a n β i ha y := by
  apply contentCornerVal_injective D Sc a n β
  change coefficientParityHom D Sc a ha n (D.parity i) (r • contentCornerVal D Sc a n β y) =
    homMatrixTwist D Sc (n + 1) (D.parity i) r •
      coefficientParityHom D Sc a ha n (D.parity i) (contentCornerVal D Sc a n β y)
  rw [coefficientParityHom_parity_eq_rightDotCoefficient,
    coefficientParityHom_parity_eq_rightDotCoefficient, rightDotCoefficient_smul]

/-- **The target side of the append-side Mackey boundary on the content-`β` corner** of the
cyclotomic quotient: `appendMackeyTarget` at `B_β = e(β) A e(β)` with the twist `σ_β`. -/
def appendContentMackeyTarget :
    CyclotomicAction.BoundaryPolynomial.MackeyTarget (contentCornerParity D Sc a n β i ha)
      (appendTensorFixed D Sc i n (CyclotomicContentCorner D Sc a n β))
      (appendTensorLeftCoordinates D Sc i n (CyclotomicContentCorner D Sc a n β)) :=
  appendMackeyTarget D Sc i n (CyclotomicContentCorner D Sc a n β)
    (contentCornerParity D Sc a n β i ha) (contentCornerParity_smul D Sc a n β i ha)

end OddMath.QuiverHecke

import OddMath.SKM.TwistedClosureDetector

/-! # Closure detection with a twisted principal coefficient

The closure `-id` on `ℕ →₀ ℤ` has principal coefficient `-p`, a twist of `p` by the injective
map `p ↦ -p`, and no corrections. The map `x ↦ x + N x` with `N` the shift lowering the
filtration `F n = {x | x i = 0 for i ≥ n}` of `ℕ →₀ ℤ` is bijective.
-/

namespace NonVacuity.TwistedClosureDetector
open OddMath.SKM.OrientedReduction

example : Function.Injective (LinearMap.id : (ℕ →₀ ℤ) →ₗ[ℤ] (ℕ →₀ ℤ)) :=
  injective_of_positive_closure_twisted (k := ℤ) (fun n : ℕ => n) LinearMap.id LinearMap.id
    (-LinearMap.id) Function.injective_id (negAddMonoidHom) neg_injective fun i p =>
      ⟨0, by simp, by simp⟩

/-- The filtration by vanishing above `n`. -/
def F (n : ℕ) : Submodule ℤ (ℕ →₀ ℤ) where
  carrier := {x | ∀ i, n ≤ i → x i = 0}
  add_mem' hx hy i hi := by simp [hx i hi, hy i hi]
  zero_mem' _ _ := rfl
  smul_mem' c x hx i hi := by simp [hx i hi]

/-- The shift `x ↦ (i ↦ x (i + 1))`, which lowers `F`. -/
noncomputable def N : (ℕ →₀ ℤ) →ₗ[ℤ] (ℕ →₀ ℤ) := Finsupp.lcomapDomain (· + 1) fun _ _ h => by
  simpa using h

example : Function.Bijective (LinearMap.id (R := ℤ) (M := ℕ →₀ ℤ) + N) :=
  bijective_id_add_of_lowering N F
    (fun x => ⟨x.support.sup id + 1, fun i hi => Finsupp.notMem_support_iff.mp fun h =>
      absurd (Finset.le_sup (f := id) h) (by simp; omega)⟩)
    (fun x hx => by ext i; simp [N, hx (i + 1) (by omega)])
    (fun n x hx i hi => by simp [N, hx (i + 1) (by omega)])

end NonVacuity.TwistedClosureDetector

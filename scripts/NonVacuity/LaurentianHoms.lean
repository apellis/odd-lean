import OddMath

/-! Concrete rational rank-one consumers of the Laurentian Hom bounds. -/

noncomputable section
namespace LaurentianHomsConsumer
open CategoryTheory StringDiagrams OddMath.SKM

abbrev datum := TwoStrandShiftConsumer.datum
abbrev sy := TwoStrandShiftConsumer.symmetrizer

/-- Rational even rank-one scalar parameters. -/
def scalars : Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by
    rintro ⟨i, hi⟩
    exact (zero_ne_one hi).elim

/-- Constant bubble-normalization units satisfy the shift law. -/
def cScalars : CScalars scalars where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [scalars]

theorem homogeneous : scalars.Homogeneous :=
  fun _ _ _ _ _ _ _ _ h => absurd rfl h

theorem locallyFinite : sy.DegreeLocallyFinite := fun _ => Set.toFinite _

/-- Empty-boundary endomorphisms have finite-dimensional pieces. -/
example (μ n : ℤ) : FiniteDimensional ℚ
    ((pres datum scalars).homDeg (gdeg datum sy) (ob datum μ []) (ob datum μ []) n) :=
  (hom_laurentian sy scalars cScalars homogeneous locallyFinite μ [] []).1 n

/-- The same empty-boundary space is bounded below. -/
example (μ : ℤ) : ∃ N, ∀ n < N,
    (pres datum scalars).homDeg (gdeg datum sy) (ob datum μ []) (ob datum μ []) n = ⊥ :=
  (hom_laurentian sy scalars cScalars homogeneous locallyFinite μ [] []).2

/-- One upward strand, in every external weight and degree. -/
example (μ n : ℤ) : FiniteDimensional ℚ
    ((pres datum scalars).homDeg (gdeg datum sy)
      (ob datum μ [up ()]) (ob datum μ [up ()]) n) :=
  (hom_laurentian sy scalars cScalars homogeneous locallyFinite μ [up ()] [up ()]).1 n

/-- Both parity intersections have finite-dimensional one-strand pieces. -/
example (μ n : ℤ) (p : ZMod 2) : FiniteDimensional ℚ
    ↥((pres datum scalars).homDeg (gdeg datum sy)
      (ob datum μ [up ()]) (ob datum μ [up ()]) n ⊓
        homPar datum scalars μ [up ()] [up ()] p) :=
  (hom_parity_laurentian sy scalars cScalars homogeneous locallyFinite μ [up ()] [up ()]).1 n p

/-- A single lower bound works simultaneously for both parities. -/
example (μ : ℤ) : ∃ N, ∀ n < N, ∀ p,
    (pres datum scalars).homDeg (gdeg datum sy)
      (ob datum μ [up ()]) (ob datum μ [up ()]) n ⊓
        homPar datum scalars μ [up ()] [up ()] p = ⊥ :=
  (hom_parity_laurentian sy scalars cScalars homogeneous locallyFinite μ [up ()] [up ()]).2

/-- Unequal-weight boundaries need no extra premise. -/
example (μ n : ℤ) : FiniteDimensional ℚ
    ((pres datum scalars).homDeg (gdeg datum sy)
      (ob datum μ [up ()]) (ob datum μ []) n) :=
  (hom_laurentian sy scalars cScalars homogeneous locallyFinite μ [up ()] []).1 n

#print axioms OddMath.SKM.hom_laurentian
#print axioms OddMath.SKM.hom_parity_laurentian

end LaurentianHomsConsumer

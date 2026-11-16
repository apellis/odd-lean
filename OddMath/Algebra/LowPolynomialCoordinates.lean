import OddMath.Algebra.FiniteTriangularCoordinates

/-! # Finite vectors and low polynomial coordinates

The finite coefficient coordinates used in the negative-height cap matrix
of DeformedRouquierMatrix, section 4. The same supported-polynomial and
reversed-vector changes apply to both moving parities.
-/
noncomputable section
namespace OddMath.LowPolynomialCoordinates
def finIioEquiv (m : ℕ) : Fin m ≃ Set.Iio m where
  toFun i := ⟨i.val, i.isLt⟩
  invFun i := ⟨i.val, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def lowVectorEquiv {k M : Type*} [CommRing k] [AddCommGroup M] [Module k M]
    (m : ℕ) : (Fin m → M) ≃ₗ[k] Finsupp.supported M k (Set.Iio m) :=
  ((Finsupp.linearEquivFunOnFinite k M (Fin m)).symm.trans
    (Finsupp.domLCongr (finIioEquiv m))).trans
      (Finsupp.supportedEquivFinsupp (R := k) (M := M) (Set.Iio m)).symm

theorem lowVectorEquiv_single {k M : Type*} [CommRing k]
    [AddCommGroup M] [Module k M] (m : ℕ) (d : Fin m) (b : M) :
    ((lowVectorEquiv (k := k) (M := M) m (Pi.single d b) :
      Finsupp.supported M k (Set.Iio m)) : ℕ →₀ M) = Finsupp.single d.val b := by
  simp only [lowVectorEquiv, LinearEquiv.trans_apply,
    Finsupp.linearEquivFunOnFinite_symm_single, Finsupp.domLCongr_single,
    Finsupp.supportedEquivFinsupp_symm_single]
  rfl

def reversedVector {k M : Type*} [CommRing k] [AddCommGroup M] [Module k M]
    (m : ℕ) : (Fin m → M) ≃ₗ[k] (Fin m → M) where
  toFun f i := f i.rev
  invFun f i := f i.rev
  left_inv f := by ext i; simp only [Fin.rev_rev]
  right_inv f := by ext i; simp only [Fin.rev_rev]
  map_add' f g := rfl
  map_smul' c f := rfl

theorem reversedVector_single {k M : Type*} [CommRing k]
    [AddCommGroup M] [Module k M] (m : ℕ) (d : Fin m) (b : M) :
    reversedVector (k := k) m (Pi.single d b) = Pi.single d.rev b := by
  classical
  ext i
  change (Pi.single d b : Fin m → M) i.rev = (Pi.single d.rev b : Fin m → M) i
  by_cases hi : i = d.rev
  · subst i; simp
  · have hr : i.rev ≠ d := by
      intro h
      have hh := congrArg Fin.rev h
      simp only [Fin.rev_rev] at hh
      exact hi hh
    simp [hi, hr]

end OddMath.LowPolynomialCoordinates

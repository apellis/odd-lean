import OddMath.SKM.UniversalCoefficientRationalization

/-! Rationalization preserves the two zero divisors in the group algebra of
an order-two group. Its polynomial extension fixes variables and maps
coefficients, including for the original normalization group. -/

noncomputable section
namespace NonVacuity.UniversalCoefficientRationalization

open OddMath.SKM
open OddMath.SKM.UniversalCoefficientRing
open OddMath.SKM.UniversalCoefficientRationalization

private abbrev G := ZMod 2
private abbrev e : AddMonoidAlgebra HalfIntegers G := AddMonoidAlgebra.single 1 1
private def f : AddMonoidAlgebra HalfIntegers G →+* AddMonoidAlgebra ℚ G :=
  AddMonoidAlgebra.mapRingHom _ coefficientMap

private theorem f_injective : Function.Injective f :=
  AddMonoidAlgebra.map_injective _ coefficientMap_injective

private theorem e_sq : e * e = 1 := by
  change AddMonoidAlgebra.single (1 : G) 1 * AddMonoidAlgebra.single (1 : G) 1 = 1
  rw [AddMonoidAlgebra.single_mul_single, one_mul, show (1 : G) + 1 = 0 by decide]
  exact AddMonoidAlgebra.one_def.symm

private theorem left_ne_zero : e - 1 ≠ 0 := by
  intro h
  have hg : (1 : G) ≠ 0 := by decide
  have hz : (1 : HalfIntegers) = 0 := by simpa [e, hg, AddMonoidAlgebra.one_def] using
    (show (e - 1).coeff 1 = (0 : AddMonoidAlgebra HalfIntegers G).coeff 1 from
      congrArg (fun x : AddMonoidAlgebra HalfIntegers G => x.coeff 1) h)
  have := congrArg coefficientMap hz
  norm_num at this

private theorem right_ne_zero : e + 1 ≠ 0 := by
  intro h
  have hg : (1 : G) ≠ 0 := by decide
  have hz : (1 : HalfIntegers) = 0 := by simpa [e, hg, AddMonoidAlgebra.one_def] using
    (show (e + 1).coeff 1 = (0 : AddMonoidAlgebra HalfIntegers G).coeff 1 from
      congrArg (fun x : AddMonoidAlgebra HalfIntegers G => x.coeff 1) h)
  have := congrArg coefficientMap hz
  norm_num at this

example : (e - 1) * (e + 1) = 0 := by
  calc
    (e - 1) * (e + 1) = e * e - 1 := by ring
    _ = 0 := by rw [e_sq]; ring

example : f (e - 1) ≠ 0 := by
  intro h
  exact left_ne_zero (f_injective (by simpa using h))

example : f (e + 1) ≠ 0 := by
  intro h
  exact right_ne_zero (f_injective (by simpa using h))

example : f (e - 1) ≠ f (e + 1) := by
  intro h
  have h' := f_injective h
  have hc := congrArg (fun x : AddMonoidAlgebra HalfIntegers G =>
    coefficientMap (x.coeff 0)) h'
  have hg : (1 : G) ≠ 0 := by decide
  have hq : (-1 : ℚ) = 1 := by simpa [e, hg, AddMonoidAlgebra.one_def] using hc
  norm_num at hq

private def p : MvPolynomial Bool (AddMonoidAlgebra HalfIntegers G) :=
  MvPolynomial.X true + MvPolynomial.C (e - 1)

example : MvPolynomial.map f p =
    MvPolynomial.X true + MvPolynomial.C (f (e - 1)) := by simp [p]

example (a : AddMonoidAlgebra HalfIntegers G) : p ≠ MvPolynomial.C a := by
  intro h
  have hc := congrArg (fun q : MvPolynomial Bool (AddMonoidAlgebra HalfIntegers G) =>
    q.coeff (Finsupp.single true 1)) h
  have hne : (0 : Bool →₀ ℕ) ≠ Finsupp.single true 1 := by
    intro he
    have hx := congrArg (fun z : Bool →₀ ℕ => z true) he
    simp at hx
  change (MvPolynomial.X true + MvPolynomial.C (e - 1)).coeff
    (Finsupp.single true 1) = (MvPolynomial.C a).coeff (Finsupp.single true 1) at hc
  have hz : (1 : AddMonoidAlgebra HalfIntegers G) = 0 := by simpa [hne] using hc
  have hz' : (1 : HalfIntegers) = 0 := by simpa [AddMonoidAlgebra.one_def] using
    (congrArg (fun x : AddMonoidAlgebra HalfIntegers G => x.coeff 0) hz)
  have := congrArg coefficientMap hz'
  norm_num at this

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
    (D : Datum I X) (σ : Type w) (s : σ) (a : UnitRing D)

example : rationalizePolynomial D σ (MvPolynomial.X s + MvPolynomial.C a) =
    MvPolynomial.X s + MvPolynomial.C (rationalize D a) := by simp

#print axioms OddMath.SKM.UniversalCoefficientRationalization.coefficientMap_injective
#print axioms OddMath.SKM.UniversalCoefficientRationalization.rationalize_injective
#print axioms OddMath.SKM.UniversalCoefficientRationalization.rationalizePolynomial_injective

end NonVacuity.UniversalCoefficientRationalization

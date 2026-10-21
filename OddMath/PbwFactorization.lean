import OddMath.PbwModelRelations
import OddMath.PbwPresentation

/-!
# The comparison map from the presented ring to the skew-polynomial model

Word evaluation in the skew-polynomial model kills each relation word
`x_i x_j + x_j x_i` (`OddMath.PbwModelRelations.rel_sum`), hence factors through the
presented ring of `OddMath.PbwPresentation` as a ring homomorphism
`Phi : Presented n →+* SkewPolynomial n` with `Phi (q i) = generator i`.

Word evaluation `evalAlg` is the free-algebra universal property (`FreeAlgebra.lift` at the
model generators). This needs typeclass structure on the model: the operations
`SkewPolynomial.mul` and `SkewPolynomial.one` satisfy the `Ring` axioms by the existing
theorems `mul_assoc`, `one_mul`, `mul_one`, `add_mul`, `mul_add`, `zero_mul` and `mul_zero`
(casts go through `• 1`), so this module equips `SkewPolynomial n` with `Semiring` and `Ring`
instances built from those theorems and the ambient `Finsupp` additive structure. The
instances are `noncomputable` because the model operations are classical finite-support
sums.

Main results:
- `evalAlg_ι`: evaluation sends each free generator to the model generator.
- `evalAlg_kills`: evaluation kills each relation word `x_i x_j + x_j x_i` for `i ≠ j`.
- `kill_mem`: evaluation kills the relation ideal (via `TwoSidedIdeal.span_induction`).
- `Phi`: the induced map `Presented n →+* SkewPolynomial n` (`Ideal.Quotient.lift` of the
  evaluation ring homomorphism).
- `Phi_q` / `Phi_mul_gens` / `Phi_rel`: `Phi` on generators, their products, and the
  relation sum.
- `Phi_sq_form` / `Phi_sq_ne_zero`: the square of a generator maps to the model square,
  which does not vanish.
- `factorization`: the conjunction of `Phi_q` and `evalAlg_kills`.

Surjectivity is `OddMath.Frontier.PbwRealization.Phi_surjective`; bijectivity and the ring
isomorphism are `OddMath.Frontier.PbwEquivalence.Phi_bijective` and `presentedEquiv`.
-/

namespace OddMath.PbwFactorization

/-- Model multiplication as a typeclass `Mul`: exactly the named
`SkewPolynomial.mul` (no new multiplication is introduced). -/
noncomputable instance instMul (n : ℕ) :
    Mul (OddMath.SkewPolynomial.SkewPolynomial n) :=
  ⟨OddMath.SkewPolynomial.mul⟩

/-- Model unit as a typeclass `One`: exactly the named `SkewPolynomial.one`. -/
noncomputable instance instOne (n : ℕ) :
    One (OddMath.SkewPolynomial.SkewPolynomial n) :=
  ⟨OddMath.SkewPolynomial.one⟩

/-- Natural-number casts, routed through the integer cast so that
`intCast_ofNat` holds by reflexivity. -/
noncomputable instance instNatCast (n : ℕ) :
    NatCast (OddMath.SkewPolynomial.SkewPolynomial n) :=
  ⟨fun k => ((k : ℤ)) • (1 : OddMath.SkewPolynomial.SkewPolynomial n)⟩

/-- Integer casts: `k • 1` through the ambient `Finsupp` additive structure. -/
noncomputable instance instIntCast (n : ℕ) :
    IntCast (OddMath.SkewPolynomial.SkewPolynomial n) :=
  ⟨fun k => k • (1 : OddMath.SkewPolynomial.SkewPolynomial n)⟩

/-- Semiring structure on the model, flattened: distributivity and zero
laws (`mul_add`, `add_mul`, `zero_mul`, `mul_zero`), associativity
(`mul_assoc`), unit laws (`one_mul`, `mul_one`), cast coherence via the
`smul` algebra, and the structural power recursor (whose laws are
reflexivity). Additive parents come from the ambient `Finsupp` structure. -/
noncomputable instance instSemiring (n : ℕ) :
    Semiring (OddMath.SkewPolynomial.SkewPolynomial n) where
  left_distrib := OddMath.SkewPolynomial.mul_add
  right_distrib := OddMath.SkewPolynomial.add_mul
  zero_mul := OddMath.SkewPolynomial.zero_mul
  mul_zero := OddMath.SkewPolynomial.mul_zero
  mul_assoc := OddMath.SkewPolynomial.mul_assoc
  one_mul := OddMath.SkewPolynomial.one_mul
  mul_one := OddMath.SkewPolynomial.mul_one
  natCast_zero := by
    show ((((0 : ℕ)) : ℤ)) • (1 : OddMath.SkewPolynomial.SkewPolynomial _) = 0
    rw [Nat.cast_zero, zero_smul]
  natCast_succ := fun k => by
    show ((((k + 1 : ℕ)) : ℤ)) • (1 : OddMath.SkewPolynomial.SkewPolynomial _)
      = ((((k : ℕ)) : ℤ)) • (1 : OddMath.SkewPolynomial.SkewPolynomial _) + 1
    rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  npow := npowRec
  npow_zero := fun _ => rfl
  npow_succ := fun _ _ => rfl

/-- Ring structure on the model, flattened: the semiring leaves above,
negation/subtraction from the ambient `Finsupp` additive group, the `zsmul`
field as the ambient `ℤ`-action, and integer-cast coherence (`negSucc` is
the negated successor cast, by `omega`; `•` respects negation). -/
noncomputable instance instRing (n : ℕ) :
    Ring (OddMath.SkewPolynomial.SkewPolynomial n) where
  left_distrib := OddMath.SkewPolynomial.mul_add
  right_distrib := OddMath.SkewPolynomial.add_mul
  zero_mul := OddMath.SkewPolynomial.zero_mul
  mul_zero := OddMath.SkewPolynomial.mul_zero
  mul_assoc := OddMath.SkewPolynomial.mul_assoc
  one_mul := OddMath.SkewPolynomial.one_mul
  mul_one := OddMath.SkewPolynomial.mul_one
  natCast_zero := by
    show ((((0 : ℕ)) : ℤ)) • (1 : OddMath.SkewPolynomial.SkewPolynomial _) = 0
    rw [Nat.cast_zero, zero_smul]
  natCast_succ := fun k => by
    show ((((k + 1 : ℕ)) : ℤ)) • (1 : OddMath.SkewPolynomial.SkewPolynomial _)
      = ((((k : ℕ)) : ℤ)) • (1 : OddMath.SkewPolynomial.SkewPolynomial _) + 1
    rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  npow := npowRec
  npow_zero := fun _ => rfl
  npow_succ := fun _ _ => rfl
  sub_eq_add_neg := SubNegMonoid.sub_eq_add_neg
  zsmul := fun k x => k • x
  zsmul_zero' := fun x => by simp
  zsmul_succ' := fun k x => by
    show ((((k.succ : ℕ)) : ℤ)) • x = ((((k : ℕ)) : ℤ)) • x + x
    have h : ((((k.succ : ℕ)) : ℤ)) = (((k : ℕ)) : ℤ) + 1 := by omega
    rw [h, add_smul, one_smul]
  zsmul_neg' := fun k x => by
    show (Int.negSucc k) • x = -(((((k.succ : ℕ)) : ℤ)) • x)
    have h : Int.negSucc k = -((((k.succ : ℕ)) : ℤ)) := by omega
    rw [h, neg_smul]
  neg_add_cancel := neg_add_cancel
  intCast_ofNat := fun _ => rfl
  intCast_negSucc := fun k => by
    show (Int.negSucc k) • (1 : OddMath.SkewPolynomial.SkewPolynomial _)
      = -(((((k + 1 : ℕ)) : ℤ)) • (1 : OddMath.SkewPolynomial.SkewPolynomial _))
    have h : Int.negSucc k = -((((k + 1 : ℕ)) : ℤ)) := by omega
    rw [h, neg_smul]

/-- Word evaluation: the free-algebra universal property at the model
generators (words are free-algebra terms). It respects `mul`/`one` by construction
(`map_mul`, `map_one`). -/
noncomputable def evalAlg (n : ℕ) :
    FreeAlgebra ℤ (Fin n) →ₐ[ℤ] OddMath.SkewPolynomial.SkewPolynomial n :=
  FreeAlgebra.lift ℤ (OddMath.SkewPolynomial.generator (n := n))

/-- Evaluation as a ring homomorphism (for the quotient lift). -/
noncomputable def evalRingHom (n : ℕ) :
    FreeAlgebra ℤ (Fin n) →+* OddMath.SkewPolynomial.SkewPolynomial n :=
  (evalAlg n).toRingHom

/-- Evaluation sends each free generator to the model generator. -/
theorem evalAlg_ι (n : ℕ) (i : Fin n) :
    evalAlg n (FreeAlgebra.ι ℤ i) = OddMath.SkewPolynomial.generator i := by
  simp only [evalAlg, FreeAlgebra.lift_ι_apply]

/-- Evaluation kills each relation word `x_i x_j + x_j x_i` for `i ≠ j`
(by `OddMath.PbwModelRelations.rel_sum`). -/
theorem evalAlg_kills (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    evalAlg n (FreeAlgebra.ι ℤ i * FreeAlgebra.ι ℤ j
      + FreeAlgebra.ι ℤ j * FreeAlgebra.ι ℤ i) = 0 := by
  rw [map_add, map_mul, map_mul, evalAlg_ι, evalAlg_ι]
  exact OddMath.PbwModelRelations.rel_sum i j h

/-- Evaluation kills every element of the relation ideal: span induction
(`TwoSidedIdeal.span_induction`). Generators die by `evalAlg_kills`
(definitionally also the `evalRingHom` statement); `0`/sums/negations die by
the hom laws; two-sided multiples die because one factor dies (`mul_zero`,
`zero_mul`). -/
theorem kill_mem (n : ℕ) (w : FreeAlgebra ℤ (Fin n))
    (hw : w ∈ OddMath.PbwPresentation.relIdeal n) :
    evalRingHom n w = 0 := by
  rw [OddMath.PbwPresentation.relIdeal, OddMath.PbwPresentation.relTwoSided,
    TwoSidedIdeal.mem_asIdeal] at hw
  induction hw using TwoSidedIdeal.span_induction with
  | mem x h =>
      obtain ⟨i, j, hh, rfl⟩ := h
      exact evalAlg_kills n i j hh
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | neg x hx ih => rw [map_neg, ih, neg_zero]
  | left_absorb a x hx ih => rw [map_mul, ih, mul_zero]
  | right_absorb b x hx ih => rw [map_mul, ih, zero_mul]

/-- Factorization: evaluation descends through the relation ideal to the
presented object (`Ideal.Quotient.lift` with `kill_mem`). -/
noncomputable def Phi (n : ℕ) :
    OddMath.PbwPresentation.Presented n →+* OddMath.SkewPolynomial.SkewPolynomial n :=
  Ideal.Quotient.lift (OddMath.PbwPresentation.relIdeal n) (evalRingHom n) (kill_mem n)

/-- `Φ` sends each quotient generator to the model generator. -/
theorem Phi_q (n : ℕ) (i : Fin n) :
    Phi n (OddMath.PbwPresentation.q n i) = OddMath.SkewPolynomial.generator i := by
  simp only [Phi, OddMath.PbwPresentation.q]
  show ⇑(evalAlg n) _ = _
  exact evalAlg_ι n i

/-- `Φ` sends quotient products to model products. -/
theorem Phi_mul_gens (n : ℕ) (i j : Fin n) :
    Phi n (OddMath.PbwPresentation.q n i * OddMath.PbwPresentation.q n j)
      = OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
        (OddMath.SkewPolynomial.generator j) := by
  rw [map_mul, Phi_q, Phi_q]
  exact rfl

/-- `Φ` kills the quotient relation sum. -/
theorem Phi_rel (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    Phi n (OddMath.PbwPresentation.q n i * OddMath.PbwPresentation.q n j
      + OddMath.PbwPresentation.q n j * OddMath.PbwPresentation.q n i) = 0 := by
  rw [map_add, Phi_mul_gens, Phi_mul_gens]
  exact OddMath.PbwModelRelations.rel_sum i j h

/-- The diagonal square maps to the model square. -/
theorem Phi_sq_form (n : ℕ) (i : Fin n) :
    Phi n (OddMath.PbwPresentation.q n i * OddMath.PbwPresentation.q n i)
      = OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
        (OddMath.SkewPolynomial.generator i) :=
  Phi_mul_gens n i i

/-- The square of a generator does not vanish under `Φ`: no square-zero law
is imposed (`OddMath.PbwModelRelations.square_ne_zero`). -/
theorem Phi_sq_ne_zero (n : ℕ) (i : Fin n) :
    Phi n (OddMath.PbwPresentation.q n i * OddMath.PbwPresentation.q n i) ≠ 0 := by
  rw [Phi_sq_form]
  exact OddMath.PbwModelRelations.square_ne_zero i

/-- Adequacy conjunction: `Φ` hits the generators and evaluation kills the
relation word. -/
theorem factorization (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    (Phi n (OddMath.PbwPresentation.q n i) = OddMath.SkewPolynomial.generator i)
    ∧ (Phi n (OddMath.PbwPresentation.q n j) = OddMath.SkewPolynomial.generator j)
    ∧ evalAlg n (FreeAlgebra.ι ℤ i * FreeAlgebra.ι ℤ j
        + FreeAlgebra.ι ℤ j * FreeAlgebra.ι ℤ i) = 0 :=
  ⟨Phi_q n i, Phi_q n j, evalAlg_kills n i j h⟩

end OddMath.PbwFactorization

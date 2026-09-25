import OddMath.PbwL1
import OddMath.PbwL2

/-!
# PBW lemma L3: universal factorization (presentation-to-model direction)

Roadmap: an unpublished note, §4,
lemma L3 (R1). This is the presentation-to-model direction of the quotient/PBW
correspondence: word evaluation respects `mul`/`one` and kills each relation
word `x_i x_j + x_j x_i` (by L1), hence factors as
`Φ : P n → SkewPolynomial n` with `Φ (q_i) = generator i`.

The one new definition is word evaluation `evalAlg`, via the free-algebra
universal property (`FreeAlgebra.lift` at the model generators). To state it,
the finite-support model needs typeclass structure: the named
`SkewPolynomial.mul`/`SkewPolynomial.one` satisfy the full `Ring` axioms
(associativity, units, distributivity, zero laws are exactly the existing
`mul_assoc`, `one_mul`, `mul_one`, `add_mul`, `mul_add`, `zero_mul`,
`mul_zero` theorems; casts go through `• 1`), so this module equips
`SkewPolynomial n` with `Semiring`/`Ring` instances using only those theorems
plus the ambient `Finsupp` additive structure. The instances are
`noncomputable` because the named model operations are (classical
finite-support sums). No new facts about the model are proved here (that is
L1, built on, not redone); no quotient content is changed (that is L2, built
on).

What this module proves (sorry-free):
- `evalAlg_ι`: evaluation sends each free generator to the model generator.
- `evalAlg_kills`: evaluation kills each relation word `x_i x_j + x_j x_i`
  for `i ≠ j` (by L1 `rel_sum`).
- `kill_mem`: evaluation kills every element of the relation ideal (span
  induction via `TwoSidedIdeal.span_induction`).
- `Phi`: the factored map `P n →+* SkewPolynomial n`
  (`Ideal.Quotient.lift` of the evaluation ring hom).
- `Phi_q`: `Φ` sends each quotient generator to the model generator.
- `Phi_mul_gens`: `Φ` sends quotient products to model products.
- `Phi_rel`: `Φ` kills the quotient relation sum.
- `Phi_sq_form` / `Phi_sq_ne_zero`: the diagonal square maps to the model
  square, hence does NOT vanish (roadmap §5 explicit non-goal: no
  square-zero law; L1 `square_ne_zero` transported).
- `factorization`: adequacy conjunction — `Φ` hits the generators AND
  evaluation kills the relation word (the exact input L4/L5 need).

Scope (NOT this module): spanning/normal-form existence (L4); linear
independence (L5); the isomorphism/PBW corollary (L6). Finite fixtures in
`OddMath/Tests/PbwL3Fixtures.lean` are development aids
(`SUPPORTED_LOW_DEGREE` at most), never a proof of the correspondence.
-/

namespace OddMath.PbwL3

/-- L3 model multiplication as a typeclass `Mul`: exactly the named
`SkewPolynomial.mul` (no new multiplication is introduced). -/
noncomputable instance instMul (n : ℕ) :
    Mul (OddMath.SkewPolynomial.SkewPolynomial n) :=
  ⟨OddMath.SkewPolynomial.mul⟩

/-- L3 model unit as a typeclass `One`: exactly the named `SkewPolynomial.one`. -/
noncomputable instance instOne (n : ℕ) :
    One (OddMath.SkewPolynomial.SkewPolynomial n) :=
  ⟨OddMath.SkewPolynomial.one⟩

/-- L3 natural-number casts, routed through the integer cast so that
`intCast_ofNat` holds by reflexivity. -/
noncomputable instance instNatCast (n : ℕ) :
    NatCast (OddMath.SkewPolynomial.SkewPolynomial n) :=
  ⟨fun k => ((k : ℤ)) • (1 : OddMath.SkewPolynomial.SkewPolynomial n)⟩

/-- L3 integer casts: `k • 1` through the ambient `Finsupp` additive structure. -/
noncomputable instance instIntCast (n : ℕ) :
    IntCast (OddMath.SkewPolynomial.SkewPolynomial n) :=
  ⟨fun k => k • (1 : OddMath.SkewPolynomial.SkewPolynomial n)⟩

/-- L3 semiring structure on the model, flattened: distributivity and zero
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

/-- L3 ring structure on the model, flattened: the semiring leaves above,
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

/-- L3 word evaluation: the free-algebra universal property at the model
generators. This is the one new definition the roadmap asks for
(`eval : Word n → SkewPolynomial n`, with words as free-algebra terms). It
respects `mul`/`one` by construction (`map_mul`, `map_one`). -/
noncomputable def evalAlg (n : ℕ) :
    FreeAlgebra ℤ (Fin n) →ₐ[ℤ] OddMath.SkewPolynomial.SkewPolynomial n :=
  FreeAlgebra.lift ℤ (OddMath.SkewPolynomial.generator (n := n))

/-- L3 evaluation as a ring homomorphism (for the quotient lift). -/
noncomputable def evalRingHom (n : ℕ) :
    FreeAlgebra ℤ (Fin n) →+* OddMath.SkewPolynomial.SkewPolynomial n :=
  (evalAlg n).toRingHom

/-- L3a: evaluation sends each free generator to the model generator. -/
theorem evalAlg_ι (n : ℕ) (i : Fin n) :
    evalAlg n (FreeAlgebra.ι ℤ i) = OddMath.SkewPolynomial.generator i := by
  simp only [evalAlg, FreeAlgebra.lift_ι_apply]

/-- L3b: evaluation kills each relation word `x_i x_j + x_j x_i` for `i ≠ j`
(by L1 `rel_sum` — the exact model-side input the roadmap prescribes). -/
theorem evalAlg_kills (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    evalAlg n (FreeAlgebra.ι ℤ i * FreeAlgebra.ι ℤ j
      + FreeAlgebra.ι ℤ j * FreeAlgebra.ι ℤ i) = 0 := by
  rw [map_add, map_mul, map_mul, evalAlg_ι, evalAlg_ι]
  exact OddMath.PbwL1.rel_sum i j h

/-- L3c: evaluation kills every element of the relation ideal: span induction
(`TwoSidedIdeal.span_induction`). Generators die by L3b (`evalAlg_kills`,
definitionally also the `evalRingHom` statement); `0`/sums/negations die by
the hom laws; two-sided multiples die because one factor dies (`mul_zero`,
`zero_mul`). -/
theorem kill_mem (n : ℕ) (w : FreeAlgebra ℤ (Fin n))
    (hw : w ∈ OddMath.PbwL2.relIdeal n) :
    evalRingHom n w = 0 := by
  rw [OddMath.PbwL2.relIdeal, OddMath.PbwL2.relTwoSided,
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

/-- L3 factorization: evaluation descends through the relation ideal to the
presented object (`Ideal.Quotient.lift` with L3c). -/
noncomputable def Phi (n : ℕ) :
    OddMath.PbwL2.Presented n →+* OddMath.SkewPolynomial.SkewPolynomial n :=
  Ideal.Quotient.lift (OddMath.PbwL2.relIdeal n) (evalRingHom n) (kill_mem n)

/-- L3d: `Φ` sends each quotient generator to the model generator. -/
theorem Phi_q (n : ℕ) (i : Fin n) :
    Phi n (OddMath.PbwL2.q n i) = OddMath.SkewPolynomial.generator i := by
  simp only [Phi, OddMath.PbwL2.q, Ideal.Quotient.lift_mk]
  show ⇑(evalAlg n) _ = _
  exact evalAlg_ι n i

/-- L3e: `Φ` sends quotient products to model products. -/
theorem Phi_mul_gens (n : ℕ) (i j : Fin n) :
    Phi n (OddMath.PbwL2.q n i * OddMath.PbwL2.q n j)
      = OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
        (OddMath.SkewPolynomial.generator j) := by
  rw [map_mul, Phi_q, Phi_q]
  exact rfl

/-- L3f: `Φ` kills the quotient relation sum. -/
theorem Phi_rel (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    Phi n (OddMath.PbwL2.q n i * OddMath.PbwL2.q n j
      + OddMath.PbwL2.q n j * OddMath.PbwL2.q n i) = 0 := by
  rw [map_add, Phi_mul_gens, Phi_mul_gens]
  exact OddMath.PbwL1.rel_sum i j h

/-- L3g: the diagonal square maps to the model square. -/
theorem Phi_sq_form (n : ℕ) (i : Fin n) :
    Phi n (OddMath.PbwL2.q n i * OddMath.PbwL2.q n i)
      = OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
        (OddMath.SkewPolynomial.generator i) :=
  Phi_mul_gens n i i

/-- L3h: the diagonal square does NOT vanish under `Φ` (roadmap §5: no
square-zero law is imposed; L1 `square_ne_zero` transported). -/
theorem Phi_sq_ne_zero (n : ℕ) (i : Fin n) :
    Phi n (OddMath.PbwL2.q n i * OddMath.PbwL2.q n i) ≠ 0 := by
  rw [Phi_sq_form]
  exact OddMath.PbwL1.square_ne_zero i

/-- L3 adequacy conjunction: `Φ` hits the generators AND evaluation kills the
relation word — the exact input L4/L5 need. -/
theorem factorization (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    (Phi n (OddMath.PbwL2.q n i) = OddMath.SkewPolynomial.generator i)
    ∧ (Phi n (OddMath.PbwL2.q n j) = OddMath.SkewPolynomial.generator j)
    ∧ evalAlg n (FreeAlgebra.ι ℤ i * FreeAlgebra.ι ℤ j
        + FreeAlgebra.ι ℤ j * FreeAlgebra.ι ℤ i) = 0 :=
  ⟨Phi_q n i, Phi_q n j, evalAlg_kills n i j h⟩

end OddMath.PbwL3

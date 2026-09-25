import OddMath.PbwL2
import OddMath.PbwL3
import OddMath.SkewPolynomial
import OddMath.Frontier.PbwEquivalence
import OddMath.Frontier.NilHeckeGradedEnd
import OddMath.Frontier.NilHeckeGrading
import OddMath.Frontier.NilHeckeSmallRankControls

/-! EKL small-rank boundary production module (N = 0, N = 1).

Source: EKL1111.1320v1, pages 14-17 (exceptional-rank dot/MNS-matrix checks).
Predecessor: `OddMath.Frontier.NilHeckeSmallRankControls` (hand checks, already
compiled). This module closes the boundaries with exact statements, each with a
genuine consumer (the audit module type-checks every declaration below).

N = 0: the presented algebra is the base ring (`presentedZeroBase`), the
polynomial grading collapses (`polynomial_piece_zero`,
`polynomial_piece_zero_top`), endomorphisms are scalars (`end_zero_is_scalar`),
and the physical rank is 1 (`physical_rank_zero`).

N = 1: the relation ideal vanishes (`relIdeal_one`), the degree-2d fiber over a
single generator is classified (`fiber_neg_empty`, `fiber_odd_empty`,
`fiber_even_unique`), the dot action goes source -> action
(`source_action_mem`) and back (`action_source_mem`, hence `degree_equiv`),
the 1x1 shift matrix carries no shift (`matrix_entry_degree`), and the physical
rank is 1 (`physical_rank_one`).

No formal Laurent series is constructed anywhere: coefficient reading goes
through the inherited `PbwEquivalence.coefficientEquiv` / `orderedBasis`
(`coord_read_zero`, `coord_read_one`). -/
namespace OddMath.Frontier.NilHeckeSmallRank

open scoped BigOperators

/-! ## N = 0: the presented algebra is the base ring. -/

/-- N = 0: the relation ideal vanishes (controls supply the empty relator set). -/
theorem relIdeal_zero : OddMath.PbwL2.relIdeal 0 = ⊥ := by
  rw [OddMath.PbwL2.ideal_is_span,
    OddMath.Frontier.NilHeckeSmallRankControls.relSet_empty_zero,
    bot_unique (TwoSidedIdeal.span_le.mpr (Set.empty_subset _)),
    TwoSidedIdeal.bot_asIdeal]

/-- N = 0: the quotient map is injective because the relation ideal vanishes. -/
theorem mk_zero_injective :
    Function.Injective (Ideal.Quotient.mk (OddMath.PbwL2.relIdeal 0)) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  rw [Ideal.Quotient.eq_zero_iff_mem, relIdeal_zero] at hx
  exact (Ideal.mem_bot).mp hx

/-- N = 0: quotienting by the vanishing ideal does nothing. -/
noncomputable def presented_zero_equiv :
    OddMath.PbwL2.Presented 0 ≃+* FreeAlgebra ℤ (Fin 0) :=
  (RingEquiv.ofBijective (Ideal.Quotient.mk (OddMath.PbwL2.relIdeal 0))
    ⟨mk_zero_injective, Ideal.Quotient.mk_surjective⟩).symm

/-- N = 0: the free algebra on no generators retracts onto the scalars. -/
theorem freeZero_leftInv :
    Function.LeftInverse (algebraMap ℤ (FreeAlgebra ℤ (Fin 0)))
      ⇑(FreeAlgebra.lift ℤ (fun i : Fin 0 => i.elim0)) := by
  intro x
  induction x using FreeAlgebra.induction with
  | grade0 r => simp [AlgHom.commutes]
  | grade1 i => exact i.elim0
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- N = 0: the retraction is right-inverse on scalars. -/
theorem freeZero_rightInv :
    Function.RightInverse (algebraMap ℤ (FreeAlgebra ℤ (Fin 0)))
      ⇑(FreeAlgebra.lift ℤ (fun i : Fin 0 => i.elim0)) := by
  intro r
  simp [AlgHom.commutes]

/-- N = 0: the free algebra on no generators is the base ring as algebras. -/
noncomputable def freeZeroAlgEquiv : FreeAlgebra ℤ (Fin 0) ≃ₐ[ℤ] ℤ :=
  AlgEquiv.ofBijective (FreeAlgebra.lift ℤ (fun i : Fin 0 => i.elim0))
    ⟨freeZero_leftInv.injective, freeZero_rightInv.surjective⟩

/-- N = 0: the presented algebra IS the base ring. -/
noncomputable def presentedZeroBase : OddMath.PbwL2.Presented 0 ≃+* ℤ :=
  presented_zero_equiv.trans freeZeroAlgEquiv.toRingEquiv

/-- N = 0: every presented element comes from a scalar through the base iso. -/
theorem presented_zero_scalar (a : OddMath.PbwL2.Presented 0) :
    ∃ n : ℤ, a = presentedZeroBase.symm n :=
  ⟨presentedZeroBase a, (RingEquiv.apply_symm_apply _ _).symm⟩

/-- N = 0: the presented module has rank one (PBW fiber over the empty word). -/
theorem finrank_presented_zero :
    Module.finrank ℤ (OddMath.PbwL2.Presented 0) = 1 := by
  haveI : IsEmpty (Fin 0) := ⟨Fin.elim0⟩
  haveI := Unique.fintype (α := Fin 0 → ℕ)
  rw [Module.finrank_eq_card_basis
    (OddMath.Frontier.PbwEquivalence.orderedBasis 0), Fintype.card_unique]

/-- N = 0: endomorphisms form a rank-one module (1x1 matrices over scalars). -/
theorem finrank_end_zero :
    Module.finrank ℤ (Module.End ℤ (OddMath.PbwL2.Presented 0)) = 1 := by
  haveI : IsEmpty (Fin 0) := ⟨Fin.elim0⟩
  haveI := Unique.fintype (α := Fin 0 → ℕ)
  haveI := Classical.decEq (Fin 0 → ℕ)
  have h1 := LinearEquiv.finrank_eq (LinearMap.toMatrix
    (OddMath.Frontier.PbwEquivalence.orderedBasis 0)
    (OddMath.Frontier.PbwEquivalence.orderedBasis 0))
  rw [Module.finrank_matrix, Fintype.card_unique, Module.finrank_self] at h1
  show Module.finrank ℤ
    (OddMath.PbwL2.Presented 0 →ₗ[ℤ] OddMath.PbwL2.Presented 0) = 1
  simpa using h1

/-- N = 0: scalar preimages are integer multiples of one. -/
theorem scalar_preimage_smul (n : ℤ) :
    presentedZeroBase.symm n = n • (1 : OddMath.PbwL2.Presented 0) := by
  have h : presentedZeroBase.symm (n : ℤ) =
      ((n : ℤ) : OddMath.PbwL2.Presented 0) := map_intCast _ n
  rw [h, zsmul_eq_mul, mul_one]

/-- N = 0: every module endomorphism is right-multiplication by its value at
one (the graded picture is trivially exact: scalars in the unique piece act as
scalars, and there is nothing else). -/
theorem end_zero_is_scalar (T : Module.End ℤ (OddMath.PbwL2.Presented 0)) :
    ∃ c : OddMath.PbwL2.Presented 0, ∀ a, T a = c * a := by
  refine ⟨T 1, fun a => ?_⟩
  obtain ⟨n, rfl⟩ := presented_zero_scalar a
  rw [scalar_preimage_smul n, map_zsmul, zsmul_eq_mul, zsmul_eq_mul, mul_one]
  exact (Int.cast_commute n (T 1)).eq

/-! ## N = 0: the polynomial grading collapses. -/

/-- N = 0: every nonzero-degree piece vanishes (controls: all pdegrees are 0). -/
theorem polynomial_piece_zero {d : ℤ} (hd : d ≠ 0) :
    OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 0 d = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  exact Finsupp.ext fun a => hf a (by
    rw [OddMath.Frontier.NilHeckeSmallRankControls.pdegree_zero_all a]
    exact Ne.symm hd)

/-- N = 0: the degree-zero piece is everything. -/
theorem polynomial_piece_zero_top :
    OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 0 0 = ⊤ := by
  rw [eq_top_iff]
  intro f _
  intro a ha
  exact absurd (OddMath.Frontier.NilHeckeSmallRankControls.pdegree_zero_all a) ha

/-- N = 0: coordinates read through the inherited PBW basis. -/
theorem coord_read_zero (x : OddMath.PbwL2.Presented 0) :
    (OddMath.Frontier.PbwEquivalence.orderedBasis 0).repr x =
      OddMath.PbwL3.Phi 0 x :=
  OddMath.Frontier.PbwEquivalence.orderedBasis_repr x

/-- N = 0 physical rank: the inversion generating sum over the trivial group
is 1 (specialization of `NilHeckeGrading.inversion_generating` at m = 0). -/
theorem physical_rank_zero {R : Type*} [CommSemiring R] (q : R) :
    (∑ w : Equiv.Perm (Fin 0), q ^ (2 * OddMath.Frontier.NilHeckeGrading.inversions w)) = 1 := by
  have h := OddMath.Frontier.NilHeckeGrading.inversion_generating (q ^ 2) 0 (R := R)
  rw [Finset.prod_range_zero] at h
  simpa only [pow_mul] using h

/-! ## N = 1: the relation ideal vanishes. -/

/-- N = 1: the relation ideal vanishes (controls supply the empty relator set;
the negative control `no_distinct_generators_one` says no relator can fire). -/
theorem relIdeal_one : OddMath.PbwL2.relIdeal 1 = ⊥ := by
  rw [OddMath.PbwL2.ideal_is_span,
    OddMath.Frontier.NilHeckeSmallRankControls.relSet_empty_one,
    bot_unique (TwoSidedIdeal.span_le.mpr (Set.empty_subset _)),
    TwoSidedIdeal.bot_asIdeal]

/-- N = 1: the quotient map is injective because the relation ideal vanishes. -/
theorem mk_one_injective :
    Function.Injective (Ideal.Quotient.mk (OddMath.PbwL2.relIdeal 1)) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  rw [Ideal.Quotient.eq_zero_iff_mem, relIdeal_one] at hx
  exact (Ideal.mem_bot).mp hx

/-- N = 1: quotienting by the vanishing ideal does nothing (the presented
single-dot algebra is the free algebra on one generator). -/
noncomputable def presented_one_equiv_free :
    OddMath.PbwL2.Presented 1 ≃+* FreeAlgebra ℤ (Fin 1) :=
  (RingEquiv.ofBijective (Ideal.Quotient.mk (OddMath.PbwL2.relIdeal 1))
    ⟨mk_one_injective, Ideal.Quotient.mk_surjective⟩).symm

/-- N = 1: relator index pairs are vacuous (consumer of the controls version). -/
theorem relPairs_one_vacuous (p : Fin 1 × Fin 1) :
    p ∉ OddMath.PbwL2.relPairs 1 := by
  rw [OddMath.Frontier.NilHeckeSmallRankControls.relPairs_empty_one]
  exact Finset.not_mem_empty p

/-- N = 1: the PBW comparison map is bijective (entry point to the inherited
equivalence; consumed by the degree correspondence below). -/
theorem phi_one_bijective : Function.Bijective (OddMath.PbwL3.Phi 1) :=
  OddMath.Frontier.PbwEquivalence.Phi_bijective 1

/-- N = 1: coordinates read through the inherited PBW basis. -/
theorem coord_read_one (x : OddMath.PbwL2.Presented 1) :
    (OddMath.Frontier.PbwEquivalence.orderedBasis 1).repr x =
      OddMath.PbwL3.Phi 1 x :=
  OddMath.Frontier.PbwEquivalence.orderedBasis_repr x

/-- N = 1: polynomial degree counts the single generator twice. -/
theorem pdegree_one (a : Fin 1 → ℕ) :
    OddMath.Frontier.NilHeckeGradedEnd.pdegree a = 2 * ((a 0 : ℕ) : ℤ) := by
  simp [OddMath.Frontier.NilHeckeGradedEnd.pdegree, Fin.sum_univ_one]

/-- N = 1: the degree-`d` fiber over the single generator. -/
def fiber (d : ℤ) : Type :=
  { a : Fin 1 → ℕ // OddMath.Frontier.NilHeckeGradedEnd.pdegree a = d }

/-- N = 1: negative-degree fibers are empty. -/
theorem fiber_neg_empty {d : ℤ} (hd : d < 0) : IsEmpty (fiber d) := by
  refine ⟨fun ⟨a, ha⟩ => ?_⟩
  rw [pdegree_one] at ha
  omega

/-- N = 1: odd-degree fibers are empty (parity control). -/
theorem fiber_odd_empty {d : ℤ} (hd : d % 2 ≠ 0) : IsEmpty (fiber d) := by
  refine ⟨fun ⟨a, ha⟩ => ?_⟩
  rw [pdegree_one] at ha
  omega

/-- N = 1: even-degree fibers hold exactly the expected monomial. -/
def fiber_even_unique (k : ℕ) : Unique (fiber (2 * (k : ℤ))) := by
  refine ⟨⟨fun _ => k, ?_⟩, fun ⟨a, ha⟩ => ?_⟩
  · simp [pdegree_one]
  · apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    have h0 : a 0 = k := by
      apply Nat.cast_injective (R := ℤ)
      have h2 : (2 : ℤ) * ((a 0 : ℕ) : ℤ) = 2 * (k : ℤ) := by
        rw [← pdegree_one a]
        exact ha
      omega
    calc a i = a 0 := by rw [hi]
      _ = k := h0
      _ = (fun _ => k) i := rfl

/-! ## N = 1: the dot action and the degree correspondence. -/

/-- N = 1: the dot piece is the span of the fiber monomials. -/
def dotPiece (d : ℤ) : Submodule ℤ (OddMath.PbwL2.Presented 1) :=
  Submodule.span ℤ (Set.range
    (fun a : fiber d =>
      OddMath.Frontier.PbwNormalization.orderedMonomial (a.val)))

/-- N = 1: fiber monomials land in the dot piece. -/
theorem fiber_basis_mem (d : ℤ) (a : Fin 1 → ℕ)
    (ha : OddMath.Frontier.NilHeckeGradedEnd.pdegree a = d) :
    OddMath.Frontier.PbwNormalization.orderedMonomial a ∈ dotPiece d :=
  Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩

/-- N = 1: the fiber monomials are linearly independent (restriction of the
inherited PBW basis along the subtype inclusion). -/
theorem fiber_linear_independent (d : ℤ) :
    LinearIndependent ℤ (fun a : fiber d =>
      OddMath.Frontier.PbwNormalization.orderedMonomial (a.val)) := by
  have h := LinearIndependent.comp
    (OddMath.Frontier.PbwEquivalence.orderedBasis 1).linearIndependent
    (fun a : fiber d => (a.val)) Subtype.val_injective
  have he : (fun a : fiber d =>
      OddMath.Frontier.PbwNormalization.orderedMonomial (a.val)) =
      ⇑(OddMath.Frontier.PbwEquivalence.orderedBasis 1) ∘
        (fun a : fiber d => a.val) := by
    funext a
    exact (OddMath.Frontier.PbwEquivalence.orderedBasis_apply a.val).symm
  rw [he]
  exact h

/-- N = 1: every dot-piece element is a finite combination of fiber monomials. -/
theorem fiber_spanning (d : ℤ) (x : OddMath.PbwL2.Presented 1)
    (hx : x ∈ dotPiece d) :
    ∃ c : fiber d →₀ ℤ,
      x = c.sum (fun a r =>
        r • OddMath.Frontier.PbwNormalization.orderedMonomial (a.val)) := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (show x ∈ Submodule.span ℤ _ from hx)
  exact ⟨c, hc.symm⟩

/-- N = 1: the dot generator maps into polynomial degree 2 (consumes both the
action-hit and the degree controls). -/
theorem dot_action_generator (i : Fin 1) :
    OddMath.PbwL3.Phi 1 (OddMath.PbwL2.q 1 i) ∈
      OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 1 2 := by
  rw [OddMath.Frontier.NilHeckeSmallRankControls.single_action_hits_generator i]
  exact OddMath.Frontier.NilHeckeSmallRankControls.single_generator_degree_two i

/-- N = 1, source -> action: the dot action sends dot-piece `d` times
polynomial-piece `e` into polynomial-piece `d + e`. This is the actual
polynomial action at rank one, by span induction on the dot piece using the
inherited `monomial_mem` / `polynomial_mul` laws. -/
theorem source_action_mem {d e : ℤ} {a : OddMath.PbwL2.Presented 1}
    (ha : a ∈ dotPiece d) {f : OddMath.SkewPolynomial.SkewPolynomial 1}
    (hf : f ∈ OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 1 e) :
    OddMath.PbwL3.Phi 1 a * f ∈
      OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 1 (d + e) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    show OddMath.PbwL3.Phi 1
        (OddMath.Frontier.PbwNormalization.orderedMonomial (u.val)) * f ∈ _
    rw [OddMath.Frontier.PbwEquivalence.Phi_orderedMonomial]
    have h1 : OddMath.SkewPolynomial.monomial (u.val) 1 ∈
        OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 1 d := by
      have hb : OddMath.Frontier.NilHeckeGradedEnd.pdegree (u.val) = d :=
        u.property
      have hm := OddMath.Frontier.NilHeckeGradedEnd.monomial_mem (u.val) 1
      rwa [hb] at hm
    exact OddMath.Frontier.NilHeckeGradedEnd.polynomial_mul h1 hf
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, add_mul]
    exact (OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 1
      (d + e)).add_mem hx hy
  | smul z x _ hx =>
    rw [map_zsmul, smul_mul_assoc]
    exact (OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 1
      (d + e)).smul_mem z hx

/-- N = 1, action -> source, key step: the PBW lift sends polynomial-piece `d`
back into dot-piece `d`, by support expansion (`support_degree` pins every
support exponent to degree `d`). -/
theorem lift_mem_dotPiece {d : ℤ} (g : OddMath.SkewPolynomial.SkewPolynomial 1)
    (hg : g ∈ OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 1 d) :
    OddMath.Frontier.PbwEquivalence.lift 1 g ∈ dotPiece d := by
  rw [OddMath.Frontier.PbwEquivalence.lift_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro b hb
  have hdeg : OddMath.Frontier.NilHeckeGradedEnd.pdegree b = d :=
    OddMath.Frontier.NilHeckeGradedEnd.support_degree hg hb
  exact (dotPiece d).smul_mem _ (fiber_basis_mem d b hdeg)

/-- N = 1, action -> source: polynomial-piece membership pulls back along the
comparison map (via the lift section `lift_Phi`). -/
theorem action_source_mem {d : ℤ} {a : OddMath.PbwL2.Presented 1}
    (ha : OddMath.PbwL3.Phi 1 a ∈
      OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 1 d) :
    a ∈ dotPiece d := by
  have h := lift_mem_dotPiece _ ha
  rwa [OddMath.Frontier.PbwEquivalence.lift_Phi] at h

/-- N = 1 degree correspondence: dot-piece membership is exactly
polynomial-piece membership after the comparison map. -/
theorem degree_equiv (d : ℤ) (a : OddMath.PbwL2.Presented 1) :
    a ∈ dotPiece d ↔ OddMath.PbwL3.Phi 1 a ∈
      OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 1 d := by
  constructor
  · intro ha
    have h1 := source_action_mem ha
      (OddMath.Frontier.NilHeckeGradedEnd.one_mem 1)
    simpa using h1
  · exact action_source_mem

/-! ## N = 1: the shift matrix and the physical rank. -/

/-- N = 1: the dot/MNS matrix is 1x1 over the trivial group, all entries the
comparison image. -/
noncomputable def shiftMatrix (a : OddMath.PbwL2.Presented 1) :
    Matrix (Equiv.Perm (Fin 1)) (Equiv.Perm (Fin 1))
      (OddMath.SkewPolynomial.SkewPolynomial 1) :=
  Matrix.of fun _ _ => OddMath.PbwL3.Phi 1 a

/-- N = 1: every length shift vanishes (the rank-one symmetric group is
trivial; consumes the Schubert triviality control). -/
theorem shift_vanish (d : ℤ) (i j : Equiv.Perm (Fin 1)) :
    d + 2 * ((OddMath.Frontier.NilHeckeGrading.inversions j : ℕ) : ℤ)
      - 2 * ((OddMath.Frontier.NilHeckeGrading.inversions i : ℕ) : ℤ) = d := by
  rw [OddMath.Frontier.NilHeckeSmallRankControls.schubert_one_trivial i,
    OddMath.Frontier.NilHeckeSmallRankControls.schubert_one_trivial j,
    add_sub_cancel_right]

/-- N = 1 matrix entry degree law: dot-piece `d` holds exactly when every
shifted matrix entry sits in the correspondingly shifted polynomial piece. -/
theorem matrix_entry_degree (d : ℤ) (a : OddMath.PbwL2.Presented 1) :
    a ∈ dotPiece d ↔ ∀ i j, shiftMatrix a i j ∈
      OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 1
        (d + 2 * ((OddMath.Frontier.NilHeckeGrading.inversions j : ℕ) : ℤ)
          - 2 * ((OddMath.Frontier.NilHeckeGrading.inversions i : ℕ) : ℤ)) := by
  constructor
  · intro ha i j
    rw [shift_vanish d i j]
    show OddMath.PbwL3.Phi 1 a ∈ _
    exact (degree_equiv d a).mp ha
  · intro h
    apply (degree_equiv d a).mpr
    have h11 := h 1 1
    rw [shift_vanish d 1 1] at h11
    exact h11

/-- N = 1 physical rank: the inversion generating sum over the trivial group
is 1 (specialization of `NilHeckeGrading.inversion_generating` at m = 1). -/
theorem physical_rank_one {R : Type*} [CommSemiring R] (q : R) :
    (∑ w : Equiv.Perm (Fin 1), q ^ (2 * OddMath.Frontier.NilHeckeGrading.inversions w)) = 1 := by
  have h := OddMath.Frontier.NilHeckeGrading.inversion_generating (q ^ 2) 1 (R := R)
  rw [Finset.prod_range_one, Finset.sum_range_one, pow_zero] at h
  simpa only [pow_mul] using h

end OddMath.Frontier.NilHeckeSmallRank

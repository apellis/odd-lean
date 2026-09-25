import OddMath.Frontier.EKPresentation
import OddMath.Frontier.CompleteTableauExpansion
import OddMath.Frontier.ElementaryRelations
import OddMath.Frontier.OddSymmetrizer

/-! Ellis 1111.3932v1 §2.1 and Theorem 3.8 (first part), on the actual EK carrier.

* `piN N : Q →+* SkewPolynomial N` is the ring map from the existing EK integer quotient
  `Q = EKRadicalQuotient.Q` sending `h_k ↦ completePoly N k` (Ellis §2.1
  `h_k = Σ_{i₁≤…≤i_k} x̃_{i₁}⋯x̃_{i_k}`). It is built by descending the free-algebra complete
  evaluation through the existing EK presentation `EKPresentation.presentationEquiv`
  (EK Cor 2.13, h-generators, relations (2.11)/(2.12)).
* The EK relations for the complete polynomials (`complete_even`, `complete_odd`) are PROVED,
  not assumed: the literal elementary sums satisfy EKL Lemma 2.3 (`ElementaryRelations`),
  so the elementary specialisation descends through the existing e-presentation
  `EKPresentation.elementaryPresentationEquiv`; the resulting map agrees with the complete
  evaluation on every free element (`ePi_pi`, via the EK generator change and the proved
  finite-alphabet e/h inversion `completeEvaluation_elementary`), which kills every relator.
* `schurK d = KostkaModuleInversion.recover d (degreeHBasis d)` is EK's `s_λ` in the actual
  degree piece of `Q`: the unique solution of (3.6) `h_μ = Σ_λ K_{λμ} s_λ` with
  `K = TableauDominance.signedKostka` (`schurK_defining`, `schurK_unique`).
  (This is the same expression as `EKSchurOrthonormal.schur`.)
* `piN_schurK`: `piN N (s_λ) = CompleteTableauExpansion.sp N λ` for every λ and every N.
* `thm38_conditional`: labelled CONDITIONAL on `EliminationC` (discharged in `OddLRThm38`).
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace OddMath.Frontier.OddLREKIdentification
open OddMath.SkewPolynomial FiniteCompleteElementary DegreeShapes
open CompleteElementary (A)
open EKRadicalQuotient (Q pi)

/-! ## Generic descent helpers -/

theorem ringHom_ext_free {R : Type*} [Ring R] (f g : A →+* R)
    (h : ∀ i, f (FreeAlgebra.ι ℤ i) = g (FreeAlgebra.ι ℤ i)) : f = g := by
  have hh : f.toIntAlgHom = g.toIntAlgHom := FreeAlgebra.hom_ext (funext h)
  ext x
  exact congrArg (fun φ : A →ₐ[ℤ] R => φ x) hh

theorem killed_of_relators {R : Type*} [Ring R] (f : A →+* R)
    (hf : ∀ r, EKPresentation.Relator r → f r = 0) :
    ∀ r ∈ EKPresentation.relIdeal, f r = 0 := by
  intro r hr
  rw [EKPresentation.relIdeal, EKPresentation.relTwoSided, TwoSidedIdeal.mem_asIdeal] at hr
  induction hr using TwoSidedIdeal.span_induction with
  | mem x hx => exact hf x hx
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]
  | left_absorb a x _ hx => rw [map_mul, hx, MulZeroClass.mul_zero]
  | right_absorb a x _ hx => rw [map_mul, hx, MulZeroClass.zero_mul]

/-! ## The elementary specialisation and its descent (EKL Lemma 2.3 input) -/

def elementaryEvaluation (N : ℕ) : A →+* SkewPolynomial N :=
  (FreeAlgebra.lift ℤ (fun i => elementaryPoly N (i + 1))).toRingHom

@[simp] theorem elementaryEvaluation_h (N k : ℕ) :
    elementaryEvaluation N (CompleteElementary.h k) = elementaryPoly N k := by
  cases k with
  | zero => simp [elementaryEvaluation]
  | succ k => exact FreeAlgebra.lift_ι_apply _ k

theorem elementary_relator (N : ℕ) {r : A} (hr : EKPresentation.Relator r) :
    elementaryEvaluation N r = 0 := by
  cases hr with
  | even a b hab =>
    rw [map_sub, map_mul, map_mul, elementaryEvaluation_h, elementaryEvaluation_h, sub_eq_zero]
    exact ElementaryRelations.elementary_even N a b hab
  | odd a b hb hab =>
    cases b with
    | zero => omega
    | succ b =>
      have he : Even (a+b) := by
        rw [Nat.even_iff]; have := Nat.odd_iff.mp hab; omega
      simp only [map_sub, map_add, map_mul, map_zsmul, elementaryEvaluation_h,
        Nat.add_sub_cancel, sub_eq_zero]
      exact ElementaryRelations.elementary_odd N a b he

/-- The elementary specialisation factors through EK's generator change h ↦ e. -/
theorem elementaryEvaluation_eq (N : ℕ) :
    elementaryEvaluation N =
      (completeEvaluation N).comp CompleteChangeOfGenerators.completeToElementary.toRingHom := by
  apply ringHom_ext_free
  intro i
  have h1 := elementaryEvaluation_h N (i+1)
  have h2 : completeEvaluation N (CompleteChangeOfGenerators.completeToElementary
      (CompleteElementary.h (i+1))) = elementaryPoly N (i+1) := by
    rw [CompleteChangeOfGenerators.completeToElementary_h, completeEvaluation_elementary]
  exact h1.trans h2.symm

def elementaryDescent (N : ℕ) : EKPresentation.Presented →+* SkewPolynomial N :=
  Ideal.Quotient.lift EKPresentation.relIdeal (elementaryEvaluation N)
    (killed_of_relators _ (fun _ hr => elementary_relator N hr))

/-- Descent of the elementary specialisation along the existing e-presentation of Q. -/
def ePi (N : ℕ) : Q →+* SkewPolynomial N :=
  (elementaryDescent N).comp EKPresentation.elementaryPresentationEquiv.symm.toRingHom

theorem elementaryPresentation_mk (y : A) :
    EKPresentation.elementaryPresentationEquiv (EKPresentation.mk y) =
      pi (CompleteChangeOfGenerators.completeToElementary y) := by
  rw [← EKPresentation.psi1_pi, ← EKPresentation.toQ_mk, EKPresentation.psi1_toQ]
  rfl

theorem ePi_pi (N : ℕ) (x : A) : ePi N (pi x) = completeEvaluation N x := by
  have hx : EKPresentation.elementaryPresentationEquiv.symm (pi x) =
      EKPresentation.mk (CompleteChangeOfGenerators.elementaryToComplete x) := by
    apply EKPresentation.elementaryPresentationEquiv.injective
    rw [RingEquiv.apply_symm_apply, elementaryPresentation_mk]
    have hh := congrArg (fun f : A →ₐ[ℤ] A => f x)
      CompleteChangeOfGenerators.completeToElementary_comp_elementaryToComplete
    exact congrArg pi hh.symm
  change elementaryDescent N (EKPresentation.elementaryPresentationEquiv.symm (pi x)) = _
  rw [hx]
  change elementaryEvaluation N (CompleteChangeOfGenerators.elementaryToComplete x) = _
  rw [elementaryEvaluation_eq]
  change completeEvaluation N (CompleteChangeOfGenerators.completeToElementary
    (CompleteChangeOfGenerators.elementaryToComplete x)) = _
  have hh := congrArg (fun f : A →ₐ[ℤ] A => f x)
    CompleteChangeOfGenerators.completeToElementary_comp_elementaryToComplete
  exact congrArg (completeEvaluation N) hh

/-! ## EK relations (2.11)/(2.12) for the complete polynomials -/

theorem complete_relator (N : ℕ) {r : A} (hr : EKPresentation.Relator r) :
    completeEvaluation N r = 0 := by
  have hz : pi r = 0 := by
    have hm : EKPresentation.mk r = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change r ∈ EKPresentation.relTwoSided.asIdeal
      rw [TwoSidedIdeal.mem_asIdeal]
      exact TwoSidedIdeal.subset_span hr
    rw [← EKPresentation.toQ_mk, hm, map_zero]
  rw [← ePi_pi, hz, map_zero]

/-- EK (2.11) for Ellis' complete polynomials in every finite alphabet. -/
theorem complete_even (N a b : ℕ) (hab : Even (a+b)) :
    completePoly N a * completePoly N b = completePoly N b * completePoly N a := by
  have h := complete_relator N (EKPresentation.Relator.even a b hab)
  simpa only [map_sub, map_mul, completeEvaluation_h, sub_eq_zero] using h

/-- EK (2.12) for Ellis' complete polynomials in every finite alphabet. -/
theorem complete_odd (N a b : ℕ) (hb : 0 < b) (hab : Odd (a+b)) :
    completePoly N a * completePoly N b + (-1 : ℤ)^a • (completePoly N b * completePoly N a) =
      (-1 : ℤ)^a • (completePoly N (a+1) * completePoly N (b-1)) +
        completePoly N (b-1) * completePoly N (a+1) := by
  have h := complete_relator N (EKPresentation.Relator.odd a b hb hab)
  simpa only [map_sub, map_add, map_mul, map_zsmul, completeEvaluation_h, sub_eq_zero] using h

/-! ## The map π_N : Q → OΛ_N ⊂ OPol_N, via the h-presentation -/

def completeDescent (N : ℕ) : EKPresentation.Presented →+* SkewPolynomial N :=
  Ideal.Quotient.lift EKPresentation.relIdeal (completeEvaluation N)
    (killed_of_relators _ (fun _ hr => complete_relator N hr))

/-- Ellis §2.1: `Q ≅ OΛ → OΛ_N ⊂ OPol_N`, `h_k ↦ h_k`. -/
def piN (N : ℕ) : Q →+* SkewPolynomial N :=
  (completeDescent N).comp EKPresentation.presentationEquiv.symm.toRingHom

theorem piN_pi (N : ℕ) (x : A) : piN N (pi x) = completeEvaluation N x := by
  have hx : EKPresentation.presentationEquiv.symm (pi x) = EKPresentation.mk x := by
    apply EKPresentation.presentationEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  change completeDescent N (EKPresentation.presentationEquiv.symm (pi x)) = _
  rw [hx]
  rfl

@[simp] theorem piN_h (N k : ℕ) : piN N (EKElementaryQuotient.h k) = completePoly N k := by
  rw [EKElementaryQuotient.h, piN_pi, completeEvaluation_h]

@[simp] theorem piN_e (N k : ℕ) : piN N (EKElementaryQuotient.e k) = elementaryPoly N k := by
  rw [EKElementaryQuotient.e, piN_pi, completeEvaluation_elementary]

/-- Both descents are the same ring map (h-route = e-route). -/
theorem piN_eq_ePi (N : ℕ) : piN N = ePi N := by
  refine RingHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := EKRadicalQuotient.pi_surjective y
  rw [piN_pi, ePi_pi]

/-- Uniqueness: π_N is the only ring map Q → OPol_N with h_k ↦ h_k. -/
theorem piN_unique (N : ℕ) (f : Q →+* SkewPolynomial N)
    (hf : ∀ k, f (EKElementaryQuotient.h k) = completePoly N k) : f = piN N := by
  have hc : f.comp pi = (piN N).comp pi := by
    apply ringHom_ext_free
    intro i
    have := hf (i+1)
    simp only [RingHom.comp_apply]
    rw [show FreeAlgebra.ι ℤ i = CompleteElementary.h (i+1) from rfl]
    rw [show pi (CompleteElementary.h (i+1)) = EKElementaryQuotient.h (i+1) from rfl, this, piN_h]
  refine RingHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := EKRadicalQuotient.pi_surjective y
  exact congrArg (fun φ : A →+* SkewPolynomial N => φ x) hc

/-- The image lies in the odd symmetric polynomials `OΛ_N` (joint kernel), N = n+2. -/
theorem piN_mem_kernel (n : ℕ) (y : Q) : piN (n+2) y ∈ OddSymmetricKernel.kernelSubring n := by
  obtain ⟨x, rfl⟩ := EKRadicalQuotient.pi_surjective y
  rw [piN_pi]
  induction x using FreeAlgebra.induction with
  | grade0 r =>
    rw [algebraMap_int_eq, eq_intCast, map_intCast]
    exact intCast_mem _ r
  | grade1 i =>
    rw [completeEvaluation_generator]
    exact OddSymmetricKernel.complete_mem n (i+1)
  | mul a b ha hb => rw [map_mul]; exact mul_mem ha hb
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

theorem piN_hPartition (N : ℕ) (μ : YoungDiagram) :
    piN N (EKPartitionSpanning.hPartition μ) = CompleteTableauExpansion.H N μ := by
  simp only [EKPartitionSpanning.hPartition, CompleteTableauExpansion.H, map_list_prod,
    List.map_map, Function.comp_def, piN_h]

/-! ## EK Schur functions (3.6) in the actual degree pieces of Q -/

/-- EK's `s_λ`, degree d: the signed-Kostka inverse of the actual complete basis. -/
def schurK (d : ℕ) : DegreeShape d → EKIntegralBases.degreePiece d :=
  KostkaModuleInversion.recover d (EKIntegralBases.degreeHBasis d)

/-- EK (3.6) literally: `h_μ = Σ_λ K_{λμ} s_λ`, `K = signedKostka` (EK (3.7)). -/
theorem schurK_defining (d : ℕ) :
    KostkaModuleInversion.transform d (schurK d) = EKIntegralBases.degreeHBasis d :=
  KostkaModuleInversion.rightInverse d _

/-- (3.6) determines `s` uniquely in the degree piece. -/
theorem schurK_unique (d : ℕ) (S : DegreeShape d → EKIntegralBases.degreePiece d)
    (hS : KostkaModuleInversion.transform d S = EKIntegralBases.degreeHBasis d) :
    S = schurK d := by
  unfold schurK
  rw [← hS]
  exact (KostkaModuleInversion.leftInverse d S).symm

/-- EK `s_λ` for an arbitrary Young diagram, as an element of Q. -/
def sK (lam : YoungDiagram) : Q := (schurK lam.card ⟨lam, rfl⟩ : Q)

theorem recover_natural {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (f : V →+ W) (d : ℕ) (H : DegreeShape d → V) (i : DegreeShape d) :
    f (KostkaModuleInversion.recover d H i) = KostkaModuleInversion.recover d (f ∘ H) i := by
  simp only [KostkaModuleInversion.recover, map_sum, map_zsmul, Function.comp_apply]

/-- MAIN: Ellis Thm 3.8 first part on the actual carriers, `π_N s^K_λ = s^p_λ`. -/
theorem piN_schurK (N d : ℕ) (lam : DegreeShape d) :
    piN N (schurK d lam : Q) = CompleteTableauExpansion.sp N lam.val := by
  let f : EKIntegralBases.degreePiece d →+ SkewPolynomial N :=
    (piN N).toAddMonoidHom.comp (EKIntegralBases.degreePiece d).subtype.toAddMonoidHom
  have h1 := recover_natural f d (EKIntegralBases.degreeHBasis d) lam
  have h2 : f ∘ EKIntegralBases.degreeHBasis d =
      fun mu : DegreeShape d => CompleteTableauExpansion.H N mu.val := by
    funext mu
    change piN N (EKIntegralBases.degreeHBasis d mu : Q) = _
    rw [EKIntegralBases.degreeHBasis_apply, piN_hPartition]
  rw [h2, CompleteTableauExpansion.sp_recovered] at h1
  exact h1

theorem piN_sK (N : ℕ) (lam : YoungDiagram) :
    piN N (sK lam) = CompleteTableauExpansion.sp N lam :=
  piN_schurK N lam.card ⟨lam, rfl⟩

/-! ## CONDITIONAL corollary: Thm 3.8 (3.9) on the actual carriers -/

/-- The obvious row-length bridge `YoungDiagram → PartitionExponent n` (N = n+2 variables). -/
def toExponent (n : ℕ) (lam : YoungDiagram) : OddSymmetrizer.PartitionExponent n :=
  ⟨fun i => lam.rowLen i.val, fun _ _ hij => lam.rowLen_anti _ _ hij⟩

/-- NAMED HYPOTHESIS = `OddLRElimination` part (c) as fixed in the specification:
`sp λ = schur λ` for every partition λ with at most N = n+2 rows, via the row-length bridge.
NOT proved here. -/
def EliminationC (n : ℕ) : Prop :=
  ∀ lam : YoungDiagram, lam.colLen 0 ≤ n + 2 →
    CompleteTableauExpansion.sp (n+2) lam = OddSymmetrizer.schur n (toExponent n lam)

/-- CONDITIONAL on `EliminationC n`:
`π_N s^K_λ = s^p_λ = s^s_λ`, N = n+2, for every λ with at most N rows. -/
theorem thm38_conditional (n : ℕ) (hc : EliminationC n) (lam : YoungDiagram)
    (hl : lam.colLen 0 ≤ n + 2) :
    piN (n+2) (sK lam) = CompleteTableauExpansion.sp (n+2) lam ∧
      CompleteTableauExpansion.sp (n+2) lam = OddSymmetrizer.schur n (toExponent n lam) :=
  ⟨piN_sK (n+2) lam, hc lam hl⟩

end OddMath.Frontier.OddLREKIdentification

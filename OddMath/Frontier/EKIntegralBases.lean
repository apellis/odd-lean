import OddMath.Frontier.EKPartitionSpanning
import OddMath.Frontier.EKSemiorthogonality
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! EK 1107.5610v2 p15 Corollary 2.12, over ℤ only.
The carrier is the inherited radical quotient, and degreePiece is defined
using images of free-h words of their actual total weight. -/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKIntegralBases
open EKRadicalQuotient EKFreeCoproduct
open EKPartitionSpanning (hPartition ePartition word)

theorem hPartition_identification (μ : YoungDiagram) :
    hPartition μ = EKSemiorthogonality.hPartition μ := rfl
theorem ePartition_identification (μ : YoungDiagram) :
    ePartition μ = EKSemiorthogonality.ePartition μ := rfl

/-- Literal complete-partition basis of the actual quotient. -/
def hBasis : Basis YoungDiagram ℤ Q :=
  Basis.mk EKSemiorthogonality.hPartition_linearIndependent
    (by rw [show EKSemiorthogonality.hPartition = hPartition from rfl,
      EKPartitionSpanning.h_span])
/-- Literal elementary-partition basis of the actual quotient. -/
def eBasis : Basis YoungDiagram ℤ Q :=
  Basis.mk EKSemiorthogonality.ePartition_linearIndependent
    (by rw [show EKSemiorthogonality.ePartition = ePartition from rfl,
      EKPartitionSpanning.e_span])

@[simp] theorem hBasis_apply (μ : YoungDiagram) : hBasis μ = hPartition μ :=
  Basis.mk_apply _ _ _
@[simp] theorem eBasis_apply (μ : YoungDiagram) : eBasis μ = ePartition μ :=
  Basis.mk_apply _ _ _

@[simp] theorem h_coordinates_partition (μ : YoungDiagram) :
    hBasis.repr (hPartition μ) = Finsupp.single μ 1 := by
  rw [← hBasis_apply]
  exact hBasis.repr_self μ

@[simp] theorem e_coordinates_partition (μ : YoungDiagram) :
    eBasis.repr (ePartition μ) = Finsupp.single μ 1 := by
  rw [← eBasis_apply]
  exact eBasis.repr_self μ

theorem h_unique_coordinates (x : Q) :
    ∃! a : YoungDiagram →₀ ℤ, a.sum (fun μ z => z • hPartition μ) = x := by
  refine ⟨hBasis.repr x, ?_, ?_⟩
  · simpa only [Finsupp.linearCombination_apply, hBasis_apply] using hBasis.linearCombination_repr x
  · intro a ha
    apply hBasis.repr.symm.injective
    simpa only [LinearEquiv.symm_apply_apply, Basis.repr_symm_apply, Finsupp.linearCombination_apply, hBasis_apply] using ha

theorem e_unique_coordinates (x : Q) :
    ∃! a : YoungDiagram →₀ ℤ, a.sum (fun μ z => z • ePartition μ) = x := by
  refine ⟨eBasis.repr x, ?_, ?_⟩
  · simpa only [Finsupp.linearCombination_apply, eBasis_apply] using eBasis.linearCombination_repr x
  · intro a ha
    apply eBasis.repr.symm.injective
    simpa only [LinearEquiv.symm_apply_apply, Basis.repr_symm_apply, Finsupp.linearCombination_apply, eBasis_apply] using ha

theorem rowLens_sum (μ : YoungDiagram) : μ.rowLens.sum = μ.card := by
  have h := EKPartitionSpanning.card_ofRowLens μ.rowLens μ.rowLens_sorted
  rw [YoungDiagram.ofRowLens_to_rowLens_eq_self] at h
  exact h.symm

/-- Source-defined homogeneous piece, not a coordinate surrogate. -/
def degreePiece (d : ℕ) : Submodule ℤ Q :=
  Submodule.span ℤ (Set.range (fun w : {w : W // degree w = d} => pi (wordBasis w.val)))

/-- Literal degree-partition span, for either color. -/
def partitionPiece (c : Bool) (d : ℕ) : Submodule ℤ Q :=
  Submodule.span ℤ (Set.range (fun μ : DegreeShapes.DegreeShape d => word c μ.val.rowLens))

theorem word_mem_partitionPiece (c : Bool) (α : List ℕ) :
    word c α ∈ partitionPiece c α.sum := EKPartitionSpanning.word_mem_degree_span c α

theorem partitionPiece_mul (c : Bool) {a b : ℕ} {x y : Q}
    (hx : x ∈ partitionPiece c a) (hy : y ∈ partitionPiece c b) :
    x*y ∈ partitionPiece c (a+b) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨ν, rfl⟩ := hy
      rw [← EKPartitionSpanning.word_append]
      have hd : (μ.val.rowLens ++ ν.val.rowLens).sum = a+b := by
        simp [rowLens_sum, μ.property, ν.property]
      simpa only [hd] using word_mem_partitionPiece c (μ.val.rowLens ++ ν.val.rowLens)
    | zero => simp
    | add y z _ _ hy hz => simpa only [mul_add] using (partitionPiece c (a+b)).add_mem hy hz
    | smul r y _ hy => simpa only [mul_smul_comm] using (partitionPiece c (a+b)).smul_mem r hy
  | zero => simp
  | add x z _ _ hx hz => simpa only [add_mul] using (partitionPiece c (a+b)).add_mem hx hz
  | smul r x _ hx => simpa only [smul_mul_assoc] using (partitionPiece c (a+b)).smul_mem r hx

theorem pi_hWord (α : List ℕ) : pi (CompleteElementary.hWord α) = word false α := by
  simp only [CompleteElementary.hWord, map_list_prod, List.map_map]
  rfl

theorem wordBasis_partitionPiece (w : W) :
    pi (wordBasis w) ∈ partitionPiece false (degree w) := by
  rw [← EKPairingAdjoint.vWord_parts w]
  change pi (CompleteElementary.hWord (List.ofFn (EKPairingAdjoint.parts w))) ∈ _
  rw [pi_hWord]
  have hd : (List.ofFn (EKPairingAdjoint.parts w)).sum = degree w := by
    rw [List.sum_ofFn, EKPairingAdjoint.parts_sum]
  simpa only [hd] using word_mem_partitionPiece false (List.ofFn (EKPairingAdjoint.parts w))

theorem hWord_mem_degreePiece (α : List ℕ) : word false α ∈ degreePiece α.sum := by
  rw [← pi_hWord, ← partWord_value]
  exact Submodule.subset_span ⟨⟨partWord α, partWord_degree α⟩, rfl⟩

theorem degreePiece_eq_hPartition_span (d : ℕ) :
    degreePiece d = partitionPiece false d := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    simpa only [w.property] using wordBasis_partitionPiece w.val
  · apply Submodule.span_le.mpr
    rintro _ ⟨μ, rfl⟩
    have hd : μ.val.rowLens.sum = d := by rw [rowLens_sum, μ.property]
    simpa only [hd] using hWord_mem_degreePiece μ.val.rowLens

theorem degreePiece_mul {a b : ℕ} {x y : Q}
    (hx : x ∈ degreePiece a) (hy : y ∈ degreePiece b) : x*y ∈ degreePiece (a+b) := by
  rw [degreePiece_eq_hPartition_span] at hx hy ⊢
  exact partitionPiece_mul false hx hy

theorem one_mem (c : Bool) : (1 : Q) ∈ partitionPiece c 0 :=
  word_mem_partitionPiece c []

theorem generator_mem (c : Bool) (n : ℕ) :
    pi (EKMixedPairing.gen c n) ∈ partitionPiece c n := by
  simpa using word_mem_partitionPiece c [n]

/-- Multiplication by a source sign is scalar multiplication, preserving the piece. -/
theorem sign_mul_mem (S : Submodule ℤ Q) (n : ℕ) {x : Q} (hx : x ∈ S) :
    pi (CompleteElementary.ekSign n) * x ∈ S := by
  have he : pi (CompleteElementary.ekSign n) * x =
      ((-1 : ℤ)^((n+1).choose 2)) • x := by
    simp [CompleteElementary.ekSign, zsmul_eq_mul]
  rw [he]
  exact S.smul_mem _ hx

/-- Elementary generators have the actual h-word degree, with EK's signs. -/
theorem elementary_mem_hPiece (n : ℕ) :
    EKElementaryQuotient.e n ∈ partitionPiece false n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [EKElementaryQuotient.e] using one_mem false
    | succ n =>
      unfold EKElementaryQuotient.e
      rw [CompleteElementary.elementary_succ, map_mul, map_neg, map_sum, neg_mul]
      apply Submodule.neg_mem
      apply sign_mul_mem
      apply Submodule.sum_mem
      intro k _
      simp only [map_mul]
      have hm := partitionPiece_mul false
        (sign_mul_mem _ k (ih k k.isLt)) (generator_mem false (n+1-k))
      have hd : (k : ℕ)+(n+1-k)=n+1 := by omega
      simpa only [hd] using hm

/-- Conversely each complete generator is in the exact elementary degree span. -/
theorem complete_mem_ePiece (n : ℕ) :
    EKElementaryQuotient.h n ∈ partitionPiece true n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [EKElementaryQuotient.h] using one_mem true
    | succ n =>
      unfold EKElementaryQuotient.h
      rw [CompleteChangeOfGenerators.h_succ, map_neg, map_sum]
      apply Submodule.neg_mem
      apply Submodule.sum_mem
      intro j _
      simp only [map_mul]
      have hm := partitionPiece_mul true
        (sign_mul_mem _ (j+1) (generator_mem true (j+1)))
        (ih (n-j) (by omega))
      have hd : ((j : ℕ)+1)+(n-j)=n+1 := by omega
      simpa only [hd] using hm

theorem word_mem_otherPiece (c : Bool) (α : List ℕ) :
    word c α ∈ partitionPiece (!c) α.sum := by
  induction α with
  | nil => exact one_mem (!c)
  | cons n α ih =>
    rw [EKPartitionSpanning.word_cons, List.sum_cons]
    apply partitionPiece_mul (!c) _ ih
    cases c
    · exact complete_mem_ePiece n
    · exact elementary_mem_hPiece n

theorem partitionPiece_color_eq (d : ℕ) : partitionPiece false d = partitionPiece true d := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨μ, rfl⟩
    have hd : μ.val.rowLens.sum = d := by rw [rowLens_sum, μ.property]
    simpa only [hd] using word_mem_otherPiece false μ.val.rowLens
  · rintro _ ⟨μ, rfl⟩
    have hd : μ.val.rowLens.sum = d := by rw [rowLens_sum, μ.property]
    simpa only [hd] using word_mem_otherPiece true μ.val.rowLens

theorem degreePiece_eq_ePartition_span (d : ℕ) :
    degreePiece d = partitionPiece true d :=
  (degreePiece_eq_hPartition_span d).trans (partitionPiece_color_eq d)

/-- Degree-d complete basis, transported only across the proved equality of
actual submodules of Q. -/
def degreeHBasis (d : ℕ) : Basis (DegreeShapes.DegreeShape d) ℤ (degreePiece d) :=
  (Basis.span (EKSemiorthogonality.degree_hPartition_linearIndependent d)).map
    (LinearEquiv.ofEq _ _ (degreePiece_eq_hPartition_span d).symm)

/-- Degree-d elementary basis on exactly the same actual submodule. -/
def degreeEBasis (d : ℕ) : Basis (DegreeShapes.DegreeShape d) ℤ (degreePiece d) :=
  (Basis.span (EKSemiorthogonality.degree_ePartition_linearIndependent d)).map
    (LinearEquiv.ofEq _ _ (degreePiece_eq_ePartition_span d).symm)

@[simp] theorem degreeHBasis_apply (d : ℕ) (μ : DegreeShapes.DegreeShape d) :
    (degreeHBasis d μ : Q) = hPartition μ.val := by
  simp only [degreeHBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
  rfl

@[simp] theorem degreeEBasis_apply (d : ℕ) (μ : DegreeShapes.DegreeShape d) :
    (degreeEBasis d μ : Q) = ePartition μ.val := by
  simp only [degreeEBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
  rfl

instance degree_free (d : ℕ) : Module.Free ℤ (degreePiece d) :=
  Module.Free.of_basis (degreeHBasis d)

instance degree_finite (d : ℕ) : Module.Finite ℤ (degreePiece d) := by
  letI := DegreeShapes.degreeFintype d
  exact Module.Finite.of_basis (degreeHBasis d)

/-- Corollary 2.12's rank: all partitions of d, with no bound on d. -/
theorem degree_finrank (d : ℕ) :
    letI := DegreeShapes.degreeFintype d
    Module.finrank ℤ (degreePiece d) = Fintype.card (DegreeShapes.DegreeShape d) := by
  letI := DegreeShapes.degreeFintype d
  exact Module.finrank_eq_card_basis (degreeHBasis d)

theorem degree_h_unique_coordinates (d : ℕ) (x : degreePiece d) :
    letI := DegreeShapes.degreeFintype d
    ∃! a : DegreeShapes.DegreeShape d → ℤ,
      ∑ μ, a μ • hPartition μ.val = (x : Q) := by
  classical
  letI := DegreeShapes.degreeFintype d
  refine ⟨fun μ => (degreeHBasis d).repr x μ, ?_, ?_⟩
  · have h := congrArg (fun z : degreePiece d => (z : Q)) ((degreeHBasis d).sum_repr x)
    simpa using h
  · intro a ha
    apply (EKSemiorthogonality.degree_hPartition_linearIndependent d).fintypeLinearCombination_injective
    simpa using ha.trans (congrArg (fun z : degreePiece d => (z : Q))
      ((degreeHBasis d).sum_repr x)).symm

theorem degree_e_unique_coordinates (d : ℕ) (x : degreePiece d) :
    letI := DegreeShapes.degreeFintype d
    ∃! a : DegreeShapes.DegreeShape d → ℤ,
      ∑ μ, a μ • ePartition μ.val = (x : Q) := by
  classical
  letI := DegreeShapes.degreeFintype d
  refine ⟨fun μ => (degreeEBasis d).repr x μ, ?_, ?_⟩
  · have h := congrArg (fun z : degreePiece d => (z : Q)) ((degreeEBasis d).sum_repr x)
    simpa using h
  · intro a ha
    apply (EKSemiorthogonality.degree_ePartition_linearIndependent d).fintypeLinearCombination_injective
    simpa using ha.trans (congrArg (fun z : degreePiece d => (z : Q))
      ((degreeEBasis d).sum_repr x)).symm

/-- The actual finite homogeneous decomposition, formed by collecting the
literal h-basis coefficients by their word degree. -/
def decompose : Q →ₗ[ℤ] (ℕ →₀ Q) :=
  hBasis.constr ℤ (fun μ => Finsupp.single μ.card (hPartition μ))

@[simp] theorem decompose_hPartition (μ : YoungDiagram) :
    decompose (hPartition μ) = Finsupp.single μ.card (hPartition μ) := by
  simpa only [hBasis_apply] using hBasis.constr_basis ℤ
    (fun μ => Finsupp.single μ.card (hPartition μ)) μ

/-- Coercion sum back into the original Q. -/
def recompose : (ℕ →₀ Q) →ₗ[ℤ] Q := Finsupp.lsum ℤ (fun _ => LinearMap.id)

@[simp] theorem recompose_apply (f : ℕ →₀ Q) :
    recompose f = f.sum (fun _ x => x) := rfl
@[simp] theorem recompose_single (d : ℕ) (x : Q) :
    recompose (Finsupp.single d x) = x := Finsupp.lsum_single _ _ _ _

theorem recompose_decompose (x : Q) : recompose (decompose x) = x := by
  have he : recompose.comp decompose = LinearMap.id := by
    apply hBasis.ext
    intro μ
    simp
  exact congrArg (fun f : Q →ₗ[ℤ] Q => f x) he

/-- Every homogeneous element goes to its own summand, not to a new grading. -/
theorem decompose_piece {d : ℕ} {x : Q} (hx : x ∈ degreePiece d) :
    decompose x = Finsupp.single d x := by
  rw [degreePiece_eq_hPartition_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, rfl⟩ := hx
    change decompose (hPartition μ.val) = Finsupp.single d (hPartition μ.val)
    rw [decompose_hPartition, μ.property]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, Finsupp.single_add]
  | smul r x _ hx => simp only [map_smul, hx, Finsupp.smul_single]

theorem decompose_mem (x : Q) (d : ℕ) : decompose x d ∈ degreePiece d := by
  classical
  induction x using EKPairingAdjoint.basis_induction hBasis with
  | hz => simp
  | ha x y hx hy => simpa using (degreePiece d).add_mem hx hy
  | hb μ r =>
    simp only [map_smul, hBasis_apply, decompose_hPartition, Finsupp.smul_apply]
    apply Submodule.smul_mem
    by_cases hd : μ.card = d
    · subst d
      rw [Finsupp.single_eq_same, degreePiece_eq_hPartition_span]
      exact Submodule.subset_span ⟨⟨μ, rfl⟩, rfl⟩
    · rw [Finsupp.single_eq_of_ne hd]
      exact Submodule.zero_mem _

theorem decompose_recompose (f : ℕ →₀ Q) (hf : ∀ d, f d ∈ degreePiece d) :
    decompose (f.sum (fun _ x => x)) = f := by
  classical
  simp only [Finsupp.sum, map_sum]
  calc
    ∑ d ∈ f.support, decompose (f d) = ∑ d ∈ f.support, Finsupp.single d (f d) := by
      apply Finset.sum_congr rfl
      intro d _
      exact decompose_piece (hf d)
    _ = f := Finsupp.sum_single f

/-- Existence AND uniqueness of an actual finitely supported degree decomposition.
The summands live in Q, satisfy the source-defined degree predicate, and sum in Q. -/
theorem unique_homogeneous_decomposition (x : Q) :
    ∃! f : ℕ →₀ Q, (∀ d, f d ∈ degreePiece d) ∧ f.sum (fun _ y => y) = x := by
  refine ⟨decompose x, ⟨decompose_mem x, recompose_decompose x⟩, ?_⟩
  intro f hf
  rw [← hf.2, decompose_recompose f hf.1]

theorem degree_disjoint {a b : ℕ} (hab : a ≠ b) :
    Disjoint (degreePiece a) (degreePiece b) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  have he := (decompose_piece hx).symm.trans (decompose_piece hy)
  have hc := congrArg (fun f : ℕ →₀ Q => f a) he
  simpa [Finsupp.single_eq_of_ne hab.symm] using hc

theorem unit_mem_degree_zero : (1 : Q) ∈ degreePiece 0 := by
  rw [degreePiece_eq_hPartition_span]
  exact one_mem false

@[simp] theorem decompose_unit : decompose (1 : Q) = Finsupp.single 0 1 :=
  decompose_piece unit_mem_degree_zero

end OddMath.Frontier.EKIntegralBases

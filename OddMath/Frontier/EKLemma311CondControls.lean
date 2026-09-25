import OddMath.Frontier.EKDualBases
import OddMath.Frontier.KostkaModuleInversion
import OddMath.Frontier.EKAutomorphisms
import OddMath.Frontier.EKInfiniteSymmetry

/-! PRE-production controls for `EKLemma311Cond`:
EK1107.5610v2 p.29, Lemma 3.11, (3.13), CONDITIONAL on exactly (3.11) in degree d.

Printed (3.13) (governs): "The involution ψ1ψ2 acts on Schur functions as follows:
ψ1ψ2(sλ) = (−1)^{ℓ(wλ)+|λ|} sλT."
Printed (3.11) (p.28, Cor 3.9): "(sλ, sµ) = (−1)^{(λT 2)} δλ,µ."

Compiled BEFORE `EKLemma311Cond`; nothing here mentions a production theorem.

(a) `Identity311` below is the hypothesis, character-for-character the `def Identity311` of
    OddMath/Frontier/EKProp310.lean
    (lines 346-348, file sha256 recorded in an unpublished script), in the same local-instance context
    (`DecidableEq (DegreeShape d) := Classical.decEq _`).  Only the namespace differs.  Its
    dependencies `transposeChoose` (verbatim from EKProp310Controls.lean lines 50-51) and
    `schur`, `schur_defining` (verbatim from EKProp310.lean lines 255-260) are copied here.
(b) The wrong-sign variant of (3.13) with `|λ|` dropped from the exponent is refuted at the
    explicit partition λ = (1) by exact computation, and the printed sign holds there
    (positive control).  The `sh1` construction is copied verbatim from the compiled predecessor
    controls (failed-attempt-snapshot/EKLemma311Controls.lean, sha256 3a48ebeb…, lines 228-231),
    `ell_1` likewise (line 716-717).  Everything else is new.
-/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace OddMath.Frontier.EKLemma311CondControls
open EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases TableauDominance
open EKPartitionSpanning (hPartition ePartition)
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-! ## (a) The hypothesis, copied -/

/-- `C(λᵀ, 2) = Σ_j C(λᵀ_j, 2)`, with `λᵀ` Mathlib's actual transpose diagram.
(verbatim, EKProp310Controls.lean lines 49-51) -/
def transposeChoose (μ : YoungDiagram) : ℕ :=
  (μ.transpose.rowLens.map (fun a => a.choose 2)).sum

/-- (verbatim, EKProp310.lean lines 255-256) -/
def schur (d : ℕ) : DegreeShape d → degreePiece d :=
  KostkaModuleInversion.recover d (degreeHBasis d)

/-- (verbatim, EKProp310.lean lines 258-260) -/
theorem schur_defining (d : ℕ) (μ : DegreeShape d) :
    degreeHBasis d μ = ∑ lam, signedKostka lam.val μ.val • schur d lam :=
  (congrFun (KostkaModuleInversion.rightInverse d (⇑(degreeHBasis d))) μ).symm

/-- Hypothesis: exactly (3.11) in degree `d`.  (verbatim, EKProp310.lean lines 345-348) -/
def Identity311 (d : ℕ) : Prop :=
  ∀ lam μ : DegreeShape d, quotientPairing (schur d lam : Q) (schur d μ : Q) =
    if lam = μ then (-1 : ℤ) ^ transposeChoose lam.val else 0

/-- Control (a): the copied statement typechecks as a family of propositions. -/
example : ℕ → Prop := Identity311

/-! ## (b) Wrong-sign refutation at λ = (1) -/

/-- (verbatim, predecessor controls lines 228-229) -/
def sh1 : DegreeShape 1 :=
  ⟨YoungDiagram.ofRowLens [1] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩
/-- (verbatim, predecessor controls lines 230-231) -/
@[simp] theorem sh1_rows : sh1.val.rowLens = [1] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)

theorem sh1_transpose_val : sh1.val.transpose = sh1.val := YoungDiagram.ext (by decide)

theorem T_1 : transposeShape 1 sh1 = sh1 := Subtype.ext sh1_transpose_val

/-- (verbatim, predecessor controls lines 716-717) -/
theorem ell_1 : EKSemiorthogonality.ell sh1.val = 0 := by
  decide

theorem list_eq_one (l : List ℕ) (hs : l.sum = 1) (hp : ∀ a ∈ l, 0 < a) : l = [1] := by
  match l, hs, hp with
  | [], hs, _ => simp at hs
  | [a], hs, _ => simp at hs; simp [hs]
  | a :: b :: t, hs, hp =>
    have ha := hp a (by simp)
    have hb := hp b (by simp)
    simp at hs
    omega

theorem shape1_eq (μ : DegreeShape 1) : μ = sh1 := by
  have hs := EKIntegralBases.rowLens_sum μ.val
  rw [μ.property] at hs
  have hl := list_eq_one _ hs μ.val.pos_of_mem_rowLens
  exact Subtype.ext (YoungDiagram.equivListRowLens.injective (Subtype.ext (hl.trans sh1_rows.symm)))

/-- In degree 1 the (3.6) solution is `s_(1) = h_1`. -/
theorem schur_sh1 : (schur 1 sh1 : Q) = EKElementaryQuotient.h 1 := by
  have hdef := schur_defining 1 sh1
  rw [Finset.sum_eq_single sh1 (fun b _ hb => absurd (shape1_eq b) hb)
    (fun h => absurd (Finset.mem_univ _) h), signedKostka_diag, one_smul] at hdef
  rw [← hdef, degreeHBasis_apply]
  simp [EKPartitionSpanning.hPartition, sh1_rows]

theorem psi12_h_one :
    EKAutomorphisms.psi12 (EKElementaryQuotient.h 1) = -EKElementaryQuotient.h 1 := by
  rw [EKAutomorphisms.psi12_apply, EKInfiniteSymmetry.psi2_h_one, map_neg,
    EKInfiniteSymmetry.psi1_h_one]

/-- Positive control: the printed sign of (3.13) holds at λ = (1) (exact computation). -/
theorem printed_sign_at_one :
    EKAutomorphisms.psi12 (schur 1 sh1 : Q) =
      ((-1 : ℤ) ^ (EKSemiorthogonality.ell sh1.val + sh1.val.card)) •
        (schur 1 (transposeShape 1 sh1) : Q) := by
  rw [T_1, ell_1, sh1.property, schur_sh1, psi12_h_one]
  simp

/-- Control (b): dropping `|λ|` from the exponent of (3.13) is FALSE (refuted at λ = (1)). -/
theorem wrong_sign_refuted :
    ¬ ∀ lam : DegreeShape 1, EKAutomorphisms.psi12 (schur 1 lam : Q) =
      ((-1 : ℤ) ^ EKSemiorthogonality.ell lam.val) • (schur 1 (transposeShape 1 lam) : Q) := by
  intro h
  have h1 := h sh1
  rw [T_1, ell_1, schur_sh1, psi12_h_one, pow_zero, one_smul] at h1
  have hp := EKSemiorthogonality.proposition_2_14_diagonal sh1.val
  rw [sh1_transpose_val, ell_1, pow_zero] at hp
  simp only [EKSemiorthogonality.hPartition, EKSemiorthogonality.ePartition, sh1_rows,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hp
  have h2 : quotientPairing (-EKElementaryQuotient.h 1) (EKElementaryQuotient.e 1) =
      quotientPairing (EKElementaryQuotient.h 1) (EKElementaryQuotient.e 1) := by
    rw [h1]
  rw [map_neg, LinearMap.neg_apply, hp] at h2
  norm_num at h2

end OddMath.Frontier.EKLemma311CondControls

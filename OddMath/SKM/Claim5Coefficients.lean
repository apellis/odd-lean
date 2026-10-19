/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.CapLaurentCoefficients
import OddMath.SKM.NoncapFamilyCoefficients
import OddMath.CoveringQuantum.CapScalar
import OddMath.CoveringQuantum.UDot.ContextualCommutator

/-! # Same-colour coefficient comparison

Finite decorated matching coefficients for BE2, arXiv:1701.04133v2,
Theorem 10.3 Claim 5. Families retain independently valid decoration points
and serializers. The cap/non-cap split is a partition of their labelled
members, rather than an assumed graphical identity.
-/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators LaurentSeries
open CoveringQuantum CoveringQuantum.Coefficients
open CoveringQuantum.UDot.GenericTensor CoveringQuantum.UDot.GenericVerma.MixedGram

/-- An independently decorated, unique family of strict reduced matchings.
Completeness is kept separate, since subfamilies need not be complete. -/
structure CoefficientFamily {I : Type*} (A : List (Letter I)) where
  members : Set (List (TMove (Letter I)))
  matching : ∀ R ∈ members, IsMatching₂ A [] R ∧ StrictReduced₂ A R
  unique : ∀ R ∈ members, ∀ S ∈ members, Iso (pairing₂ A R) (pairing₂ A S) → R = S
  points : members → ℕ → ℕ × ℕ
  onStrand : ∀ R k, k ∈ leftEnds₂ A R.val → OnStrand₂ A R.val k (points R k)
  serialize : ∀ R : members, (MatchingStrand A R.val → ℕ) → List (DTMove I)
  decorates : ∀ R c, Decorates₂ A R.val (points R) (strandCounts c) (serialize R c)

namespace CoefficientFamily
variable {I X : Type*} {A : List (Letter I)}

/-- Coverage of all strict reduced matching pairings. -/
def Complete (F : CoefficientFamily A) : Prop :=
  ∀ R, IsMatching₂ A [] R → StrictReduced₂ A R →
    ∃ S ∈ F.members, Iso (pairing₂ A S) (pairing₂ A R)

/-- Labelled members, before grading data are chosen. -/
abbrev Labels (F : CoefficientFamily A) := Σ R : F.members, MatchingStrand A R.val → ℕ

/-- Restrict the representatives and the already fixed serializer. -/
def restrict (F : CoefficientFamily A) (P : List (TMove (Letter I)) → Prop) :
    CoefficientFamily A where
  members := {R | R ∈ F.members ∧ P R}
  matching R hR := F.matching R hR.1
  unique R hR S hS := F.unique R hR.1 S hS.1
  points R := F.points ⟨R.val, R.property.1⟩
  onStrand R := F.onStrand ⟨R.val, R.property.1⟩
  serialize R := F.serialize ⟨R.val, R.property.1⟩
  decorates R := F.decorates ⟨R.val, R.property.1⟩

/-- Inclusion of a restricted labelled family. -/
def includeLabels (F : CoefficientFamily A) (P : List (TMove (Letter I)) → Prop)
    (t : (F.restrict P).Labels) : F.Labels := ⟨⟨t.1.val, t.1.property.1⟩, t.2⟩

variable [AddCommGroup X]
/-- Total graphical degree of a serialized member. -/
def degree (F : CoefficientFamily A) (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    (t : F.Labels) : ℤ := tableDegree D sy μ (dLay A (F.serialize t.1 t.2))

/-- Total graphical parity of a serialized member. -/
def parity (F : CoefficientFamily A) (D : Datum I X) (μ : X)
    (t : F.Labels) : ZMod 2 := xpar D μ (dLay A (F.serialize t.1 t.2))

/-- Finite degree fibers are derived from matching uniqueness and valid decoration. -/
theorem finite (F : CoefficientFamily A) (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    (z : ℤ) : Set.Finite {t | F.degree D sy μ t = z} :=
  mixed_labelled_degree_finite D sy μ A [] F.members
    (fun R hR => (F.matching R hR).1) F.unique F.points F.onStrand F.serialize F.decorates z

/-- The weighted finite coefficient, without assuming a Laurent-series realization. -/
def coeff (F : CoefficientFamily A) (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    (σ : ℚ) (z : ℤ) : ℚ :=
  ∑ t ∈ (F.finite D sy μ z).toFinset, σ ^ (F.parity D μ t).val

private theorem restrict_coeff (F : CoefficientFamily A)
    (P : List (TMove (Letter I)) → Prop) [DecidablePred P]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) (σ : ℚ) (z : ℤ) :
    (F.restrict P).coeff D sy μ σ z =
      ∑ t ∈ (F.finite D sy μ z).toFinset.filter (fun t => P t.1.val),
        σ ^ (F.parity D μ t).val := by
  classical
  unfold coeff
  apply Finset.sum_bij (fun t _ => F.includeLabels P t)
  · intro t ht
    exact Finset.mem_filter.mpr ⟨(F.finite D sy μ z).mem_toFinset.mpr
      ((F.restrict P).finite D sy μ z |>.mem_toFinset.mp ht), t.1.property.2⟩
  · intro t _ u _ h
    cases t with | mk t c =>
      cases u with | mk u d =>
        cases t with | mk t ht =>
          cases u with | mk u hu =>
            cases h
            rfl
  · intro t ht
    refine ⟨⟨⟨t.1.val, t.1.property, (Finset.mem_filter.mp ht).2⟩, t.2⟩, ?_, rfl⟩
    exact ((F.restrict P).finite D sy μ z).mem_toFinset.mpr
      ((F.finite D sy μ z).mem_toFinset.mp (Finset.mem_filter.mp ht).1)
  · intros; rfl

/-- A partition of the actual labelled members and their finite fibers. Both
subfamilies use restrictions of the full family's independent serializer. -/
theorem coeff_partition (F : CoefficientFamily A)
    (P : List (TMove (Letter I)) → Prop)
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) (σ : ℚ) (z : ℤ) :
    F.coeff D sy μ σ z = (F.restrict P).coeff D sy μ σ z +
      (F.restrict (fun R => ¬ P R)).coeff D sy μ σ z := by
  classical
  rw [restrict_coeff, restrict_coeff]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

end CoefficientFamily

variable {I X : Type*} [AddCommGroup X]

/-- Membership in the third (cap) class of Claim 5. -/
def claim5Cap (a b : List (Letter I)) (ε : Bool) (i : I)
    (R : List (TMove (Letter I))) : Prop :=
  Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)

/-- The direct cap factor, with the physical suffix weight. No outer bar occurs. -/
def claim5CapSeries (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    (b : List (Letter I)) (ε : Bool) (i : I) (σ : ℚ) : LaurentSeries ℚ :=
  HahnSeries.single
    (sy.d i * (1 + if !ε then D.h i (wt D μ b) else -D.h i (wt D μ b)))
    (σ ^ (cupPar D (wt D μ b) (!ε, i)).val) *
    (PreF.DotSeries.factor (σ ^ (D.parity i).val) (2 * sy.d i).toNat
      (by have := sy.pos i; omega) : LaurentSeries ℚ)

/-- The cap Laurent bridge applied to restrictions of the full serializer. -/
theorem claim5_cap_coeff {a b : List (Letter I)} {ε : Bool} {i : I}
    (M : CoefficientFamily (a ++ (ε, i) :: (!ε, i) :: b))
    (K : CoefficientFamily (a ++ b)) (hM : M.Complete) (hK : K.Complete)
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) (σ : ℚ) (hσ : σ ^ 2 = 1)
    (L : LaurentSeries ℚ) (hIH : ∀ z : ℤ, K.coeff D sy μ σ z = L.coeff z) (z : ℤ) :
    (M.restrict (claim5Cap a b ε i)).coeff D sy μ σ z =
      (claim5CapSeries D sy μ b ε i σ * L).coeff z := by
  obtain ⟨hf, he, hh⟩ := cap_labelled_family_laurent_coefficients
    M.matching K.matching (M.restrict (claim5Cap a b ε i)).points K.points
    (M.restrict (claim5Cap a b ε i)).onStrand K.onStrand
    (M.restrict (claim5Cap a b ε i)).serialize K.serialize
    (M.restrict (claim5Cap a b ε i)).decorates K.decorates
    hM hK M.unique K.unique D sy μ
  exact hh σ hσ L hIH z

/-- Cancellation of the union of the first two classes, using the independently
chosen serializers on the two complete families. -/
theorem claim5_noncap_coeff {a b : List (Letter I)} {i : I}
    (M : CoefficientFamily (a ++ (true, i) :: (false, i) :: b))
    (N : CoefficientFamily (a ++ (false, i) :: (true, i) :: b))
    (hM : M.Complete) (hN : N.Complete)
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (M.restrict (fun R => ¬ claim5Cap a b true i R)).coeff D sy μ σ z =
      σ ^ (D.parity i).val *
        (N.restrict (fun R => ¬ claim5Cap a b false i R)).coeff D sy μ σ z := by
  obtain ⟨_, hh⟩ := noncap_labelled_family_coefficients (X := X)
    M.matching N.matching
    (M.restrict (fun R => ¬ claim5Cap a b true i R)).points
    (N.restrict (fun R => ¬ claim5Cap a b false i R)).points
    (M.restrict (fun R => ¬ claim5Cap a b true i R)).onStrand
    (N.restrict (fun R => ¬ claim5Cap a b false i R)).onStrand
    (M.restrict (fun R => ¬ claim5Cap a b true i R)).serialize
    (N.restrict (fun R => ¬ claim5Cap a b false i R)).serialize
    (M.restrict (fun R => ¬ claim5Cap a b true i R)).decorates
    (N.restrict (fun R => ¬ claim5Cap a b false i R)).decorates
    hM hN M.unique N.unique
  obtain ⟨_, _, _, _, hs⟩ := hh D sy μ
  exact (hs σ hσ z).2

/-- Whole-family graphical commutator: split the actual labelled fibers,
cancel the non-cap contributions, and apply both cap Laurent bridges.
The sole comparison premise is the all-integer shorter coefficient equality. -/
theorem claim5_graphical_commutator {a b : List (Letter I)} {i : I}
    (M : CoefficientFamily (a ++ (true, i) :: (false, i) :: b))
    (N : CoefficientFamily (a ++ (false, i) :: (true, i) :: b))
    (K : CoefficientFamily (a ++ b))
    (hM : M.Complete) (hN : N.Complete) (hK : K.Complete)
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) (σ : ℚ) (hσ : σ ^ 2 = 1)
    (L : LaurentSeries ℚ) (hIH : ∀ z : ℤ, K.coeff D sy μ σ z = L.coeff z) (z : ℤ) :
    M.coeff D sy μ σ z - σ ^ (D.parity i).val * N.coeff D sy μ σ z =
      ((claim5CapSeries D sy μ b true i σ -
        HahnSeries.C (σ ^ (D.parity i).val) * claim5CapSeries D sy μ b false i σ) * L).coeff z := by
  have hm := claim5_cap_coeff M K hM hK D sy μ σ hσ L hIH z
  have hn := claim5_cap_coeff N K hN hK D sy μ σ hσ L hIH z
  have hc := claim5_noncap_coeff M N hM hN D sy μ σ hσ z
  rw [M.coeff_partition (claim5Cap a b true i),
    N.coeff_partition (claim5Cap a b false i), hm, hn, hc]
  rw [sub_mul, HahnSeries.coeff_sub, mul_assoc]
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  ring

/-- The two oriented cap factors simplify to the barred quantum integer,
using the corrected scalar identity and the graphical parity convention. -/
theorem claim5_cap_scalar (D : RootDatum I X) (μ : X) (b : List (Letter I))
    (i : I) (σ : ℚ) (hσ : σ ^ 2 = 1) :
    claim5CapSeries D.toSKM D.skmSymmetrizer μ b true i σ -
      HahnSeries.C (σ ^ (D.parity i).val) *
        claim5CapSeries D.toSKM D.skmSymmetrizer μ b false i σ =
      signLaurent σ hσ (bar (qpInt (D.qi Coefficients.q i) (D.pii pi i)
        (D.h i (wt D.toSKM μ b)))) := by
  rw [← CapScalar.series_eq_bar D σ hσ i (wt D.toSKM μ b)]
  simp only [claim5CapSeries, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    ite_false, ite_true, cupPar, ZMod.val_zero, pow_zero]
  have hs (n : ℤ) (c d : ℚ) :
      (HahnSeries.C c * HahnSeries.single n d : LaurentSeries ℚ) =
        HahnSeries.C (c * d) * HahnSeries.single n 1 := by
    simp only [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  rw [← mul_assoc, hs, ← sub_mul]
  rfl

section Form
variable [DecidableEq I] [DecidableEq X]

/-- The coefficientwise form of Claim 5 at both rational sign specializations.
The explicit induction premise is only the shorter-word coefficient equality
at every integer degree (and every square-one rational sign). No endpoint,
finite-fiber, grading, cap identity or whole-word comparison is assumed.
Colours are unrestricted and bar consistency is not required. The covering
coefficients remain purely even. This is not Theorem 10.3. -/
theorem same_boundary_labelled_form_coeff_iff {a b : List (Letter I)} {i : I}
    (M : CoefficientFamily (a ++ (true, i) :: (false, i) :: b))
    (N : CoefficientFamily (a ++ (false, i) :: (true, i) :: b))
    (K : CoefficientFamily (a ++ b))
    (hM : M.Complete) (hN : N.Complete) (hK : K.Complete)
    (D : RootDatum I X) (μ : X)
    (hIH : ∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
      K.coeff D.toSKM D.skmSymmetrizer μ σ z =
        (signLaurent σ hσ (sesquilinearForm D
          (algebraWord D μ (a ++ b)) (algebraWord D μ []))).coeff z) :
    ((∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
      (signLaurent σ hσ (sesquilinearForm D
        (algebraWord D μ (a ++ (true, i) :: (false, i) :: b))
        (algebraWord D μ []))).coeff z = M.coeff D.toSKM D.skmSymmetrizer μ σ z) ↔
     (∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
      (signLaurent σ hσ (sesquilinearForm D
        (algebraWord D μ (a ++ (false, i) :: (true, i) :: b))
        (algebraWord D μ []))).coeff z = N.coeff D.toSKM D.skmSymmetrizer μ σ z)) := by
  have hc (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
      (signLaurent σ hσ (sesquilinearForm D
        (algebraWord D μ (a ++ (true, i) :: (false, i) :: b))
        (algebraWord D μ []))).coeff z - σ ^ (D.parity i).val *
      (signLaurent σ hσ (sesquilinearForm D
        (algebraWord D μ (a ++ (false, i) :: (true, i) :: b))
        (algebraWord D μ []))).coeff z =
      M.coeff D.toSKM D.skmSymmetrizer μ σ z -
        σ ^ (D.parity i).val * N.coeff D.toSKM D.skmSymmetrizer μ σ z := by
    have hg := claim5_graphical_commutator M N K hM hN hK D.toSKM D.skmSymmetrizer
      μ σ hσ _ (hIH σ hσ) z
    simp only [RootDatum.toSKM_parity] at hg
    rw [claim5_cap_scalar D μ b i σ hσ] at hg
    have ha := congrArg (fun v => (signLaurent σ hσ v).coeff z)
      (sesquilinearForm_context_EF D μ a b i)
    simp only [map_sub, map_mul, SuperCartanDatum.pii, map_pow,
      signLaurent_pi, HahnSeries.coeff_sub] at ha
    rw [← map_pow, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
      smul_eq_mul] at ha
    exact ha.trans hg.symm
  constructor
  · intro h σ hσ z
    have hn : σ ≠ 0 := by intro hz; simp [hz] at hσ
    have hh := hc σ hσ z
    rw [h σ hσ z] at hh
    exact mul_left_cancel₀ (pow_ne_zero _ hn) (sub_right_inj.mp hh)
  · intro h σ hσ z
    have hh := hc σ hσ z
    rw [h σ hσ z] at hh
    exact sub_left_inj.mp hh

end Form
end OddMath.SKM

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.FiniteWeightDuality
import OddMath.CoveringQuantum.SourceWeightLatticeExamples

/-! # Full-dual realization of the infinite-colour complex fixture -/

noncomputable section

namespace OddMath.CoveringQuantum.FiniteWeightDualityConsumer

open FiniteWeightDuality SourceWeightLatticeConsumer

abbrev Y := Module.Dual ℤ lattice

def R : restrictedDatum.toSuperCartanDatum.lusztigDatum.RootDatum Y :=
  sourceRealization h cartan alpha cartan_eval coroots_independent colours weights

def e : lattice ≃ₗ[ℤ] (Y →+ ℤ) := weightEquiv lattice

theorem finite_coweight : Module.Finite ℤ Y := coweight_finite lattice

theorem free_coweight : Module.Free ℤ Y := coweight_free lattice

theorem roundtrip (x : lattice) : e.symm (e x) = x := e.symm_apply_apply x

theorem roundtrip_dual (μ : Y →+ ℤ) : e (e.symm μ) = μ := e.apply_symm_apply μ

theorem evaluation (x : lattice) (y : Y) : e x y = y x := rfl

theorem pairing (i : colours) (x : lattice) :
    (restrictedDatum.toSuperCartanDatum.rootDatumOf R).h i (e x) =
      restrictedDatum.h i x := rfl

theorem pairing_inverse (i : colours) (μ : Y →+ ℤ) :
    restrictedDatum.h i (e.symm μ) =
      (restrictedDatum.toSuperCartanDatum.rootDatumOf R).h i μ :=
  coroot_weightEquiv_symm restrictedDatum i μ

theorem roots (i : colours) :
    e (restrictedDatum.α i) = (restrictedDatum.toSuperCartanDatum.rootDatumOf R).α i := rfl

theorem roots_inverse (i : colours) :
    e.symm ((restrictedDatum.toSuperCartanDatum.rootDatumOf R).α i) = restrictedDatum.α i :=
  weightEquiv_symm_root restrictedDatum i

theorem roots_independent :
    LinearIndependent ℤ (restrictedDatum.toSuperCartanDatum.rootDatumOf R).α :=
  source_root_independent h cartan alpha cartan_eval coroots_independent colours weights
    SourceWeightLatticeConsumer.roots_independent

theorem coroots_independent : LinearIndependent ℤ R.coroot :=
  source_coroot_independent h cartan alpha cartan_eval
    SourceWeightLatticeConsumer.coroots_independent colours weights

/-- Centrality on simple coroots does not identify a weight with zero. -/
theorem central_survives : e centralInWindow ≠ 0 := by
  intro hz
  apply central_nonzero
  exact e.injective (hz.trans e.map_zero.symm)

theorem central_roundtrip : e.symm (e centralInWindow) = centralInWindow :=
  roundtrip centralInWindow

theorem central_pairing (i : colours) :
    (restrictedDatum.toSuperCartanDatum.rootDatumOf R).h i (e centralInWindow) = 0 :=
  central_coroot_zero i

/-- Some functional in the full dual detects the retained central direction. -/
theorem central_detected : ∃ y : Y, e centralInWindow y ≠ 0 := by
  by_contra hn
  apply central_survives
  ext y
  exact not_not.mp (fun hne ↦ hn ⟨y, hne⟩)

/-- The fixture retains its infinite-support seed, not only the central generator. -/
theorem seed_roundtrip : e.symm (e seedInWindow) = seedInWindow := roundtrip seedInWindow

theorem seed_pairing (i : colours) :
    (restrictedDatum.toSuperCartanDatum.rootDatumOf R).h i (e seedInWindow) = 1 :=
  seed_coroot i

theorem cartan_compatible (i j : colours) :
    (restrictedDatum.toSuperCartanDatum.rootDatumOf R).a i j = restrictedDatum.a i j := rfl

theorem symmetrizer_compatible (i : colours) :
    (restrictedDatum.toSuperCartanDatum.rootDatumOf R).d i = restrictedDatum.d i := rfl

theorem parity_compatible (i : colours) :
    (restrictedDatum.toSuperCartanDatum.rootDatumOf R).parity i = restrictedDatum.parity i := rfl

end OddMath.CoveringQuantum.FiniteWeightDualityConsumer

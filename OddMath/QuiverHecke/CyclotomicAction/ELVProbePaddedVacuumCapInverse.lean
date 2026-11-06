/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumCap
import OddMath.QuiverHecke.SwappedAssembly.Sigma.VacuumCapInverseWindow
import OddMath.QuiverHecke.SwappedAssembly.Sigma.FactorWindowInverse
import OddMath.QuiverHecke.CyclotomicAction.ParameterTwistPureNilpotent

/-! # The chosen vacuum cap inverse in the native chart

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

At formal content zero and positive height, the actual positive augmented factor
matrix of the supported vacuum sector has a cap-window inverse
(`SupportedSectors.vacuumCapInverseData`). This file transports that inverse,
entry by entry, to the native chart of the regular vacuum probe: its principal map
becomes the evaluated A6 bend `evaluatedMixedBend` (odd colour, through
`paddedVacuumDx_odd`) and its windows become the native rows `x ^ n ≫ v`
(`paddedVacuumCap_eq`). The result `vacuumCapInverse_odd` is a cap
inverse of exactly the window used by `tensorVacuumCapInverse_odd_moments`.

The transport uses only additive evaluation (`IsCapInverse.map`), the corner
charts (`IsCapInverse.coordinates`) and a change of the common window target
(`IsCapInverse.target`). No inverse, moment or bubble value is assumed.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct

namespace OddMath.QuiverHecke.SwappedAssembly

namespace ProbeWindow

variable {C : Type*} [Category C] [Preadditive C]
  {X Y O O' : C} {n : ℕ} {s : X ⟶ Y} {v : Fin n → (X ⟶ O)}
  {j : Y ⟶ X} {A : Fin n → (O ⟶ X)}

/-- An isomorphism of the common window target transports a cap inverse. -/
theorem IsCapInverse.target (H : IsCapInverse s v j A) (c : O ≅ O') :
    IsCapInverse s (fun r => v r ≫ c.hom) j (fun r => c.inv ≫ A r) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨h1, fun r => ?_, fun r => ?_, fun r t => ?_, ?_⟩
  · rw [Category.assoc, h2 r, Limits.comp_zero]
  · rw [← Category.assoc, h3 r, Limits.zero_comp]
  · rw [Category.assoc, reassoc_of% (h4 r t)]
    split_ifs <;> simp
  · simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h5

end ProbeWindow

namespace ProbeReservoir

open OddMath.SKM Classical
open scoped ZeroObject

universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
variable (P : ProbeReservoir k B D Sc)
variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
  {C' : Type*} [Category C'] [Preadditive C'] [Limits.HasZeroObject C']

/-- A padded central cap inverse survives postcomposition of the evaluation with an
additive functor: the padded principal map and cap rows of the composite evaluation
have an entrywise inverse whenever those of the original evaluation do. -/
theorem centralPadded_capInverse_comp (c : P.CrossCoeff) (i : I) (t : Sector I)
    (Z Z' : P.H t) (hZ : Z = Z') (E : P.H t ⥤ C) (G : C ⥤ C') [G.Additive]
    (E' : P.H t ⥤ C') (hE : E ⋙ G = E') {a b : Bool}
    (ha : StepValid (up i) a t) (hb : StepValid (dn i) b t) {N : ℕ}
    (hN : ∃ j A, ProbeWindow.IsCapInverse (P.centralPaddedSigma c i t Z E a b)
      (fun n : Fin N => P.centralPaddedCap i t Z E a n) j A) :
    ∃ j A, ProbeWindow.IsCapInverse (P.centralPaddedSigma c i t Z' E' a b)
      (fun n : Fin N => P.centralPaddedCap i t Z' E' a n) j A := by
  subst hZ
  subst hE
  obtain ⟨j, A, h⟩ := hN
  let s := P.centralSourceCornerIso i t Z (E ⋙ G) ⟨a, ha⟩ ≪≫
    (G.mapIso (P.centralSourceCornerIso i t Z E ⟨a, ha⟩)).symm
  let r := P.centralTargetCornerIso i t Z (E ⋙ G) ⟨b, hb⟩ ≪≫
    (G.mapIso (P.centralTargetCornerIso i t Z E ⟨b, hb⟩)).symm
  have h' := (h.map G).coordinates s r
  have hσ : s.hom ≫ G.map (P.centralPaddedSigma c i t Z E a b) ≫ r.inv =
      P.centralPaddedSigma c i t Z (E ⋙ G) a b := by
    simp only [centralPaddedSigma, dite_eq_left_of_eq_true (eq_true ha),
      dite_eq_left_of_eq_true (eq_true hb), s, r, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp,
      Functor.comp_map, Category.assoc, Iso.map_inv_hom_id_assoc]
  have hcap : ∀ n : Fin N, s.hom ≫ G.map (P.centralPaddedCap i t Z E a n) =
      P.centralPaddedCap i t Z (E ⋙ G) a n := by
    intro n
    simp only [centralPaddedCap, dite_eq_left_of_eq_true (eq_true ha), s, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_inv, Functor.map_comp, Functor.comp_map, Category.assoc,
      Iso.map_inv_hom_id_assoc]
  rw [hσ] at h'
  simp only [hcap] at h'
  exact ⟨_, _, h'⟩

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u

local instance paddedVacuumCapInverseHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance paddedVacuumCapInverseZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR

/-- Evaluating the whole-output projection at the regular probe is the
vacuum bend evaluation. -/
theorem reservoirOutputEval_comp_total :
    SupportedSectors.reservoirOutputEval D Sc m cutoff bound ΛP ΛR hcP hcR ((0, 0) : Sector I)
        (sectorEmpty D Sc m cutoff bound ΛP ΛR hcP hcR) ⋙
      homTotalEvaluation (k := k) (sectorRegular D Sc m cutoff bound ΛP ΛR hcP hcR) =
    vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR := by
  rw [vacuumSectorEvaluation_eq]
  exact CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => by
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    rfl)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))
variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (i : I)

include sy hc in
/-- **The chosen vacuum cap inverse in the native chart (odd colour).** If the
supported vacuum input is the given tensor input, the actual positive factor
matrix supplies an entrywise inverse of the native cap window
`[bend; x ^ n ≫ v]_(n < h)` of the evaluated A6 bend, `h = h_i(wt)`. -/
theorem vacuumCapInverse_odd [Fact Sc.PureNilpotent]
    (Z : SupportedSectors.H D (parameterTwist D Sc) m cutoff bound ΛP ΛR ((0, 0) : Sector I))
    (hZ : Z.obj = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1)
    (hh : 0 ≤ D.h i ((P).wt ((0, 0) : Sector I))) :
    ∃ (j : _) (A : Fin (D.h i ((P).wt ((0, 0) : Sector I))).toNat → _),
      ProbeWindow.IsCapInverse
        (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
        (fun n => (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ (n : ℕ)) ≫
          ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H)) j A := by
  have : (homTotalEvaluation (k := k)
      (B := ContentModules D (parameterTwist D Sc) cutoff bound (0 : Multiset I))
      (sectorRegular D Sc m cutoff bound ΛP ΛR hcP hcR)).Additive := inferInstance
  obtain ⟨j, A, h₁⟩ := (P).centralPadded_capInverse_comp
    (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc) i ((0, 0) : Sector I)
    Z.obj _ hZ
    (SupportedSectors.reservoirOutputEval D Sc m cutoff bound ΛP ΛR hcP hcR ((0, 0) : Sector I)
      (sectorEmpty D Sc m cutoff bound ΛP ΛR hcP hcR))
    (homTotalEvaluation (k := k) (sectorRegular D Sc m cutoff bound ΛP ΛR hcP hcR))
    (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR)
    (reservoirOutputEval_comp_total D Sc m cutoff bound ΛP ΛR hcP hcR)
    (a := true) (b := false) trivial trivial
    ⟨_, _, (SupportedSectors.vacuumCapInverseData D Sc m cutoff bound ΛP ΛR hcP hcR sy hc i Z
      (sectorEmpty D Sc m cutoff bound ΛP ΛR hcP hcR) hh).isInverse⟩
  have h₃ := (h₁.coordinates (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm
    (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm).target
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H)
  have hs : (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
      (P).centralPaddedSigma (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc) i
        ((0, 0) : Sector I) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
      (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
        (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) :=
    (Iso.inv_comp_eq _).2 (paddedVacuumDx_odd D Sc m cutoff bound ΛP ΛR hcP hcR H i sy hc hP hi)
  have hw : ∀ n : ℕ, (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
      (P).centralPaddedCap i ((0, 0) : Sector I)
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true n ≫
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom =
      (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := fun n =>
    (Iso.inv_comp_eq _).2 (paddedVacuumCap_eq D Sc m cutoff bound ΛP ΛR hcP hcR H i hP n)
  simp only [Iso.symm_hom, Iso.symm_inv, Category.assoc, hs, hw] at h₃
  exact ⟨_, _, h₃⟩

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum

import OddMath.QuiverHecke.SwappedAssembly.Sigma.AugmentedFactorMatrix
import OddMath.SKM.RouquierHomPreInverse

/-! # Transfer of prescribed factor window inverses

The pure factor input to SwappedHomInversion §§2,6 and the inverse
attachment in CentralMatrixAttachment: every entry of the prescribed
local inverse survives additive evaluation and a change of corner objects.
The statements include empty windows and zero objects. No inverse of the
central matrix or of its residual is assumed.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM Supercategory

namespace ProbeWindow
section Evaluation
variable {C C' : Type*} [Category C] [Category C'] [Preadditive C] [Preadditive C']
  (E : C ⥤ C') [E.Additive]
  {X Y O : C} {n : ℕ} {s : X ⟶ Y} {v : Fin n → (X ⟶ O)}
  {j : Y ⟶ X} {A : Fin n → (O ⟶ X)}

/-- Additive evaluation retains every cap inverse identity. -/
theorem IsCapInverse.map (H : IsCapInverse s v j A) :
    IsCapInverse (E.map s) (fun a => E.map (v a)) (E.map j) (fun a => E.map (A a)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨?_, fun a => ?_, fun a => ?_, fun a b => ?_, ?_⟩
  · simpa only [Functor.map_comp, E.map_id] using congrArg E.map h1
  · simpa only [Functor.map_comp, E.map_zero] using congrArg E.map (h2 a)
  · simpa only [Functor.map_comp, E.map_zero] using congrArg E.map (h3 a)
  · simpa only [Functor.map_comp, apply_ite E.map, E.map_id, E.map_zero] using
      congrArg E.map (h4 a b)
  · simpa only [Functor.map_add, Functor.map_sum, Functor.map_comp, E.map_id] using
      congrArg E.map h5

/-- Additive evaluation retains every cup inverse identity. -/
theorem IsCupInverse.map {u : Fin n → (O ⟶ Y)} {B : Fin n → (Y ⟶ O)}
    (H : IsCupInverse s u j B) :
    IsCupInverse (E.map s) (fun a => E.map (u a)) (E.map j) (fun a => E.map (B a)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨?_, fun a => ?_, fun a => ?_, fun a b => ?_, ?_⟩
  · simpa only [Functor.map_comp, E.map_id] using congrArg E.map h1
  · simpa only [Functor.map_comp, E.map_zero] using congrArg E.map (h2 a)
  · simpa only [Functor.map_comp, E.map_zero] using congrArg E.map (h3 a)
  · simpa only [Functor.map_comp, apply_ite E.map, E.map_id, E.map_zero] using
      congrArg E.map (h4 a b)
  · simpa only [Functor.map_add, Functor.map_sum, Functor.map_comp, E.map_id] using
      congrArg E.map h5

end Evaluation

section Coordinates
variable {C : Type*} [Category C] [Preadditive C]
  {X Y O X' Y' : C} {n : ℕ} {s : X ⟶ Y} {v : Fin n → (X ⟶ O)}
  {j : Y ⟶ X} {A : Fin n → (O ⟶ X)}

/-- Corner isomorphisms transport the whole cap inverse, including zero corners. -/
theorem IsCapInverse.coordinates (H : IsCapInverse s v j A) (a : X' ≅ X) (b : Y' ≅ Y) :
    IsCapInverse (a.hom ≫ s ≫ b.inv) (fun r => a.hom ≫ v r)
      (b.hom ≫ j ≫ a.inv) (fun r => A r ≫ a.inv) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨?_, fun r => ?_, fun r => ?_, fun r t => ?_, ?_⟩
  · simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% h1, Iso.hom_inv_id]
  · simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% (h2 r), Limits.zero_comp]
  · simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [h3 r, Limits.comp_zero]
  · simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h4 r t
  · have h := congrArg (fun f => a.hom ≫ f ≫ a.inv) h5
    simpa only [Preadditive.comp_add, Preadditive.add_comp, Preadditive.comp_sum,
      Preadditive.sum_comp, Category.assoc, Iso.inv_hom_id_assoc, Category.id_comp,
      Iso.hom_inv_id] using h

/-- Corner isomorphisms transport the whole cup inverse, including zero corners. -/
theorem IsCupInverse.coordinates {u : Fin n → (O ⟶ Y)} {B : Fin n → (Y ⟶ O)}
    (H : IsCupInverse s u j B) (a : X' ≅ X) (b : Y' ≅ Y) :
    IsCupInverse (a.hom ≫ s ≫ b.inv) (fun r => u r ≫ b.inv)
      (b.hom ≫ j ≫ a.inv) (fun r => b.hom ≫ B r) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨?_, fun r => ?_, fun r => ?_, fun r t => ?_, ?_⟩
  · simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% h1, Iso.hom_inv_id]
  · simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [h2 r, Limits.comp_zero]
  · simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% (h3 r), Limits.zero_comp]
  · simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h4 r t
  · have h := congrArg (fun f => b.hom ≫ f ≫ b.inv) h5
    simpa only [Preadditive.comp_add, Preadditive.add_comp, Preadditive.comp_sum,
      Preadditive.sum_comp, Category.assoc, Iso.inv_hom_id_assoc, Category.id_comp,
      Iso.hom_inv_id] using h

/-- The negative central matrix negates the principal inverse as well. -/
theorem IsCapInverse.neg_principal (H : IsCapInverse s v j A) :
    IsCapInverse (-s) v (-j) A := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  exact ⟨by simpa using h1, fun r => by simp [h2 r],
    fun r => by simp [h3 r], h4, by simpa using h5⟩

/-- The negative central matrix retains the unit rows while negating its principal inverse. -/
theorem IsCupInverse.neg_principal {u : Fin n → (O ⟶ Y)} {B : Fin n → (Y ⟶ O)}
    (H : IsCupInverse s u j B) : IsCupInverse (-s) u (-j) B := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  exact ⟨by simpa using h1, fun r => by simp [h2 r],
    fun r => by simp [h3 r], h4, by simpa using h5⟩
end Coordinates
end ProbeWindow

namespace FactorWindowInverse
variable {k : Type*} [CommRing k] {C : Type*} [Category C] [Preadditive C]
  [Linear k C] [Supercategory k C] {A B Z : C} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}

/-- Forgetting the parity profile retains all five cap inverse equations. -/
theorem cap {f : A ⟶ B} {g : ℕ → (A ⟶ Z)} (J : SuperSumInvTo (k := k) f g p q n) :
    ProbeWindow.IsCapInverse f (fun r : Fin n => g r) J.f' (fun r => J.g' r) := by
  refine ⟨J.ff, fun r => J.gf r r.isLt, fun r => J.fg r r.isLt, ?_, ?_⟩
  · intro r t
    simpa only [Fin.ext_iff] using J.gg r t r.isLt t.isLt
  · change f ≫ J.f' + ∑ r : Fin n, g r ≫ J.g' r = _
    rw [Fin.sum_univ_eq_sum_range (fun r => g r ≫ J.g' r)]
    exact J.total

/-- Forgetting the parity profile retains all five cup inverse equations. -/
theorem cup {f : B ⟶ A} {g : ℕ → (Z ⟶ A)} (J : SuperSumInvFrom (k := k) f g p q n) :
    ProbeWindow.IsCupInverse f (fun r : Fin n => g r) J.f' (fun r => J.g' r) := by
  refine ⟨J.ff, fun r => J.fg r r.isLt, fun r => J.gf r r.isLt, ?_, ?_⟩
  · intro r t
    simpa only [Fin.ext_iff] using J.gg r t r.isLt t.isLt
  · change J.f' ≫ f + ∑ r : Fin n, J.g' r ≫ g r = _
    rw [Fin.sum_univ_eq_sum_range (fun r => J.g' r ≫ g r)]
    exact J.total
end FactorWindowInverse

section ZeroCorner
variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]

/-- An absent pure corner is compared to a proved zero native object. -/
def sectorFamilyZeroCornerIso (p : Bool → Prop) (V : {a : Bool // p a} → C)
    (a : Bool) (ha : ¬p a) (N : C) (hN : Limits.IsZero N) :
    sectorFamilyCorner p V a ≅ N :=
  eqToIso (by simp only [sectorFamilyCorner, dite_eq_right ha]) ≪≫
    (Limits.isZero_zero C).iso hN
end ZeroCorner

namespace ProbeReservoir
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k} (P : ProbeReservoir k B D Sc)
  {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
  (c : P.CrossCoeff) (i : I) (t : Sector I) (Z : P.H t)
  (E : P.H t ⥤ C) [E.Additive]

/-- The occupied probe cap corner retains the normalized left-factor inverse and its signs. -/
theorem centralPaddedProbe_capInverse (hb : StepValid (dn i) true t)
    (hh : D.h i (-P.muP t) ≤ 0) :
    ∃ j A, ProbeWindow.IsCapInverse (P.centralPaddedSigma c i t Z E true true)
      (fun a : Fin (-D.h i (-P.muP t)).toNat => P.centralPaddedCap i t Z E true a) j A := by
  have ha : StepValid (up i) true t := by trivial
  let J := homContentPreInvPos P.T P.W.obj i (P.muM t)
    (P.muP_preE i t) (P.muP_preF i hb) hh Z
  have H := ((FactorWindowInverse.cap J).map E).coordinates
    (P.centralSourceCornerIso i t Z E ⟨true, ha⟩)
    (P.centralTargetCornerIso i t Z E ⟨true, hb⟩)
  refine ⟨(P.centralTargetCornerIso i t Z E ⟨true, hb⟩).hom ≫ E.map J.f' ≫ (P.centralSourceCornerIso i t Z E ⟨true, ha⟩).inv, (fun r => E.map (J.g' r) ≫ (P.centralSourceCornerIso i t Z E ⟨true, ha⟩).inv), ?_⟩
  simpa only [centralPaddedSigma, centralPaddedCap, dite_eq_left ha, dite_eq_left hb,
    centralFactorSigma, centralFactorCap, homContentPreMate] using H

/-- The occupied probe unit corner retains all normalized inverse window rows. -/
theorem centralPaddedProbe_cupInverse (hb : StepValid (dn i) true t)
    (hh : 0 ≤ D.h i (-P.muP t)) :
    ∃ j B, ProbeWindow.IsCupInverse (P.centralPaddedSigma c i t Z E true true)
      (fun a : Fin (D.h i (-P.muP t)).toNat => P.centralPaddedUnit i t Z E true a) j B := by
  have ha : StepValid (up i) true t := by trivial
  let J := homContentPreInvNeg P.T P.W.obj i (P.muM t)
    (P.muP_preE i t) (P.muP_preF i hb) hh Z
  have H := ((FactorWindowInverse.cup J).map E).coordinates
    (P.centralSourceCornerIso i t Z E ⟨true, ha⟩)
    (P.centralTargetCornerIso i t Z E ⟨true, hb⟩)
  refine ⟨(P.centralTargetCornerIso i t Z E ⟨true, hb⟩).hom ≫ E.map J.f' ≫ (P.centralSourceCornerIso i t Z E ⟨true, ha⟩).inv, (fun r => (P.centralTargetCornerIso i t Z E ⟨true, hb⟩).hom ≫ E.map (J.g' r)), ?_⟩
  simpa only [centralPaddedSigma, centralPaddedUnit, dite_eq_left ha, dite_eq_left hb,
    centralFactorSigma, centralFactorUnit, homContentPreMate] using H

/-- An absent probe target transports the normalized native cap inverse
through the native target's proved vanishing, retaining every dotted row. -/
theorem centralPaddedProbe_capInverse_of_target_isZero
    (hb : ¬StepValid (dn i) true t) {ρ : X} (h : -ρ + D.α i = -P.muP t)
    (hzero : Limits.IsZero ((homContentPreF P.T P.W.obj i (P.muM t) h).obj
      ((homContentPreE P.T P.W.obj i (P.muM t) h).obj Z)))
    (hh : D.h i (-P.muP t) ≤ 0) :
    ∃ j A, ProbeWindow.IsCapInverse (P.centralPaddedSigma c i t Z E true true)
      (fun a : Fin (-D.h i (-P.muP t)).toNat => P.centralPaddedCap i t Z E true a) j A := by
  have ha : StepValid (up i) true t := by trivial
  let a := P.centralSourceCornerIso i t Z E ⟨true, ha⟩
  let b := sectorFamilyZeroCornerIso (fun b => StepValid (dn i) b t)
    (fun b => E.obj (P.centralTargetFactor i t Z b)) true hb _ (E.map_isZero hzero)
  let J := homContentPreInvPos P.T P.W.obj i (P.muM t) (P.muP_preE i t) h hh Z
  have H := ((FactorWindowInverse.cap J).map E).coordinates a b
  have hz : Limits.IsZero (sectorFamilyCorner (fun b => StepValid (dn i) b t)
      (fun b => E.obj (P.centralTargetFactor i t Z b)) true) := by
    simpa only [sectorFamilyCorner, dite_eq_right hb] using Limits.isZero_zero C
  have hs : a.hom ≫ E.map (homContentPreMate P.T P.W.obj i (P.muM t)
      (P.muP_preE i t) h Z) ≫ b.inv = P.centralPaddedSigma c i t Z E true true :=
    hz.eq_of_tgt _ _
  rw [hs] at H
  have hv : (fun r : Fin (-D.h i (-P.muP t)).toNat =>
      a.hom ≫ E.map (homReservoirCap P.T P.W.obj i (P.muM t) (P.muP_preE i t) r Z)) =
      (fun r : Fin (-D.h i (-P.muP t)).toNat => P.centralPaddedCap i t Z E true r) := by
    funext r
    simp only [centralPaddedCap, dite_eq_left ha, centralFactorCap, a]
  rw [hv] at H
  exact ⟨_, _, H⟩

/-- The absent probe target also retains the whole normalized native cup inverse. -/
theorem centralPaddedProbe_cupInverse_of_target_isZero
    (hb : ¬StepValid (dn i) true t) {ρ : X} (h : -ρ + D.α i = -P.muP t)
    (hzero : Limits.IsZero ((homContentPreF P.T P.W.obj i (P.muM t) h).obj
      ((homContentPreE P.T P.W.obj i (P.muM t) h).obj Z)))
    (hh : 0 ≤ D.h i (-P.muP t)) :
    ∃ j B, ProbeWindow.IsCupInverse (P.centralPaddedSigma c i t Z E true true)
      (fun a : Fin (D.h i (-P.muP t)).toNat => P.centralPaddedUnit i t Z E true a) j B := by
  have ha : StepValid (up i) true t := by trivial
  let a := P.centralSourceCornerIso i t Z E ⟨true, ha⟩
  let b := sectorFamilyZeroCornerIso (fun b => StepValid (dn i) b t)
    (fun b => E.obj (P.centralTargetFactor i t Z b)) true hb _ (E.map_isZero hzero)
  let J := homContentPreInvNeg P.T P.W.obj i (P.muM t) (P.muP_preE i t) h hh Z
  have H := ((FactorWindowInverse.cup J).map E).coordinates a b
  have hz : Limits.IsZero (sectorFamilyCorner (fun b => StepValid (dn i) b t)
      (fun b => E.obj (P.centralTargetFactor i t Z b)) true) := by
    simpa only [sectorFamilyCorner, dite_eq_right hb] using Limits.isZero_zero C
  have hs : a.hom ≫ E.map (homContentPreMate P.T P.W.obj i (P.muM t)
      (P.muP_preE i t) h Z) ≫ b.inv = P.centralPaddedSigma c i t Z E true true :=
    hz.eq_of_tgt _ _
  have hu : (fun r : Fin (D.h i (-P.muP t)).toNat =>
      E.map (homReservoirCup P.T P.W.obj i (P.muM t) h r Z) ≫ b.inv) =
      (fun r : Fin (D.h i (-P.muP t)).toNat => P.centralPaddedUnit i t Z E true r) := by
    funext r
    exact hz.eq_of_tgt _ _
  rw [hs, hu] at H
  exact ⟨_, _, H⟩
end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

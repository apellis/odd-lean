import OddMath.QuiverHecke.SwappedAssembly.Sigma.BendWindowEquations
import OddMath.QuiverHecke.SwappedAssembly.Sigma.ProbeSlideWindow

/-! # Separated mixed bends in the padded central charts

`SwappedHomInversion.md` §3 (6): transport the separated bend equations
to the literal two-sector corners used by `CentralInverse/ResidualComparison`.
The probe automorphisms, cap and unit are those of `ProbeSlideWindow`.
Absent reservoir sources and probe targets retain their zero padding.
-/
noncomputable section
open scoped BigOperators Classical
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM

namespace ProbeWindow
variable {C : Type*} [Category C] [Preadditive C]

/-- Transport a separated negative-probe series through its two corner charts. -/
theorem dx_coordinates {XP YR O XP' YR' : C} (x : Aut XP) (v : XP ⟶ O)
    (uR : ℕ → (O ⟶ YR)) (q : ℤ) (N : ℕ) {Dx : XP ⟶ YR}
    (H : Dx = -∑ r ∈ Finset.range N,
      q^(r+1) • ((x ^ (-(r : ℤ)-1)).hom ≫ v ≫ uR r))
    (a : XP' ≅ XP) (b : YR' ≅ YR) :
    a.hom ≫ Dx ≫ b.inv = -∑ r ∈ Finset.range N,
      q^(r+1) • ((cornerAut a x ^ (-(r : ℤ)-1)).hom ≫
        (a.hom ≫ v) ≫ (uR r ≫ b.inv)) := by
  rw [H]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sum,
    Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    cornerAut_zpow_hom, Category.assoc, Iso.inv_hom_id_assoc]

/-- Transport a separated negative-target series through its two corner charts. -/
theorem cx_coordinates {XR YP O XR' YP' : C} (y : Aut YP) (vR : ℕ → (XR ⟶ O))
    (u : O ⟶ YP) (q : ℤ) (N : ℕ) {Cx : XR ⟶ YP}
    (H : Cx = ∑ r ∈ Finset.range N,
      q^(r+2) • (vR r ≫ u ≫ (y ^ (-(r : ℤ)-1)).hom))
    (a : XR' ≅ XR) (b : YP' ≅ YP) :
    a.hom ≫ Cx ≫ b.inv = ∑ r ∈ Finset.range N,
      q^(r+2) • ((a.hom ≫ vR r) ≫ (u ≫ b.inv) ≫
        (cornerAut b y ^ (-(r : ℤ)-1)).hom) := by
  rw [H]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, cornerAut_zpow_hom, Category.assoc, Iso.inv_hom_id_assoc]
end ProbeWindow

namespace ProbeReservoir
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k} (P : ProbeReservoir k B D Sc)
  {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
  (i : I) (t : Sector I) (Z : P.H t) (E : P.H t ⥤ C) [E.Additive]
  (hdot : ∀ {a b : X} (h : a + D.α i = b), IsIso (P.T.dot i h))

/-- The literal padded `hDx` equation, including its leading minus. -/
def CentralPaddedDxSeparatedAt (c : P.CrossCoeff) (N : ℕ) : Prop :=
  P.centralPaddedSigma c i t Z E true false = -∑ r ∈ Finset.range N,
    (koszulSign (D.parity i) (D.parity i))^(r+1) •
      ((P.centralPaddedProbeX i t Z E hdot ^ (-(r : ℤ)-1)).hom ≫
        P.centralPaddedCap i t Z E true 0 ≫ P.centralPaddedUnit i t Z E false r)

/-- The literal padded `hCx` equation, retaining both interchange shifts. -/
def CentralPaddedCxSeparatedAt (c : P.CrossCoeff) (N : ℕ) : Prop :=
  P.centralPaddedSigma c i t Z E false true = ∑ r ∈ Finset.range N,
    (koszulSign (D.parity i) (D.parity i))^(r+2) •
      (P.centralPaddedCap i t Z E false r ≫ P.centralPaddedUnit i t Z E true 0 ≫
        (P.centralPaddedProbeY i t Z E hdot ^ (-(r : ℤ)-1)).hom)

omit [E.Additive] in
/-- The occupied Dx bend is the separated series in its prescribed padded charts. -/
theorem centralPaddedDx_separated (c : P.CrossCoeff) (N : ℕ)
    (H : let _ := hdot (P.muP_preE i t)
      ProbeToReservoirSeparatedAt P i t Z E c N) :
    P.CentralPaddedDxSeparatedAt i t Z E hdot c N := by
  let := hdot (P.muP_preE i t)
  have H' := ProbeWindow.dx_coordinates
    (Functor.mapAut _ E (homPreDotAut P.T P.W i (P.muP_preE i t)
      ((homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj Z)))
    (E.map ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
      (P.muM t) (P.muP_preE i t)).counit.app Z))
    (fun r => E.map (homContentPostCup P.T.obj P.W i t.1 (P.muP t)
      (P.muM_postF i t) r Z)) _ N H
    (P.centralSourceCornerIso i t Z E ⟨true, by trivial⟩)
    (P.centralTargetCornerIso i t Z E ⟨false, by trivial⟩)
  simpa only [CentralPaddedDxSeparatedAt, centralPaddedSigma, centralPaddedUnit,
    dite_eq_left (show StepValid (up i) true t from by trivial),
    dite_eq_left (show StepValid (dn i) false t from by trivial), centralFactorSigma,
    centralFactorUnit, centralPaddedProbeX, probeDotAut, centralSourceFactor,
    P.centralPaddedProbeCap_zero i t Z E] using H'

omit [E.Additive] in
/-- The occupied Cx bend is the separated series in its prescribed padded charts. -/
theorem centralPaddedCx_separated (c : P.CrossCoeff)
    (hb : StepValid (dn i) true t) (hv : StepValid (up i) false t) (N : ℕ)
    (H : let _ := hdot (P.muP_preF i hb)
      ReservoirToProbeSeparatedAt P i t hb hv Z E c N) :
    P.CentralPaddedCxSeparatedAt i t Z E hdot c N := by
  let := hdot (P.muP_preF i hb)
  have H' := ProbeWindow.cx_coordinates
    (Functor.mapAut _ E (Functor.mapAut _
      (homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hb))
      (homPreDotAut P.T P.W i (P.muP_preF i hb) Z)))
    (fun r => E.map (homContentPostCap P.T.obj P.W i t.1 (P.muP t)
      (P.muM_postE i hv) r Z))
    (E.map ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
      (P.muM t) (P.muP_preF i hb)).unit.app Z)) _ N H
    (P.centralSourceCornerIso i t Z E ⟨false, hv⟩)
    (P.centralTargetCornerIso i t Z E ⟨true, hb⟩)
  simpa only [CentralPaddedCxSeparatedAt, centralPaddedSigma, centralPaddedCap,
    dite_eq_left hv, dite_eq_left hb, centralFactorSigma, centralFactorCap,
    centralPaddedProbeY, probeDotAut, centralTargetFactor,
    P.centralPaddedProbeUnit_zero i t Z E hb] using H'

omit [E.Additive] in
/-- A missing reservoir source makes the padded Cx equation hold at every count. -/
theorem centralPaddedCx_separated_of_source_absent (c : P.CrossCoeff)
    (hv : ¬StepValid (up i) false t) (N : ℕ) :
    P.CentralPaddedCxSeparatedAt i t Z E hdot c N := by
  have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
      (fun a => E.obj (P.centralSourceFactor i t Z a)) false) := by
    simpa only [sectorFamilyCorner, dite_eq_right hv] using Limits.isZero_zero C
  exact hz.eq_of_src _ _

omit [E.Additive] in
/-- A missing probe target makes the padded Cx equation hold at every count. -/
theorem centralPaddedCx_separated_of_target_absent (c : P.CrossCoeff)
    (hb : ¬StepValid (dn i) true t) (N : ℕ) :
    P.CentralPaddedCxSeparatedAt i t Z E hdot c N := by
  have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (dn i) a t)
      (fun a => E.obj (P.centralTargetFactor i t Z a)) true) := by
    simpa only [sectorFamilyCorner, dite_eq_right hb] using Limits.isZero_zero C
  exact hz.eq_of_tgt _ _

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

import Mathlib.Tactic.Abel
import OddMath.QuiverHecke.CyclotomicAction.ProbePaddedVacuum.ProbeEvenCentralBend
import OddMath.QuiverHecke.CyclotomicAction.ProbePaddedVacuum.ProbePaddedVacuumCapInverse
import OddMath.QuiverHecke.SwappedAssembly.PointwiseLeftwardInverse
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseCapInverse

/-!
# Probe padded vacuum

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The padded Dx bend on the regular vacuum probe

SwappedHomInversion §3 (4)–(5) and SwappedVacuumCoordinates §4:
evaluate the specified padded mixed entry at the vacuum sector. Its
finite ordered expansion has the same raw dots, normalized pre-cap and
reservoir unit as the evaluated vacuum bend.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
set_option quotPrecheck false
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u
local instance paddedVacuumBendHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private theorem bendFunctorEnd_nilpotent_congr
    {C A : Type*} [Category C] [Preadditive C] [Category A] [Preadditive A]
    {E F : C ⥤ A} [E.Additive] [F.Additive] (h : E = F)
    {U : C} (a : End U) (ha : IsNilpotent (bendFunctorEnd E U a)) :
    IsNilpotent (bendFunctorEnd F U a) := by
  subst F
  exact ha

private theorem mapped_square {C A : Type*} [Category C] [Category A]
    (E : C ⥤ A) {X Y U V : C} {a : X ⟶ Y} {b : U ⟶ V}
    (s : X ≅ U) (t : Y ≅ V) (h : a ≫ t.hom = s.hom ≫ b) :
    E.map a ≫ (E.mapIso t).hom = (E.mapIso s).hom ≫ E.map b := by
  simpa only [Functor.map_comp, Functor.mapIso_hom] using congrArg E.map h

private theorem finite_weighted_sum_congr {M : Type*} [AddCommGroup M]
    (f g : ℕ → M) (q : ℤ) (N : ℕ) (h : ∀ r, f r = g r) :
    (-∑ r ∈ Finset.range N, q ^ (r + 1) • f r) =
      -∑ r ∈ Finset.range N, q ^ (r + 1) • g r := by
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro r hr
  exact congrArg (fun w => q ^ (r + 1) • w) (h r)

private theorem finite_series_charts {C : Type*} [Category C] [Preadditive C]
    {A B X Y U V : C} (s : A ≅ X) (t : B ≅ Y) (u : X ≅ U) (v : Y ≅ V)
    (a : ℕ → (X ⟶ Y)) (b : ℕ → (U ⟶ V)) (q : ℤ) (N : ℕ)
    (h : ∀ r, a r ≫ v.hom = u.hom ≫ b r) :
    (-∑ r ∈ Finset.range N, q ^ (r + 1) • (s.hom ≫ a r ≫ t.inv)) ≫ (t ≪≫ v).hom =
      (s ≪≫ u).hom ≫ (-∑ r ∈ Finset.range N, q ^ (r + 1) • b r) := by
  simp only [Iso.trans_hom, Preadditive.neg_comp, Preadditive.sum_comp,
    Preadditive.zsmul_comp, Preadditive.comp_neg, Preadditive.comp_sum,
    Preadditive.comp_zsmul, Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [h r]

private theorem finite_series_charts_attach {C : Type*} [Category C] [Preadditive C]
    {A B X Y U V U' V' : C} (s : A ≅ X) (t : B ≅ Y) (u : X ≅ U) (v : Y ≅ V)
    (e : U ≅ U') (f : V ≅ V') (a : ℕ → (X ⟶ Y)) (b : ℕ → (U ⟶ V))
    (q : ℤ) (N : ℕ) (h : ∀ r, a r ≫ v.hom = u.hom ≫ b r)
    (d : U' ⟶ V')
    (hb : (-∑ r ∈ Finset.range N, q ^ (r + 1) • b r) ≫ f.hom = e.hom ≫ d)
    (z : A ⟶ B)
    (hz : z = -∑ r ∈ Finset.range N, q ^ (r + 1) • (s.hom ≫ a r ≫ t.inv)) :
    z ≫ (t ≪≫ v ≪≫ f).hom = (s ≪≫ u ≪≫ e).hom ≫ d := by
  rw [hz]
  have hh := finite_series_charts s t u v a b q N h
  calc
    _ = ((-∑ r ∈ Finset.range N, q ^ (r + 1) • (s.hom ≫ a r ≫ t.inv)) ≫
        (t ≪≫ v).hom) ≫ f.hom := by simp only [Iso.trans_hom, Category.assoc]
    _ = ((s ≪≫ u).hom ≫ (-∑ r ∈ Finset.range N, q ^ (r + 1) • b r)) ≫ f.hom :=
      congrArg (fun w => w ≫ f.hom) hh
    _ = (s ≪≫ u ≪≫ e).hom ≫ d := by
      rw [Category.assoc, hb]
      simp only [Iso.trans_hom, Category.assoc]

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance paddedVacuumZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β, elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

omit [Fintype I] in
private theorem probeWeight_zero : ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muP (((0, 0) : Sector I)) = ΛP := by
  simp [ProbeReservoir.muP, elvProbeReservoir]
omit [Fintype I] in
private theorem reservoirWeight_zero : ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muM (((0, 0) : Sector I)) = -ΛR := by
  simp [ProbeReservoir.muM, elvProbeReservoir]

omit [Fintype I] in
private theorem homContentEvaluation_weight
    {a a' b b' : X} (h₁ : a = a') (h₂ : b = b')
    (M : (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T)).obj (-a')) (δ : WeightBlocks D ΛR b') :
    (SKM.homWeightEquivalence ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T) ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W) h₁ h₂).functor ⋙
        homContentEvaluation D (parameterTwist D Sc) cutoff bound ΛR b' ((((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T)).obj (-a')) M δ =
      homContentEvaluation D (parameterTwist D Sc) cutoff bound ΛR b ((((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T)).obj (-a))
        ((Pi.eqToEquivalence (fun x : X => (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T)).obj (-x)) h₁).inverse.obj M)
        (⟨δ.1, δ.2.trans h₂.symm⟩ : WeightBlocks D ΛR b) := by
  subst a'
  subst b'
  rfl

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶ elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))

/-- The full given tensor input, through only its formal zero-sector weight chart. -/
def vacuumSectorInput : ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).H (((0, 0) : Sector I)) := by
  exact ((SKM.homWeightEquivalence ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T) ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W) (probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) (reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR))).inverse.obj (preCapInput D (parameterTwist D Sc) m ΛP hcP (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H)

private def normalVacuumEvaluation :
    SKM.homWeightSector ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T).obj ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W).obj ΛP (-ΛR) ⥤
      ContentModules D (parameterTwist D Sc) cutoff bound (0 : Multiset I) :=
  homContentEvaluation D (parameterTwist D Sc) cutoff bound ΛR (-ΛR)
    (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T).obj (-ΛP)) (regularProbe D (parameterTwist D Sc) m ΛP) (emptyBlock D ΛR)
private instance normalVacuumEvaluation_additive : ((normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR)).Additive :=
  homContentEvaluation_additive D (parameterTwist D Sc) cutoff bound ΛR (-ΛR)
    (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T).obj (-ΛP)) (regularProbe D (parameterTwist D Sc) m ΛP) (emptyBlock D ΛR)

/-- The evaluation retains all Hom maps before selecting the regular
probe and empty output block; its first factor only changes weight presentations. -/
def vacuumSectorEvaluation := ((SKM.homWeightEquivalence ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T) ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W) (probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) (reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR))).functor ⋙ (normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR)
instance vacuumSectorEvaluation_additive : ((vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR)).Additive := inferInstanceAs (((SKM.homWeightEquivalence ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T) ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W) (probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) (reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR))).functor ⋙ (normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR)).Additive

def sectorRegular : ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).T.obj (-((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muP (((0, 0) : Sector I))) :=
  (Pi.eqToEquivalence (fun x : X => (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T)).obj (-x)) (probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR)).inverse.obj (regularProbe D (parameterTwist D Sc) m ΛP)
def sectorEmpty : WeightBlocks D ΛR (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muM (((0, 0) : Sector I))) :=
  ⟨0, (emptyBlock D ΛR).2.trans ((reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR)).symm⟩

theorem vacuumSectorEvaluation_eq : (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) =
    elvProbeBendOutputEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR (((0, 0) : Sector I))
      (sectorRegular D Sc m cutoff bound ΛP ΛR hcP hcR)
      (sectorEmpty D Sc m cutoff bound ΛP ΛR hcP hcR) :=
  homContentEvaluation_weight D Sc m cutoff bound ΛP ΛR hcP hcR (probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) (reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) (regularProbe D (parameterTwist D Sc) m ΛP) (emptyBlock D ΛR)

variable (i : I)

private theorem factorDotIso [Fact Sc.PureNilpotent] {a b : X} (h : a + D.α i = b) : IsIso (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).T.dot i h) :=
  (isUnit_iff_isIso _).mp
    (elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hcP hcR i h)

/-- The source comparison includes the prescribed padded corner,
the weight equality chart and the literal normalized vacuum pre-cap chart. -/
def paddedVacuumSourceIso [Fact Sc.PureNilpotent] :=
  ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralSourceCornerIso i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) ⟨true, by trivial⟩ ≪≫
    ((normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR)).mapIso (SKM.homPreWeightPullbackIso ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T) ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W) (probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) (reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) i (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muP_preE i (((0, 0) : Sector I))) (preCapInput D (parameterTwist D Sc) m ΛP hcP (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H)) ≪≫
      vacuumPreBlockSourceIso D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP i ((show -ΛP + D.α i = -((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muP (nextSector (true,i) true (((0, 0) : Sector I))) from (congrArg (fun x : X => -x + D.α i) ((probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR))).symm.trans (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muP_preE i (((0, 0) : Sector I))))) H

/-- The target comparison includes the prescribed padded corner,
the weight equality chart and the literal reservoir unit/dot target chart. -/
def paddedVacuumTargetIso :=
  ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralTargetCornerIso i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) ⟨false, by trivial⟩ ≪≫
    ((normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR)).mapIso (SKM.homPostWeightPullbackIso ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T) ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W) (probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) (reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) i (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muM_postF i (((0, 0) : Sector I))) 0 (preCapInput D (parameterTwist D Sc) m ΛP hcP (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H)) ≪≫
      vacuumPostTarget D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR i ((show -ΛR + D.α i = ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muM (nextSector (false,i) false (((0, 0) : Sector I))) from (congrArg (fun x : X => x + D.α i) ((reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR))).symm.trans (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muM_postF i (((0, 0) : Sector I))))) 0 H

private theorem normalVacuumEvaluation_map
    {F G : SKM.homWeightSector
      (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T.obj
      (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W.obj ΛP (-ΛR)} (η : F ⟶ G) :
    (normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map η =
      η.total (regularProbe D (parameterTwist D Sc) m ΛP) (emptyBlock D ΛR) := rfl

variable (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound)

private theorem paddedVacuumDx_odd_at [Fact Sc.PureNilpotent]
    (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) (n : ℕ)
    (hn : ProbeVacuumCap.diagonalPostDot D (parameterTwist D Sc) m cutoff bound i (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ n = 0)
    (hDx : ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).CentralPaddedDxSeparatedAt i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) (2 * n)) :
    ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralPaddedSigma (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
        (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom ≫
        ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := by
  classical
  let P := elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
  let E := vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let E₀ := normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let Z := vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H
  let Z₀ := preCapInput D (parameterTwist D Sc) m ΛP hcP
    (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H
  let ha := probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let hb := reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let ep := P.muP_preE i (0, 0)
  let er := P.muM_postF i (0, 0)
  let ep₀ := (congrArg (fun x : X => -x + D.α i) ha).symm.trans ep
  let er₀ := (congrArg (fun x : X => x + D.α i) hb).symm.trans er
  let : E.Additive := vacuumSectorEvaluation_additive D Sc m cutoff bound ΛP ΛR hcP hcR
  let := factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i ep
  let := factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i ep₀
  let s := P.centralSourceCornerIso i (0, 0) Z E ⟨true, by trivial⟩
  let t := P.centralTargetCornerIso i (0, 0) Z E ⟨false, by trivial⟩
  let u := E₀.mapIso (SKM.homPreWeightPullbackIso P.T P.W ha hb i ep Z₀)
  let v := E₀.mapIso (SKM.homPostWeightPullbackIso P.T P.W ha hb i er 0 Z₀)
  let e := vacuumPreBlockSourceIso D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP i ep₀ H
  let f := vacuumPostTarget D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR i er₀ 0 H
  let a (r : ℕ) := E.map (SKM.homPreNegativeCap P.T P.W.obj i (P.muM (0, 0)) ep (r + 1) Z ≫
    SKM.homContentPostCup P.T.obj P.W i 0 (P.muP (0, 0)) er r Z)
  let b (r : ℕ) := E₀.map (SKM.homPreNegativeCap P.T P.W.obj i (-ΛR) ep₀ (r + 1) Z₀ ≫
    SKM.homContentPostCup P.T.obj P.W i 0 ΛP er₀ r Z₀)
  have hw (r : ℕ) : a r ≫ v.hom = u.hom ≫ b r := by
    have h := SKM.homCapCup_weight_pullback_square P.T P.W ha hb i ep er 0 Z₀
      (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (r + 1) r
    have hm := mapped_square E₀ _ _ h
    simpa only [a, b, u, v, E, Z, Z₀, vacuumSectorEvaluation, vacuumSectorInput,
      Functor.comp_map] using hm
  have hn := vacuumBendWordSum_odd D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR
    i ep₀ er₀ 0 H hP hi n hn
  have hn' : (-∑ r ∈ Finset.range (2 * n), (koszulSign (D.parity i) (D.parity i)) ^ (r + 1) • b r) ≫
      f.hom = e.hom ≫ ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
        (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := by
    have hsum : (-∑ r ∈ Finset.range (2 * n), (koszulSign (D.parity i) (D.parity i)) ^ (r + 1) • b r) =
        vacuumBendWordSum D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR
          i ep₀ er₀ 0 H (2 * n) := by
      dsimp only [vacuumBendWordSum]
      apply finite_weighted_sum_congr
      intro r
      dsimp only [b, E₀]
      exact normalVacuumEvaluation_map D Sc m cutoff bound ΛP ΛR hcP hcR _
    rw [hsum]
    exact hn
  have hs := finite_series_charts_attach s t u v e f a b
    (koszulSign (D.parity i) (D.parity i)) (2 * n) hw _ hn' _
    (P.centralPaddedDx_word_series i (0, 0) Z E
      (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i)
      (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) (2 * n) hDx)
  simpa only [s, t, u, v, e, f, E, E₀, Z, Z₀, P,
    paddedVacuumSourceIso, paddedVacuumTargetIso] using hs

/-- The prescribed padded Dx entry at the vacuum sector is the
evaluated odd vacuum bend through its displayed source and target charts.
Both finite-series bounds are constructed from nilpotence of the appended
dot for the twisted parameters; no endpoint, moment or bend compatibility is assumed. -/
theorem paddedVacuumDx_odd [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) :
    ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralPaddedSigma (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
        (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom ≫
        ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := by
  let := (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muP_preE i (((0, 0) : Sector I)))
  have hA := elvProbeDxOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hcP hcR i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (sectorRegular D Sc m cutoff bound ΛP ΛR hcP hcR)
    (sectorEmpty D Sc m cutoff bound ΛP ΛR hcP hcR)
    hdot
  simp only [probeToReservoirBendCoefficientEvaluation, RingHom.comp_apply] at hA
  let : (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).Additive :=
    vacuumSectorEvaluation_additive D Sc m cutoff bound ΛP ΛR hcP hcR
  have hA' := bendFunctorEnd_nilpotent_congr
    (vacuumSectorEvaluation_eq D Sc m cutoff bound ΛP ΛR hcP hcR).symm _ hA
  obtain ⟨nA, hnA⟩ := hA' 
  obtain ⟨nB, _positive, hnB⟩ := ProbeVacuumCap.diagonalPostDot_pow_zero D (parameterTwist D Sc) m cutoff bound
    hdot i
  let n := max nA nB
  have ha' := pow_eq_zero_of_le (Nat.le_max_left nA nB) hnA
  have hb' := pow_eq_zero_of_le (Nat.le_max_right nA nB) (hnB (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
  have hD := probeToReservoirBend_odd_separated ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)) i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot)
    (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hcP hcR hdot) hi n ha'
  exact paddedVacuumDx_odd_at D Sc m cutoff bound ΛP ΛR hcP hcR H i hdot hP hi n hb'
    (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralPaddedDx_separated i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) (2 * n) hD)

private theorem paddedVacuumDx_even_at [Fact Sc.PureNilpotent]
    (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0) (n : ℕ)
    (hn : ProbeVacuumCap.diagonalPostDot D (parameterTwist D Sc) m cutoff bound i (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ n = 0)
    (hDx : ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).CentralPaddedDxSeparatedAt i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) n) :
    ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralPaddedSigma (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
        (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom ≫
        ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := by
  classical
  let P := elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
  let E := vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let E₀ := normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let Z := vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H
  let Z₀ := preCapInput D (parameterTwist D Sc) m ΛP hcP
    (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H
  let ha := probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let hb := reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let ep := P.muP_preE i (0, 0)
  let er := P.muM_postF i (0, 0)
  let ep₀ := (congrArg (fun x : X => -x + D.α i) ha).symm.trans ep
  let er₀ := (congrArg (fun x : X => x + D.α i) hb).symm.trans er
  let : E.Additive := vacuumSectorEvaluation_additive D Sc m cutoff bound ΛP ΛR hcP hcR
  let := factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i ep
  let := factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i ep₀
  let s := P.centralSourceCornerIso i (0, 0) Z E ⟨true, by trivial⟩
  let t := P.centralTargetCornerIso i (0, 0) Z E ⟨false, by trivial⟩
  let u := E₀.mapIso (SKM.homPreWeightPullbackIso P.T P.W ha hb i ep Z₀)
  let v := E₀.mapIso (SKM.homPostWeightPullbackIso P.T P.W ha hb i er 0 Z₀)
  let e := vacuumPreBlockSourceIso D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP i ep₀ H
  let f := vacuumPostTarget D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR i er₀ 0 H
  let a (r : ℕ) := E.map (SKM.homPreNegativeCap P.T P.W.obj i (P.muM (0, 0)) ep (r + 1) Z ≫
    SKM.homContentPostCup P.T.obj P.W i 0 (P.muP (0, 0)) er r Z)
  let b (r : ℕ) := E₀.map (SKM.homPreNegativeCap P.T P.W.obj i (-ΛR) ep₀ (r + 1) Z₀ ≫
    SKM.homContentPostCup P.T.obj P.W i 0 ΛP er₀ r Z₀)
  have hw (r : ℕ) : a r ≫ v.hom = u.hom ≫ b r := by
    have h := SKM.homCapCup_weight_pullback_square P.T P.W ha hb i ep er 0 Z₀
      (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (r + 1) r
    have hm := mapped_square E₀ _ _ h
    simpa only [a, b, u, v, E, Z, Z₀, vacuumSectorEvaluation, vacuumSectorInput,
      Functor.comp_map] using hm
  have hn := vacuumBendWordSum_even D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR
    i ep₀ er₀ 0 H hP hi n hn
  have hn' : (-∑ r ∈ Finset.range n, (koszulSign (D.parity i) (D.parity i)) ^ (r + 1) • b r) ≫
      f.hom = e.hom ≫ ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
        (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := by
    have hsum : (-∑ r ∈ Finset.range n, (koszulSign (D.parity i) (D.parity i)) ^ (r + 1) • b r) =
        vacuumBendWordSum D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR
          i ep₀ er₀ 0 H n := by
      dsimp only [vacuumBendWordSum]
      apply finite_weighted_sum_congr
      intro r
      dsimp only [b, E₀]
      exact normalVacuumEvaluation_map D Sc m cutoff bound ΛP ΛR hcP hcR _
    rw [hsum]
    exact hn
  have hs := finite_series_charts_attach s t u v e f a b
    (koszulSign (D.parity i) (D.parity i)) n hw _ hn' _
    (P.centralPaddedDx_word_series i (0, 0) Z E
      (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i)
      (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) n hDx)
  simpa only [s, t, u, v, e, f, E, E₀, Z, Z₀, P,
    paddedVacuumSourceIso, paddedVacuumTargetIso] using hs

/-- Even colour: the prescribed padded Dx entry at the vacuum sector is the
evaluated even vacuum bend through its displayed source and target charts.
Both finite-series bounds are constructed from nilpotence of the appended
dot for the twisted parameters; no endpoint, moment or bend compatibility is assumed. -/
theorem paddedVacuumDx_even [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0) :
    ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralPaddedSigma (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
        (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom ≫
        ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := by
  let := (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muP_preE i (((0, 0) : Sector I)))
  have hA := elvProbeDxOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hcP hcR i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (sectorRegular D Sc m cutoff bound ΛP ΛR hcP hcR)
    (sectorEmpty D Sc m cutoff bound ΛP ΛR hcP hcR)
    hdot
  simp only [probeToReservoirBendCoefficientEvaluation, RingHom.comp_apply] at hA
  let : (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).Additive :=
    vacuumSectorEvaluation_additive D Sc m cutoff bound ΛP ΛR hcP hcR
  have hA' := bendFunctorEnd_nilpotent_congr
    (vacuumSectorEvaluation_eq D Sc m cutoff bound ΛP ΛR hcP hcR).symm _ hA
  obtain ⟨nA, hnA⟩ := hA' 
  obtain ⟨nB, _positive, hnB⟩ := ProbeVacuumCap.diagonalPostDot_pow_zero D (parameterTwist D Sc) m cutoff bound
    hdot i
  let n := max nA nB
  have ha' := pow_eq_zero_of_le (Nat.le_max_left nA nB) hnA
  have hb' := pow_eq_zero_of_le (Nat.le_max_right nA nB) (hnB (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
  have hD := probeToReservoirBend_even_separated ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)) i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot)
    (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hcP hcR hdot) hi n ha'
  exact paddedVacuumDx_even_at D Sc m cutoff bound ΛP ΛR hcP hcR H i hdot hP hi n hb'
    (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralPaddedDx_separated i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) n hD)

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end

section

/-! # The padded reservoir cap rows on the regular vacuum probe

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8. The cap rows of the positive two-sector matrix at the vacuum sector are
the prescribed padded reservoir caps `centralPaddedCap true n`: the raw
reservoir dot `n` times, followed by the normalized pre-Hom counit. This
file evaluates them on the regular probe. Through the same source chart as
the padded Dx entry (`paddedVacuumSourceIso`), and the weight, block and
regular-input charts of the target, the `n`-th cap row is the native
`x ^ n ≫ v`, where `x` is the shifted pre dot and `v` the shifted pre cap
(`paddedVacuumCap_eq`). No parity, moment or cap compatibility is
assumed.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
set_option quotPrecheck false
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u
local instance paddedVacuumCapHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

section Generic

private theorem total_pow_square {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F : Superfunctor k C A} (f : End F) (N : C) {B : A} (e : F.obj N ⟶ B) (y : End B)
    (h : f.total N ≫ e = e ≫ y) (n : ℕ) :
    (f ^ n).total N ≫ e = e ≫ (y ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, End.one_def, End.one_def]
    exact (congrArg (fun w => w ≫ e) (SuperNatTrans.id_total F.toFunctor N)).trans
      ((Category.id_comp e).trans (Category.comp_id e).symm)
  | succ n ih =>
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def, Superfunctor.comp_total,
      Category.assoc, ih, ← Category.assoc, h, Category.assoc]

/-- Chart bookkeeping for a cap row: a pulled-back square, a block
selection and a normalized native identity compose. -/
private theorem cap_charts_attach {C : Type*} [Category C]
    {A X U U₀ U' Y V V' : C} (s : A ≅ X) (u : X ≅ U) (hU : U = U₀) (e : U₀ ≅ U')
    (c : X ⟶ Y) (p : Y ⟶ V) (q : V ⟶ V') (c₀ : U ⟶ V) (c₁ : U₀ ⟶ V) (d : U' ⟶ V')
    (hsq : c ≫ p = u.hom ≫ c₀) (hE : c₀ = eqToHom hU ≫ c₁) (hn : c₁ ≫ q = e.hom ≫ d) :
    (s.hom ≫ c) ≫ p ≫ q = (s ≪≫ u ≪≫ (eqToIso hU ≪≫ e)).hom ≫ d := by
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [reassoc_of% hsq, hE, Category.assoc, hn]

private def reservoirRow {k : Type u} [CommRing k]
    {A B R : PiSCat.{u,u,u+1} k} (E : A ⟶ B) (F : B ⟶ A) (Z : A ⟶ R)
    (σ : ZMod 2) (z : ℤ) (f : E ⟶ E) (g : E ≫ F ⟶ 𝟙 A) :
    (SKM.homPre (k := k) E).obj ((SKM.homParityShift (k := k) (C := B ⟶ R) σ).obj (F ≫ Z)) ⟶ Z :=
  z • (E ◁ ((SKM.homParityShiftDatum (k := k) σ).iso (F ≫ Z)).hom ≫
    f ▷ (F ≫ Z) ≫ g ▷ Z)

private theorem reservoirCap_row
    {I X k : Type u} [AddCommGroup X] [CommRing k] {D : SKM.Datum I X}
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (W : X → PiSCat.{u,u,u+1} k) (i : I) (x : X) {a b : X}
    (edge : -a + D.α i = -b) (n : ℕ) (Z : T.obj (-a) ⟶ W x) :
    SKM.homReservoirCap T W i x edge n Z =
      reservoirRow (R := W x) (T.E i edge) (T.F i edge) Z
        (SKM.leftAdjParity D i (-a))
        (koszulSign (SKM.leftAdjParity D i (-a)) (1 + (n : ZMod 2) * D.parity i))
        (SKM.rouquierPower (T.dot i edge) n)
        (((((T.leftAdjScalar i (-a))⁻¹ : kˣ) : k)) • T.leftCap i edge) := by
  rw [SKM.homReservoirCap_coordinates]
  unfold reservoirRow
  erw [PiSCat.associator_inv, PiSCat.leftUnitor_hom, Category.comp_id, Category.id_comp]

private theorem reservoirRow_block
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (δ : WeightBlocks D Λ x)
    {A B : PiSCat.{u,u,u+1} k} (E : A ⟶ B) (F : B ⟶ A)
    (Z : A ⟶ elvWeightSpace D Sc cutoff bound Λ x) (N : A)
    (σ : ZMod 2) (z : ℤ) (f : E ⟶ E) (g : E ≫ F ⟶ 𝟙 A)
    (hSrc : (((SKM.homPre (k := k) E).obj
        ((SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ x) σ).obj
          (F ≫ Z))).obj N) δ =
      ((SKM.homPre (k := k) E).obj
        ((SKM.homParityShift (k := k) (C := B ⟶ contentModuleTarget D Sc cutoff bound δ.1) σ).obj
          (F ≫ Z.comp (elvBlockEval D Sc cutoff bound Λ δ)))).obj N) :
    ((reservoirRow (R := elvWeightSpace D Sc cutoff bound Λ x) E F Z σ z f g).total N) δ =
      eqToHom hSrc ≫ (reservoirRow (R := contentModuleTarget D Sc cutoff bound δ.1) E F
        (Z.comp (elvBlockEval D Sc cutoff bound Λ δ)) σ z f g).total N := by
  fin_cases σ
  all_goals
    have hh : hSrc = rfl := Subsingleton.elim _ _
    rw [hh]
    simp only [eqToHom_refl, Category.id_comp]
    rfl

/-- Selecting an output block of the whole weight space commutes with
every dotted reservoir cap, through the block source chart. -/
theorem reservoirCap_block
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (δ : WeightBlocks D Λ x)
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (i : I) {a b : X} (edge : -a + D.α i = -b)
    (Z : T.obj (-a) ⟶ elvWeightSpace D Sc cutoff bound Λ x) (N : T.obj (-a))
    (hSrc : (((SKM.homContentPreE T (elvWeightSpace D Sc cutoff bound Λ) i x edge).obj
        ((SKM.homContentPreF T (elvWeightSpace D Sc cutoff bound Λ) i x edge).obj Z)).obj N) δ =
      ((SKM.homContentPreE T (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge).obj
        ((SKM.homContentPreF T (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge).obj
          (Z.comp (elvBlockEval D Sc cutoff bound Λ δ)))).obj N)
    (n : ℕ) :
    (SKM.homReservoirCap T (elvWeightSpace D Sc cutoff bound Λ) i x edge n Z).total N δ =
      eqToHom hSrc ≫ (SKM.homReservoirCap T
        (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge n
        (Z.comp (elvBlockEval D Sc cutoff bound Λ δ))).total N := by
  rw [reservoirCap_row, reservoirCap_row]
  exact reservoirRow_block D Sc cutoff bound Λ x δ (T.E i edge) (T.F i edge) Z N
    (SKM.leftAdjParity D i (-a))
    (koszulSign (SKM.leftAdjParity D i (-a)) (1 + (n : ZMod 2) * D.parity i))
    (SKM.rouquierPower (T.dot i edge) n)
    (((((T.leftAdjScalar i (-a))⁻¹ : kˣ) : k)) • T.leftCap i edge) hSrc

end Generic

section Regular

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ) (Λ : X)
  (hc : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)
  (W : X → PiSCat.{u,u,u+1} k) (muM : X) (i : I) {muP : X}
  (h : -Λ + D.α i = -muP) (H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ W muM)
local notation "T" => probeOldRouquierFamily D Sc m Λ hc
local notation "N₀" => regularProbe D Sc m Λ
local notation "Z" => preCapInput D Sc m Λ hc W muM H

/-- Every prescribed dotted reservoir cap on the regular probe is the native
`x ^ n ≫ v` through the normalized pre-cap source chart. No parity is used. -/
theorem vacuumPreReservoirCap_eq (hP : 0 < probeCutoff D m i) (n : ℕ) :
    (SKM.homReservoirCap T W i muM h n Z).total N₀ ≫
      H.map (eqToHom (emptyProbe_regular D Sc m Λ)) =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D Sc m (W muM) i hP H := by
  rw [SKM.homReservoirCap, Superfunctor.comp_total, Category.assoc,
    vacuumPreCounit_eq D Sc m Λ hc W muM i h H hP, ← Category.assoc,
    total_pow_square _ _ _ _ (vacuumPreDot_source D Sc m Λ hc W muM i h H hP) n,
    Category.assoc]

end Regular

section Pullback

variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : SKM.Datum I X}
  (T W : SKM.RouquierFamily (k := k) (B := B) D)
  {a a' b b' : X} (ha : a = a') (hb : b = b')
  (Z' : SKM.homWeightSector T.obj W.obj a' b')

/-- A pulled-back input returns to itself under the weight equivalence. -/
def capPullbackSelfIso :
    (SKM.homWeightEquivalence T W ha hb).functor.obj
      ((SKM.homWeightEquivalence T W ha hb).inverse.obj Z') ≅ Z' := by
  subst a'
  subst b'
  exact Iso.refl _

/-- The dotted reservoir cap on a pulled-back input is the cap on the
normalized input, through the source pullback chart and the return chart. -/
theorem homReservoirCap_weight_pullback_square (i : I) {c : X}
    (hp : -a + D.α i = -c) (n : ℕ) :
    (SKM.homWeightEquivalence T W ha hb).functor.map
        (SKM.homReservoirCap T W.obj i b hp n
          ((SKM.homWeightEquivalence T W ha hb).inverse.obj Z')) ≫
      (capPullbackSelfIso T W ha hb Z').hom =
    (SKM.homPreWeightPullbackIso T W ha hb i hp Z').hom ≫
      SKM.homReservoirCap T W.obj i b' (show -a' + D.α i = -c from ha ▸ hp) n Z' := by
  subst a'
  subst b'
  change SKM.homReservoirCap T W.obj i b hp n Z' ≫ 𝟙 _ =
    𝟙 _ ≫ SKM.homReservoirCap T W.obj i b hp n Z'
  simp only [Category.comp_id, Category.id_comp]

end Pullback

section Padded

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance paddedCapZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR

omit [Fintype I] in
private theorem capProbeWeight_zero : (P).muP (((0, 0) : Sector I)) = ΛP := by
  simp [ProbeReservoir.muP, elvProbeReservoir]
omit [Fintype I] in
private theorem capReservoirWeight_zero : (P).muM (((0, 0) : Sector I)) = -ΛR := by
  simp [ProbeReservoir.muM, elvProbeReservoir]

private def capVacuumEvaluation :
    SKM.homWeightSector (P).T.obj (P).W.obj ΛP (-ΛR) ⥤
      ContentModules D (parameterTwist D Sc) cutoff bound (0 : Multiset I) :=
  homContentEvaluation D (parameterTwist D Sc) cutoff bound ΛR (-ΛR)
    ((P).T.obj (-ΛP)) (regularProbe D (parameterTwist D Sc) m ΛP) (emptyBlock D ΛR)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))

/-- The cap target comparison: return the pulled-back vacuum input to the
normalized input, then apply the regular-input chart of the output block. -/
def paddedVacuumCapTargetIso :=
  (capVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).mapIso
      (capPullbackSelfIso (P).T (P).W
        (capProbeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR)
        (capReservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR)
        (preCapInput D (parameterTwist D Sc) m ΛP hcP
          (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H)) ≪≫
    (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).toFunctor.mapIso
      (eqToIso (emptyProbe_regular D (parameterTwist D Sc) m ΛP))

/-- The prescribed padded reservoir cap row `n` at the vacuum sector is the
native `x ^ n ≫ v` of the output block, through the same source chart as the
padded Dx entry. No parity, moment or cap compatibility is assumed. -/
theorem paddedVacuumCap_eq [Fact Sc.PureNilpotent] (i : I) (hP : 0 < probeCutoff D m i) (n : ℕ) :
    (P).centralPaddedCap i (((0, 0) : Sector I))
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true n ≫
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom =
    (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom ≫
      (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := by
  classical
  let PR := elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
  let E₀ := capVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let Z := vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H
  let E := vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let Z₀ := preCapInput D (parameterTwist D Sc) m ΛP hcP
    (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H
  let ha := capProbeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let hb := capReservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let ep := PR.muP_preE i (0, 0)
  let ep₀ : -ΛP + D.α i = -PR.muP (nextSector (true, i) true (((0, 0) : Sector I))) :=
    (congrArg (fun x : X => -x + D.α i) ha).symm.trans ep
  let B₀ := vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H
  let W₀ : X → PiSCat.{u,u,u+1} k :=
    fun _ => contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)
  let N₀ := regularProbe D (parameterTwist D Sc) m ΛP
  let s := PR.centralSourceCornerIso i (0, 0) Z E ⟨true, by trivial⟩
  let u := E₀.mapIso (SKM.homPreWeightPullbackIso PR.T PR.W ha hb i ep Z₀)
  let e := vacuumPreSourceIso D (parameterTwist D Sc) m ΛP hcP W₀ (-ΛR) i ep₀ B₀
  let c := E₀.map ((SKM.homWeightEquivalence PR.T PR.W ha hb).functor.map
    (SKM.homReservoirCap PR.T PR.W.obj i (PR.muM (0, 0)) ep n
      ((SKM.homWeightEquivalence PR.T PR.W ha hb).inverse.obj Z₀)))
  let p := E₀.map (capPullbackSelfIso PR.T PR.W ha hb Z₀).hom
  let q := B₀.toFunctor.map (eqToHom (emptyProbe_regular D (parameterTwist D Sc) m ΛP))
  let c₀ := E₀.map (SKM.homReservoirCap PR.T PR.W.obj i (-ΛR) ep₀ n Z₀)
  let c₁ := (SKM.homReservoirCap (probeOldRouquierFamily D (parameterTwist D Sc) m ΛP hcP)
    W₀ i (-ΛR) ep₀ n (preCapInput D (parameterTwist D Sc) m ΛP hcP W₀ (-ΛR) B₀)).total N₀
  let d := (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
      (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i B₀ ^ n) ≫
    ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
      (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP B₀
  have hsq : c ≫ p = u.hom ≫ c₀ := by
    have h := congrArg E₀.map
      (homReservoirCap_weight_pullback_square PR.T PR.W ha hb Z₀ i ep n)
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  have hSrc : (((SKM.homContentPreE PR.T (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR)
        i (-ΛR) ep₀).obj ((SKM.homContentPreF PR.T
          (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) i (-ΛR) ep₀).obj Z₀)).obj
        N₀) (emptyBlock D ΛR) =
      ((SKM.homContentPreE PR.T W₀ i (-ΛR) ep₀).obj ((SKM.homContentPreF PR.T W₀ i (-ΛR) ep₀).obj
            (preCapInput D (parameterTwist D Sc) m ΛP hcP W₀ (-ΛR) B₀))).obj N₀ := by
    simp only [SKM.homContentPreF, Functor.comp_obj, SKM.homParityShift]
    split_ifs <;> rfl
  have hE0 := reservoirCap_block D (parameterTwist D Sc) cutoff bound ΛR (-ΛR) (emptyBlock D ΛR)
      PR.T i ep₀ Z₀ N₀ hSrc n
  have hc₀ : c₀ = (SKM.homReservoirCap PR.T PR.W.obj
      i (-ΛR) ep₀ n Z₀).total N₀ (emptyBlock D ΛR) := by
    simp only [c₀, E₀, N₀, capVacuumEvaluation, homContentEvaluation, Functor.comp_map,
      Pi.eval_map, homTotalEvaluation]
  have hc₁ : (SKM.homReservoirCap PR.T
        (fun _ => contentModuleTarget D (parameterTwist D Sc) cutoff bound (emptyBlock D ΛR).1)
        i (-ΛR) ep₀ n
        (Z₀.comp (elvBlockEval D (parameterTwist D Sc) cutoff bound ΛR (emptyBlock D ΛR)))).total N₀
      = c₁ := rfl
  have hE : c₀ = eqToHom hSrc ≫ c₁ := by
    rw [hc₀, ← hc₁]
    exact hE0
  have hn : c₁ ≫ q = e.hom ≫ d :=
    vacuumPreReservoirCap_eq D (parameterTwist D Sc) m ΛP hcP W₀ (-ΛR) i ep₀ B₀ hP n
  have hs := cap_charts_attach s u hSrc e c p q c₀ c₁ d hsq hE hn
  have hcap : PR.centralPaddedCap i (((0, 0) : Sector I)) Z E true n = s.hom ≫ c := by
    unfold ProbeReservoir.centralPaddedCap
    rw [dite_eq_left_of_eq_true (eq_true (show StepValid (SKM.up i) true (((0, 0) : Sector I)) from
      by trivial))]
    rfl
  have hsrc : (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      (s ≪≫ u ≪≫ (eqToIso hSrc ≪≫ e)).hom := rfl
  have htgt : (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom = p ≫ q := rfl
  rw [hcap, htgt, hsrc]
  exact hs
end Padded

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end

section

/-! # The leftward vacuum cap inverse in the native chart

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

`vacuumCapInverse_odd` transports a cap inverse of the vacuum window to the
native chart, but only existentially. Here the inverse is the one given by any
leftward data satisfying the positive inverse equations at the vacuum sector
(`isCapInverse_centralPadded_of_posInverseAt`), evaluated directly by the vacuum
sector evaluation. Its columns are explicit: the dotted leftward cups, conjugated
by the source and cap-target charts (`vacuumLeftwardCapInverse_odd`).
Consequently every product of a column with a native cap row `x ^ N ≫ v` is the
conjugated evaluation of the left bubble entry `dcup n ≫ ε xᴺ`
(`vacuumLeftwardColumn_cap_eq`). No inverse, moment or bubble value is assumed.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct

namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u

local instance leftwardVacuumCapInverseHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance leftwardVacuumCapInverseZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "ν₀" => (P).wt ((0, 0) : Sector I)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))
variable (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (i : I)
local notation "p₀" => SPath.centralUpDn i (SKM.wt D ν₀ [SKM.dn i]) ν₀ ((0, 0) : Sector I)
  ⟨true, trivial⟩

/-- The explicit native column `n` of the leftward vacuum cap inverse: the dotted
leftward cup, evaluated by the vacuum sector evaluation and conjugated by the
padded source, corner and cap-target charts. -/
def vacuumLeftwardColumn [Fact Sc.PureNilpotent] (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj Z ⟶ ((P).pathFunctor p).obj Z) (n : ℕ) := by
  subst hZ
  exact (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).inv ≫
    (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
        (dc n (.nil _) p₀ ≫ ((P).centralSourceFactorIso i ν₀ ((0, 0) : Sector I)
          (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ⟨true, trivial⟩).inv) ≫
      ((P).centralSourceCornerIso i ((0, 0) : Sector I)
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) ⟨true, trivial⟩).inv ≫
    (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom

include hdot in
/-- **The leftward vacuum cap inverse in the native chart (odd colour).** Leftward
data satisfying the positive inverse equations at the vacuum sector give an
entrywise inverse of the native cap window `[bend; x ^ n ≫ v]_(n < h)` of the
evaluated A6 bend, whose columns are the explicit `vacuumLeftwardColumn`. -/
theorem vacuumLeftwardCapInverse_odd [Fact Sc.PureNilpotent] (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (HP : (P).PosInverseAt (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) :
    ∃ j, ProbeWindow.IsCapInverse
        (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
        (fun n : Fin (D.h i ν₀).toNat => (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ (n : ℕ)) ≫
          ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H)) j
        (fun n => vacuumLeftwardColumn D Sc m cutoff bound ΛP ΛR hcP hcR H i Z hZ dc n) := by
  subst hZ
  have hu : ¬StepValid (SKM.up i) false ((0, 0) : Sector I) := by
    simp [StepValid]
  have hd : ¬StepValid (SKM.dn i) true ((0, 0) : Sector I) := by
    simp [StepValid]
  have h₁ := (P).isCapInverse_centralPadded_of_posInverseAt
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀ ((0, 0) : Sector I)
    (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) lc dc HP hu hd
  have h₃ := (h₁.coordinates (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm
    (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm).target
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H)
  have hs : (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
      (P).centralPaddedSigma (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i
        ((0, 0) : Sector I) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
      (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
        (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) :=
    (Iso.inv_comp_eq _).2 (paddedVacuumDx_odd D Sc m cutoff bound ΛP ΛR hcP hcR H i
      hdot hP hi)
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
  exact ⟨_, h₃⟩

/-- **Column moments are bubble entries.** The native column `n` of the leftward
vacuum cap inverse followed by the native cap row `x ^ N ≫ v` is the evaluated left
bubble entry `dcup n ≫ ε xᴺ`, conjugated by the cap-target chart. -/
theorem vacuumLeftwardColumn_cap_eq [Fact Sc.PureNilpotent]
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ⟶
        ((P).pathFunctor p).obj (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H))
    (cc : (P).CrossCoeff) (hP : 0 < probeCutoff D m i) (n N : ℕ) :
    vacuumLeftwardColumn D Sc m cutoff bound ΛP ΛR hcP hcR H i _ rfl dc n ≫
        (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ N) ≫
        ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) =
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).inv ≫
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
          (dc n (.nil _) p₀ ≫ (P).epsEntry cc i N ν₀ p₀ (.nil _)
            (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)) ≫
        (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom := by
  simp only [vacuumLeftwardColumn, Category.assoc]
  rw [← paddedVacuumCap_eq D Sc m cutoff bound ΛP ΛR hcP hcR H i hP N,
    (P).map_dcup_epsEntry_eq_padded cc i ν₀ ((0, 0) : Sector I)
      (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
      (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (dc n (.nil _) p₀) N]
  simp only [Category.assoc]

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end

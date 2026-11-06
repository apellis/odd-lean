import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumBendSeries
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeFiniteBends
import OddMath.QuiverHecke.SwappedAssembly.Sigma.BendWindowEquations
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCentralBend
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedBendWordSeries
import OddMath.SKM.RouquierHomWeightCoordinates

/-! # The padded Dx bend on the regular vacuum probe

SwappedHomInversion §3 (4)–(5) and SwappedVacuumCoordinates §4:
evaluate the specified padded mixed entry at the vacuum sector. Its
finite ordered expansion has the same raw dots, normalized pre-cap and
reservoir unit as the evaluated vacuum bend.
-/
noncomputable section
set_option quotPrecheck false
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
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

private theorem factorDotIso {a b : X} (h : a + D.α i = b) : IsIso (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).T.dot i h) :=
  (isUnit_iff_isIso _).mp
    (elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hcP hcR i h)

/-- The source comparison includes the prescribed padded corner,
the weight equality chart and the literal normalized vacuum pre-cap chart. -/
def paddedVacuumSourceIso :=
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

private theorem paddedVacuumDx_odd_at
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
theorem paddedVacuumDx_odd (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) :
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

private theorem paddedVacuumDx_even_at
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
theorem paddedVacuumDx_even (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0) :
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

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum

import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumBendMonomials
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeSeparatedBends
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
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u
local instance paddedVacuumBendHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "T" => probeOldRouquierFamily D Sc' m ΛP hcP
local notation "W" => elvRouquierFamily D Sc' cutoff bound ΛR hcR
local notation "t₀" => ((0, 0) : Sector I)
local notation "N₀" => regularProbe D Sc' m ΛP
local notation "δ₀" => emptyBlock D ΛR
local notation "R₀" => contentModuleTarget D Sc' cutoff bound (0 : Multiset I)

omit [Fintype I] in
private instance paddedVacuumZero : Limits.HasZeroObject R₀ :=
  ⟨⟨elvZeroModule D Sc' cutoff bound 0, elvZeroModule_isZero D Sc' cutoff bound 0⟩⟩

private theorem probeWeight_zero : (P).muP t₀ = ΛP := by
  simp [ProbeReservoir.muP, elvProbeReservoir]
private theorem reservoirWeight_zero : (P).muM t₀ = -ΛR := by
  simp [ProbeReservoir.muM, elvProbeReservoir]
local notation "ha" => probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "hb" => reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "K" => SKM.homWeightEquivalence T W ha hb

private theorem homContentEvaluation_weight
    {a a' b b' : X} (h₁ : a = a') (h₂ : b = b')
    (M : (T).obj (-a')) (δ : WeightBlocks D ΛR b') :
    (SKM.homWeightEquivalence T W h₁ h₂).functor ⋙
        homContentEvaluation D Sc' cutoff bound ΛR b' ((T).obj (-a')) M δ =
      homContentEvaluation D Sc' cutoff bound ΛR b ((T).obj (-a))
        ((Pi.eqToEquivalence (fun x : X => (T).obj (-x)) h₁).inverse.obj M)
        (⟨δ.1, δ.2.trans h₂.symm⟩ : WeightBlocks D ΛR b) := by
  subst a'
  subst b'
  rfl

variable (H : ProbeVacuumCap.modulePiCategory D Sc' m ⟶ (W).obj (-ΛR))
local notation "Z₀" => preCapInput D Sc' m ΛP hcP (elvWeightSpace D Sc' cutoff bound ΛR) (-ΛR) H
local notation "H₀" => vacuumBendBlock D Sc' m cutoff bound ΛR hcR H

/-- The full given tensor input, through only its formal zero-sector weight chart. -/
def vacuumSectorInput : (P).H t₀ := (K).inverse.obj Z₀
local notation "Z" => vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H

private def normalVacuumEvaluation :=
  homContentEvaluation D Sc' cutoff bound ΛR (-ΛR)
    (probeOldWeightSpace D Sc' m ΛP (-ΛP)) N₀ δ₀
local notation "E₀" => normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR

/-- The evaluation retains all Hom maps before selecting the regular
probe and empty output block; its first factor only changes weight presentations. -/
def vacuumSectorEvaluation := (K).functor ⋙ E₀
local notation "E" => vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
instance : (E).Additive := inferInstanceAs ((K).functor ⋙ E₀).Additive

def sectorRegular : (P).T.obj (-(P).muP t₀) :=
  (Pi.eqToEquivalence (fun x : X => (T).obj (-x)) ha).inverse.obj N₀
def sectorEmpty : WeightBlocks D ΛR ((P).muM t₀) :=
  ⟨0, (emptyBlock D ΛR).2.trans hb.symm⟩

theorem vacuumSectorEvaluation_eq : E =
    elvProbeBendOutputEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR t₀
      (sectorRegular D Sc m cutoff bound ΛP ΛR hcP hcR)
      (sectorEmpty D Sc m cutoff bound ΛP ΛR hcP hcR) :=
  homContentEvaluation_weight D Sc m cutoff bound ΛP ΛR hcP hcR ha hb N₀ δ₀

variable (i : I)
local notation "ep" => (P).muP_preE i t₀
local notation "er" => (P).muM_postF i t₀
local notation "ep₀" => (show -ΛP + D.α i = -(P).muP (nextSector (true,i) true t₀) from ha ▸ ep)
local notation "er₀" => (show -ΛR + D.α i = (P).muM (nextSector (false,i) false t₀) from hb ▸ er)

private theorem factorDotIso {a b : X} (h : a + D.α i = b) : IsIso ((P).T.dot i h) :=
  (isUnit_iff_isIso _).mp
    (elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hcP hcR i h)
local notation "hd" => factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i

/-- The source comparison includes the prescribed padded corner,
the weight equality chart and the literal normalized vacuum pre-cap chart. -/
def paddedVacuumSourceIso :=
  (P).centralSourceCornerIso i t₀ Z E ⟨true, by trivial⟩ ≪≫
    E₀.mapIso (SKM.homPreWeightPullbackIso T W ha hb i ep Z₀) ≪≫
      vacuumPreBlockSourceIso D Sc' m cutoff bound ΛP ΛR hcP hcR i ep₀ H

/-- The target comparison includes the prescribed padded corner,
the weight equality chart and the literal reservoir unit/dot target chart. -/
def paddedVacuumTargetIso :=
  (P).centralTargetCornerIso i t₀ Z E ⟨false, by trivial⟩ ≪≫
    E₀.mapIso (SKM.homPostWeightPullbackIso T W ha hb i er 0 Z₀) ≪≫
      vacuumPostTarget D Sc' m cutoff bound ΛP ΛR hcP hcR i er₀ 0 H

private theorem paddedWord_square (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1)
    (n r : ℕ) :
    (E).map (letI := hd ep;
      SKM.homPreNegativeCap (P).T (P).W.obj i ((P).muM t₀) ep n Z ≫
        SKM.homContentPostCup (P).T.obj (P).W i 0 ((P).muP t₀) er r Z) ≫
      (E₀.mapIso (SKM.homPostWeightPullbackIso T W ha hb i er 0 Z₀)).hom ≫
        (vacuumPostTarget D Sc' m cutoff bound ΛP ΛR hcP hcR i er₀ 0 H).hom =
    (E₀.mapIso (SKM.homPreWeightPullbackIso T W ha hb i ep Z₀)).hom ≫
      (vacuumPreBlockSourceIso D Sc' m cutoff bound ΛP ΛR hcP hcR i ep₀ H).hom ≫
        (Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc' m R₀ i H₀) ^ n) ≫
          ProbeVacuumCap.shiftedPreCap D Sc' m R₀ i hP H₀ ≫
            (adjunction (contentAppend D Sc' cutoff bound (0 : Multiset I) [i])).unit.app
              ((H₀).obj (probeOldVacuumRegular D Sc' m)) ≫
            restrictedDotEnd (contentAppend D Sc' cutoff bound (0 : Multiset I) [i])
              (canonicalAppendDot_supernatural D Sc' cutoff bound (0 : Multiset I) i)
              ((H₀).obj (probeOldVacuumRegular D Sc' m)) ^ r := by
  have h := SKM.homCapCup_weight_pullback_square T W ha hb i ep er 0 Z₀ hd n r
  have he := congrArg E₀.map h
  simp only [Functor.map_comp, ← Functor.mapIso_hom] at he
  change ((E).map _ ≫ _) ≫ _ = _
  rw [he, Category.assoc]
  congr 1
  exact vacuumBendMonomial_native D Sc' m cutoff bound ΛP ΛR hcP hcR i ep₀ er₀ 0 H hP hi n r

private theorem negative_odd_coefficient (r : ℕ) :
    -((-1 : ℤ) ^ (r + 1)) = (-1 : ℤ) ^ r := by
  rw [pow_succ]
  ring

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
local notation "c" => elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc

private theorem paddedVacuumDx_odd_at
    (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) (n : ℕ)
    (hn : ProbeVacuumCap.diagonalPostDot D Sc' m cutoff bound i H₀ ^ n = 0)
    (hDx : (P).CentralPaddedDxSeparatedAt i t₀ Z E hd c (2 * n)) :
    (P).centralPaddedSigma c i t₀ Z E true false ≫
        (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom ≫
        ProbeVacuumCap.evaluatedMixedBend D Sc' m cutoff bound i hP H₀ := by
  classical
  rw [(P).centralPaddedDx_word_series i t₀ Z E hd c (2 * n) hDx,
    ProbeVacuumCap.evaluatedMixedBend_odd_expansion D Sc' m cutoff bound i hi hP H₀ n hn]
  simp only [paddedVacuumTargetIso, paddedVacuumSourceIso, Iso.trans_hom,
    Functor.mapIso_hom, Preadditive.neg_comp, Preadditive.sum_comp,
    Preadditive.zsmul_comp, Preadditive.comp_sum, Preadditive.comp_zsmul,
    Category.assoc, Iso.inv_hom_id_assoc, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← neg_zsmul, hi, koszulSign_one_one, negative_odd_coefficient]
  congr 1
  simpa only [Category.assoc, Functor.mapIso_hom] using
    congrArg (fun f => ((P).centralSourceCornerIso i t₀ Z E ⟨true, by trivial⟩).hom ≫ f)
      (paddedWord_square D Sc m cutoff bound ΛP ΛR hcP hcR H i hP hi (r + 1) r)

/-- The prescribed padded Dx entry at the vacuum sector is the
evaluated odd vacuum bend through its displayed source and target charts.
Both finite-series bounds are constructed from homogeneous symmetrizable
reservoir parameters; no endpoint, moment or bend compatibility is assumed. -/
theorem paddedVacuumDx_odd (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) :
    (P).centralPaddedSigma c i t₀ Z E true false ≫
        (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom ≫
        ProbeVacuumCap.evaluatedMixedBend D Sc' m cutoff bound i hP H₀ := by
  let := hd ep
  have hA := elvProbeDxOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hcP hcR i t₀ Z
    (sectorRegular D Sc m cutoff bound ΛP ΛR hcP hcR)
    (sectorEmpty D Sc m cutoff bound ΛP ΛR hcP hcR) sy hc
  rw [← vacuumSectorEvaluation_eq D Sc m cutoff bound ΛP ΛR hcP hcR] at hA
  obtain ⟨nA, hnA⟩ := hA
  obtain ⟨nB, _positive, hnB⟩ := ProbeVacuumCap.diagonalPostDot_pow_zero D Sc' m cutoff bound
    sy (parameterTwist_homogeneous D Sc hc) i
  let n := max nA nB
  have ha' := pow_eq_zero_of_le (Nat.le_max_left nA nB) hnA
  have hb' := pow_eq_zero_of_le (Nat.le_max_right nA nB) (hnB H₀)
  have hD := probeToReservoirBend_odd_separated (P) i t₀ Z E c
    (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hcP hcR sy hc) hi n ha'
  exact paddedVacuumDx_odd_at D Sc m cutoff bound ΛP ΛR hcP hcR H i sy hc hP hi n hb'
    ((P).centralPaddedDx_separated i t₀ Z E hd c (2 * n) hD)

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum

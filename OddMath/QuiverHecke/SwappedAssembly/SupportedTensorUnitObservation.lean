import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorEntryPullback
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorWordQuotientObservation

/-! # Canonical cyclic-unit observation of the supported tensor matrix

SwappedVacuumCoordinates §§3–7: the literal original-weight row is
observed on its prescribed source unit, through the global path charts.
No layer decomposition or generator-comparison premise enters the map.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorUnitObservationHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
private def chartAtOriginalWeight {k J I : Type u} [CommRing k]
    (A : PiSCat.{u,u,u + 1} k) (C : J → PiSCat.{u,u,u + 1} k)
    (W : (x : J) → List I → C x) {x y : J} (h : x = y)
    (F : A ⟶ C x) (G : A ⟶ C y) (hFG : HEq F G) (R : A) (ν : List I)
    (e : G.obj R ≅ W y ν) : F.obj R ≅ W x ν := by
  subst y
  cases hFG
  exact e

private theorem chartAtOriginalWeight_hom_heq {k J I : Type u} [CommRing k]
    (A : PiSCat.{u,u,u + 1} k) (C : J → PiSCat.{u,u,u + 1} k)
    (W : (x : J) → List I → C x) {x y : J} (h : x = y)
    (F : A ⟶ C x) (G : A ⟶ C y) (hFG : HEq F G) (R : A) (ν : List I)
    (e : G.obj R ≅ W y ν) :
    HEq (chartAtOriginalWeight A C W h F G hFG R ν e).hom e.hom := by
  subst y
  cases hFG
  rfl

private theorem chartAtOriginalWeight_even {k J I : Type u} [CommRing k]
    (A : PiSCat.{u,u,u + 1} k) (C : J → PiSCat.{u,u,u + 1} k)
    (W : (x : J) → List I → C x) {x y : J} (h : x = y)
    (F : A ⟶ C x) (G : A ⟶ C y) (hFG : HEq F G) (R : A) (ν : List I)
    (e : G.obj R ≅ W y ν) (he : e.hom ∈ parity (R := k) _ _ 0) :
    (chartAtOriginalWeight A C W h F G hFG R ν e).hom ∈ parity (R := k) _ _ 0 := by
  subst y
  cases hFG
  exact he

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "R₀" => WeightTensorVacuum.regularProbe D Tw m ΛP

/-- The global path chart at its original reservoir weight, retaining
all content blocks rather than selecting a weight representative. -/
def tensorPathValueChart {l : List (Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hup : ∀ a ∈ l, a.l.1 = true) :
    (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p hup).obj R₀ ≅
      PowerWordWeight.wordFamily D Tw cutoff L ΛR (ReservoirWord.weight D ΛR c)
        ((l.map (fun a => a.l.2)).reverse) := by
  have hw := TensorReservoirWords.path_weight D ΛR p hup
  have hF := TensorReservoirWords.pathHom_heq D Tw m cutoff L ΛP ΛR p hup
  generalize hν : (l.map (fun a => a.l.2)).reverse = ν at hw hF ⊢
  exact chartAtOriginalWeight (probeOldWeightSpace D Tw m ΛP (-ΛP))
    (fun x => elvWeightSpace D Tw cutoff N ΛR x)
    (PowerWordWeight.wordFamily D Tw cutoff L ΛR) hw
    (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p hup)
    (TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν) hF R₀ ν
    (TensorVacuumWords.chart D Tw m cutoff L ΛP ΛR ν)

/-- The original-weight supported path chart retains the global word chart
under its proved endpoint and whole-functor transports. -/
theorem tensorPathValueChart_global_heq {l : List (Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hup : ∀ a ∈ l, a.l.1 = true) :
    HEq (tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom
      (TensorVacuumWords.chart D Tw m cutoff L ΛP ΛR
        (l.map (fun a => a.l.2)).reverse).hom := by
  unfold tensorPathValueChart
  dsimp only
  apply chartAtOriginalWeight_hom_heq

/-- The global path chart is even in every original content block. -/
theorem tensorPathValueChart_hom_mem {l : List (Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hup : ∀ a ∈ l, a.l.1 = true) :
    (tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom ∈ parity (R := k) _ _ 0 := by
  unfold tensorPathValueChart
  dsimp only
  apply chartAtOriginalWeight_even
  exact TensorVacuumWords.chart_even D Tw m cutoff L ΛP ΛR (l.map (fun a => a.l.2)).reverse

omit [Fintype I] in
/-- Reading the literal source labels recovers the specified source word. -/
theorem tensorSourceLabels_colors (s : List I) :
    (tensorSourceLabels D ΛP ΛR s).map (fun a => a.l.2) = s := by
  induction s with
  | nil => rfl
  | cons i s ih =>
    simpa only [tensorSourceLabels, upWord, List.map_cons, wd_cons] using congrArg (List.cons i) ih

variable (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "cS" => tensorSourceContent D ΛP ΛR s

/-- The source word's exact content, inside the original reservoir weight. -/
def tensorSourceWordBlock : WeightBlocks D ΛR (ReservoirWord.weight D ΛR cS) :=
  ⟨s.reverse, by
    have h := TensorReservoirWords.path_weight D ΛR (tensorSourcePath D ΛP ΛR s)
      (tensorSourceLabels_up D ΛP ΛR s)
    simpa only [tensorSourceLabels_colors] using h.symm⟩

/-- The same source path chart with its literal source-word labels read. -/
def tensorSourcePathValueChart :
    (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR (tensorSourcePath D ΛP ΛR s)
      (tensorSourceLabels_up D ΛP ΛR s)).obj R₀ ≅
      PowerWordWeight.wordFamily D Tw cutoff L ΛR (ReservoirWord.weight D ΛR cS) s.reverse :=
  tensorPathValueChart D Sc m cutoff ΛP ΛR L (tensorSourcePath D ΛP ΛR s)
    (tensorSourceLabels_up D ΛP ΛR s) ≪≫
      eqToIso (congrArg (PowerWordWeight.wordFamily D Tw cutoff L ΛR
        (ReservoirWord.weight D ΛR cS))
          (congrArg List.reverse (tensorSourceLabels_colors D ΛP ΛR s)))

/-- The cyclic source unit in the unchanged original-input source functor. -/
def tensorOriginalSourceUnit :
    (((tensorOriginalRowSource D Sc m cutoff ΛP ΛR L s).obj R₀)
      (tensorSourceWordBlock D ΛP ΛR s)).obj
        (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl) :=
  (((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).inv.total R₀)
    (tensorSourceWordBlock D ΛP ΛR s)).total
      (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)
      ((moduleIsoLinearEquiv (Pi.isoApp (tensorSourcePathValueChart D Sc m cutoff ΛP ΛR L s)
        (tensorSourceWordBlock D ΛP ΛR s))
        (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)).symm
          (PowerWordYoneda.unitVector D Tw cutoff L s.reverse))

/-- The actual supported tensor matrix observed through its canonical
original-input row and global path chart, on its canonical cyclic source unit. -/
def tensorMatrixQuotientObservation {a : Obj (SKM.sig D)}
    (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = a.endR)
    (p : SPath a.word (0,cS) (0,0)) (hup : ∀ c ∈ a.word, c.l.1 = true)
    (x : matrixModule D Sc m cutoff N ΛP ΛR
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L) a) :=
  PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (a.word.map (fun a => a.l.2))
    ((((tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom
      (tensorSourceWordBlock D ΛP ΛR s)).total
        (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl))
      (((((tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s hEnd p hup x).total R₀)
        (tensorSourceWordBlock D ΛP ΛR s)).total
          (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl))
            (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s)))

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors

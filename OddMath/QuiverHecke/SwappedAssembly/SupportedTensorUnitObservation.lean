import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorEntryPullback
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumWords
import OddMath.QuiverHecke.HalfTurn.PowerWordQuotientCoordinates

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
private structure ModuleChart {k : Type u} [CommRing k] {C : Type u} [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (M N : Superfunctor k C (SVec k)) (forward : M ⟶ N) (backward : N ⟶ M) where
  iso : M ≅ N
  hom_eq : iso.hom = forward
  inv_eq : iso.inv = backward

private theorem moduleChart_comp_apply {k : Type u} [CommRing k] {C : Type u} [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M N P : Superfunctor k C (SVec k)} (f : M ⟶ N) (g : N ⟶ P) {backward : P ⟶ M}
    (c : ModuleChart M P (f ≫ g) backward) (w : C) (z : M.obj w) :
    moduleIsoLinearEquiv c.iso w z = g.total w (f.total w z) := by
  change c.iso.hom.total w z = _
  rw [c.hom_eq,Superfunctor.comp_total]
  rfl

private def tensorValueIso {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) {F G : A ⟶ B} (e : F ≅ G) (R : A) :
    F.obj R ≅ G.obj R where
  hom := e.hom.total R
  inv := e.inv.total R
  hom_inv_id := by
    rw [← Superfunctor.comp_total,e.hom_inv_id]
    exact SuperNatTrans.id_total F.toFunctor R
  inv_hom_id := by
    rw [← Superfunctor.comp_total,e.inv_hom_id]
    exact SuperNatTrans.id_total G.toFunctor R

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

private def wordVectorEquiv (ν ρ : List I) :
    (PowerWordWeight.wordAt D Tw cutoff L ν (ρ : Multiset I)).obj
      (PowerWordContentCyclicity.wordObject D Tw cutoff L ρ (ρ : Multiset I) rfl) ≃ₗ[k]
    (powerWordModule D Tw cutoff L ν).obj (OldCategory.mk ρ) := LinearEquiv.refl k _

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

private opaque tensorSourceModuleChart :
    ModuleChart
      (((tensorOriginalRowSource D Sc m cutoff ΛP ΛR L s).obj R₀)
        (tensorSourceWordBlock D ΛP ΛR s))
      ((PowerWordWeight.wordFamily D Tw cutoff L ΛR (ReservoirWord.weight D ΛR cS) s.reverse)
        (tensorSourceWordBlock D ΛP ΛR s))
      ((((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom.total R₀)
        (tensorSourceWordBlock D ΛP ΛR s)) ≫
        (tensorSourcePathValueChart D Sc m cutoff ΛP ΛR L s).hom
          (tensorSourceWordBlock D ΛP ΛR s))
      ((tensorSourcePathValueChart D Sc m cutoff ΛP ΛR L s).inv
        (tensorSourceWordBlock D ΛP ΛR s) ≫
        (((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).inv.total R₀)
          (tensorSourceWordBlock D ΛP ΛR s))) :=
  ⟨Pi.isoApp (tensorValueIso (probeOldWeightSpace D Tw m ΛP (-ΛP))
    (elvWeightSpace D Tw cutoff N ΛR (ReservoirWord.weight D ΛR cS))
    (tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s) R₀)
      (tensorSourceWordBlock D ΛP ΛR s) ≪≫
    Pi.isoApp (tensorSourcePathValueChart D Sc m cutoff ΛP ΛR L s)
      (tensorSourceWordBlock D ΛP ΛR s), rfl, rfl⟩

/-- The original-weight source module isomorphism through the whole
source chart and the normalized global word chart. -/
def tensorOriginalSourceModuleIso :=
  (tensorSourceModuleChart D Sc m cutoff ΛP ΛR L hP hR s).iso

private theorem tensorSourceModuleIso_hom :
    (tensorOriginalSourceModuleIso D Sc m cutoff ΛP ΛR L hP hR s).hom =
      (((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom.total R₀)
        (tensorSourceWordBlock D ΛP ΛR s)) ≫
        (tensorSourcePathValueChart D Sc m cutoff ΛP ΛR L s).hom
          (tensorSourceWordBlock D ΛP ΛR s) :=
  (tensorSourceModuleChart D Sc m cutoff ΛP ΛR L hP hR s).hom_eq

private theorem tensorSourceModuleIso_inv :
    (tensorOriginalSourceModuleIso D Sc m cutoff ΛP ΛR L hP hR s).inv =
      (tensorSourcePathValueChart D Sc m cutoff ΛP ΛR L s).inv
        (tensorSourceWordBlock D ΛP ΛR s) ≫
        (((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).inv.total R₀)
          (tensorSourceWordBlock D ΛP ΛR s)) :=
  (tensorSourceModuleChart D Sc m cutoff ΛP ΛR L hP hR s).inv_eq

/-- The old-word unit in the exact original-weight source-word value space. -/
def tensorSourceWordUnit :
    ((PowerWordWeight.wordFamily D Tw cutoff L ΛR (ReservoirWord.weight D ΛR cS) s.reverse)
      (tensorSourceWordBlock D ΛP ΛR s)).obj
      (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl) :=
  (wordVectorEquiv D Sc cutoff L s.reverse s.reverse).symm
    (PowerWordYoneda.unitVector D Tw cutoff L s.reverse)

theorem tensorSourceWordUnit_formula :
    tensorSourceWordUnit D Sc cutoff ΛP ΛR L s =
      PowerWordYoneda.unitVector D Tw cutoff L s.reverse := rfl

attribute [local irreducible] tensorOriginalSourceModuleIso

/-- The prescribed source unit, pulled back through the entire source
module chart. -/
def tensorOriginalSourceUnit :=
  (moduleIsoLinearEquiv (tensorOriginalSourceModuleIso D Sc m cutoff ΛP ΛR L hP hR s)
    (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)).symm
    (tensorSourceWordUnit D Sc cutoff ΛP ΛR L s)

/-- The whole source module chart sends the prescribed source unit to
the source-word unit in its exact value space. -/
theorem tensorOriginalSourceUnit_value :
    moduleIsoLinearEquiv (tensorOriginalSourceModuleIso D Sc m cutoff ΛP ΛR L hP hR s)
      (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)
      (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s) =
      tensorSourceWordUnit D Sc cutoff ΛP ΛR L s :=
  (moduleIsoLinearEquiv (tensorOriginalSourceModuleIso D Sc m cutoff ΛP ΛR L hP hR s)
    (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)).apply_symm_apply _

/-- The module chart evaluates every vector by the literal whole source
chart followed by the normalized global word chart. -/
theorem tensorOriginalSourceModuleIso_apply
    (z : (((tensorOriginalRowSource D Sc m cutoff ΛP ΛR L s).obj R₀)
      (tensorSourceWordBlock D ΛP ΛR s)).obj
        (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)) :
    moduleIsoLinearEquiv (tensorOriginalSourceModuleIso D Sc m cutoff ΛP ΛR L hP hR s)
      (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl) z =
      (((tensorSourcePathValueChart D Sc m cutoff ΛP ΛR L s).hom
        (tensorSourceWordBlock D ΛP ΛR s)).total
          (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl))
        ((((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom.total R₀)
          (tensorSourceWordBlock D ΛP ΛR s)).total
            (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl) z) := by
  unfold tensorOriginalSourceModuleIso
  exact moduleChart_comp_apply
    (((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom.total R₀)
      (tensorSourceWordBlock D ΛP ΛR s))
    ((tensorSourcePathValueChart D Sc m cutoff ΛP ΛR L s).hom
      (tensorSourceWordBlock D ΛP ΛR s))
    (tensorSourceModuleChart D Sc m cutoff ΛP ΛR L hP hR s)
    (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl) z

private def proofProposition {P : Prop} (_ : P) : Prop := P

/-- The unchanged whole source chart and normalized global word chart
send the canonical source unit to its exact original-weight word unit. -/
theorem tensorOriginalSourceUnit_wordValue :
    proofProposition ((tensorOriginalSourceModuleIso_apply D Sc m cutoff ΛP ΛR L hP hR s
      (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s)).symm.trans
        (tensorOriginalSourceUnit_value D Sc m cutoff ΛP ΛR L hP hR s)) :=
  (tensorOriginalSourceModuleIso_apply D Sc m cutoff ΛP ΛR L hP hR s
    (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s)).symm.trans
    (tensorOriginalSourceUnit_value D Sc m cutoff ΛP ΛR L hP hR s)

/-- The source unit agrees exactly with the prescribed inverse whole
source and inverse global word-chart formula. -/
theorem tensorOriginalSourceUnit_formula :
    tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s =
      (((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).inv.total R₀)
        (tensorSourceWordBlock D ΛP ΛR s)).total
          (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)
          ((moduleIsoLinearEquiv (Pi.isoApp (tensorSourcePathValueChart D Sc m cutoff ΛP ΛR L s)
            (tensorSourceWordBlock D ΛP ΛR s))
            (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)).symm
              (PowerWordYoneda.unitVector D Tw cutoff L s.reverse)) := by
  unfold tensorOriginalSourceUnit
  change (tensorOriginalSourceModuleIso D Sc m cutoff ΛP ΛR L hP hR s).inv.total _
    (tensorSourceWordUnit D Sc cutoff ΛP ΛR L s) = _
  rw [tensorSourceModuleIso_inv,Superfunctor.comp_total,tensorSourceWordUnit_formula]
  rfl

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

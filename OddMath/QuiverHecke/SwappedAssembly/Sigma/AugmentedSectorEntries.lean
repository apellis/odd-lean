import OddMath.QuiverHecke.SwappedAssembly.Sigma.AugmentedSectorChart
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SectorFamilyEntries
import OddMath.QuiverHecke.SwappedAssembly.Sigma.ProbePrincipal
import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirToProbeBend
import OddMath.QuiverHecke.SwappedAssembly.ProbeDottedFactorCoordinates

/-! # The prescribed entries of the central two-sector chart

The finite path enumeration is eliminated before the native factor
objects are substituted. Thus the chart retains the chosen principal
mates, both mixed bends, and every dotted cap/unit entry of
Brundan–Ellis (1.13)–(1.14), with their prescribed signs.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM Classical
open scoped ZeroObject
private theorem mappedIsoEntry {A C : Type*} [Category A] [Category C]
    (E : A ⥤ C) {X Y U V : A} {S T : C}
    (e : X ≅ U) (e' : Y ≅ V) (s : S ≅ E.obj X) (t : T ≅ E.obj Y) (f : X ⟶ Y) :
    (s ≪≫ E.mapIso e).hom ≫ E.map (e.inv ≫ f ≫ e'.hom) ≫
      (t ≪≫ E.mapIso e').inv = s.hom ≫ E.map f ≫ t.inv := by
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.map_comp]
  change (s.hom ≫ (E.mapIso e).hom) ≫
    ((E.mapIso e).inv ≫ E.map f ≫ (E.mapIso e').hom) ≫
    (E.mapIso e').inv ≫ t.inv = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem mappedIsoCap {A C : Type*} [Category A] [Category C]
    (E : A ⥤ C) {X U Z : A} {S : C}
    (e : X ≅ U) (s : S ≅ E.obj X) (f : X ⟶ Z) :
    (s ≪≫ E.mapIso e).hom ≫ E.map (e.inv ≫ f) ≫ 𝟙 (E.obj Z) =
      s.hom ≫ E.map f := by
  simp only [Iso.trans_hom, Functor.map_comp]
  change (s.hom ≫ (E.mapIso e).hom) ≫
    ((E.mapIso e).inv ≫ E.map f) ≫ 𝟙 (E.obj Z) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id]

private theorem mappedIsoUnit {A C : Type*} [Category A] [Category C]
    (E : A ⥤ C) {Y V Z : A} {T : C}
    (e : Y ≅ V) (t : T ≅ E.obj Y) (f : Z ⟶ Y) :
    𝟙 (E.obj Z) ≫ E.map (f ≫ e.hom) ≫ (t ≪≫ E.mapIso e).inv =
      E.map f ≫ t.inv := by
  simp only [Iso.trans_inv, Functor.map_comp]
  change 𝟙 (E.obj Z) ≫ (E.map f ≫ (E.mapIso e).hom) ≫
    (E.mapIso e).inv ≫ t.inv = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Category.id_comp]

universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)
local instance entryPathFintype (w : List (Col I X)) (s t : Sector I) : Fintype (SPath w s t) :=
  Fintype.ofFinite _

variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]

/-- The inverse source index is the prescribed pure cap path. -/
theorem centralSourceIndex_symm_inl (i : I) (ν : X) (t : Sector I)
    (a : {a : Bool // StepValid (up i) a t}) :
    (centralSourceIndex (D := D) i ν t).symm (.inl a) =
      SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t a := rfl

/-- The inverse augmented target index is the prescribed pure cup path. -/
theorem centralAugTargetIndex_symm_inl (i : I) (ν : X) (t : Sector I) (n : ℕ)
    (a : {a : Bool // StepValid (dn i) a t}) :
    (centralAugTargetIndex (D := D) i ν t n).symm (.inl a) =
      .inl (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t a) := rfl

/-- The inverse target index is the prescribed pure cup path. -/
theorem centralTargetIndex_symm_inl (i : I) (ν : X) (t : Sector I)
    (a : {a : Bool // StepValid (dn i) a t}) :
    (centralTargetIndex (D := D) i ν t).symm (.inl a) =
      SPath.centralDnUp i (SKM.wt D ν [up i]) ν t a := rfl

/-- The inverse augmented source index is the prescribed pure cap path. -/
theorem centralAugSourceIndex_symm_inl (i : I) (ν : X) (t : Sector I) (n : ℕ)
    (a : {a : Bool // StepValid (up i) a t}) :
    (centralAugSourceIndex (D := D) i ν t n).symm (.inl a) =
      .inl (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t a) := rfl

/-- An augmented source window retains its actual empty path. -/
theorem centralAugSourceIndex_symm_inr (i : I) (ν : X) (t : Sector I) (n : ℕ) (r : Fin n) :
    (centralAugSourceIndex (D := D) i ν t n).symm (.inr r) = .inr (r, .nil t) := rfl

/-- An augmented target window retains its actual empty path. -/
theorem centralAugTargetIndex_symm_inr (i : I) (ν : X) (t : Sector I) (n : ℕ) (r : Fin n) :
    (centralAugTargetIndex (D := D) i ν t n).symm (.inr r) = .inr (r, .nil t) := rfl

/-- Restore a present source corner from its conditional zero padding. -/
def centralSourceCornerIso (i : I) (t : Sector I) (Z : P.H t) (E : P.H t ⥤ C)
    (a : {a : Bool // StepValid (up i) a t}) :
    sectorFamilyCorner (fun a => StepValid (up i) a t)
      (fun a => E.obj (P.centralSourceFactor i t Z a)) a.1 ≅
      E.obj (P.centralSourceFactor i t Z a) :=
  eqToIso (by simp only [sectorFamilyCorner, dite_eq_left a.2])

/-- Restore a present target corner from its conditional zero padding. -/
def centralTargetCornerIso (i : I) (t : Sector I) (Z : P.H t) (E : P.H t ⥤ C)
    (a : {a : Bool // StepValid (dn i) a t}) :
    sectorFamilyCorner (fun a => StepValid (dn i) a t)
      (fun a => E.obj (P.centralTargetFactor i t Z a)) a.1 ≅
      E.obj (P.centralTargetFactor i t Z a) :=
  eqToIso (by simp only [sectorFamilyCorner, dite_eq_left a.2])

/-- A present source slot restores exactly its selected native factor. -/
def centralSourceSlotIso {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : I) (t : Sector I) (Z : P.H t) (E : P.H t ⥤ C)
    (a : {a : Bool // StepValid (up i) a t}) :
    (sectorFamilyObject (ι := ι) (fun a => StepValid (up i) a t)
      (fun a => E.obj (P.centralSourceFactor i t Z a)) (E.obj Z)).X
        (sectorFamilyIndex (.inl a : Sum {a : Bool // StepValid (up i) a t} ι)) ≅
    E.obj (P.centralSourceFactor i t Z a) := by
  rcases a with ⟨a, ha⟩
  cases a
  · exact P.centralSourceCornerIso i t Z E ⟨false, ha⟩
  · exact P.centralSourceCornerIso i t Z E ⟨true, ha⟩

/-- A present target slot restores exactly its selected native factor. -/
def centralTargetSlotIso {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : I) (t : Sector I) (Z : P.H t) (E : P.H t ⥤ C)
    (a : {a : Bool // StepValid (dn i) a t}) :
    (sectorFamilyObject (ι := ι) (fun a => StepValid (dn i) a t)
      (fun a => E.obj (P.centralTargetFactor i t Z a)) (E.obj Z)).X
        (sectorFamilyIndex (.inl a : Sum {a : Bool // StepValid (dn i) a t} ι)) ≅
    E.obj (P.centralTargetFactor i t Z a) := by
  rcases a with ⟨a, ha⟩
  cases a
  · exact P.centralTargetCornerIso i t Z E ⟨false, ha⟩
  · exact P.centralTargetCornerIso i t Z E ⟨true, ha⟩

/-- The source component chart at a valid pure path, in any window size. -/
def centralSourcePathIso {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : I) (ν : X) (t : Sector I) (Z : P.H t) (E : P.H t ⥤ C)
    (a : {a : Bool // StepValid (up i) a t}) :
    (sectorFamilyObject (ι := ι) (fun a => StepValid (up i) a t)
      (fun a => E.obj (P.centralSourceFactor i t Z a)) (E.obj Z)).X
        (sectorFamilyIndex (.inl a : Sum {a : Bool // StepValid (up i) a t} ι)) ≅
    E.obj ((P.pathFunctor (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t a)).obj Z) := by
  rcases a with ⟨a, ha⟩
  cases a
  · exact P.centralSourceCornerIso i t Z E ⟨false, ha⟩ ≪≫
      E.mapIso (P.centralSourceFactorIso i ν t Z ⟨false, ha⟩)
  · exact P.centralSourceCornerIso i t Z E ⟨true, ha⟩ ≪≫
      E.mapIso (P.centralSourceFactorIso i ν t Z ⟨true, ha⟩)

/-- The target component chart at a valid pure path, in any window size. -/
def centralTargetPathIso {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : I) (ν : X) (t : Sector I) (Z : P.H t) (E : P.H t ⥤ C)
    (a : {a : Bool // StepValid (dn i) a t}) :
    (sectorFamilyObject (ι := ι) (fun a => StepValid (dn i) a t)
      (fun a => E.obj (P.centralTargetFactor i t Z a)) (E.obj Z)).X
        (sectorFamilyIndex (.inl a : Sum {a : Bool // StepValid (dn i) a t} ι)) ≅
    E.obj ((P.pathFunctor (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t a)).obj Z) := by
  rcases a with ⟨a, ha⟩
  cases a
  · exact P.centralTargetCornerIso i t Z E ⟨false, ha⟩ ≪≫
      E.mapIso (P.centralTargetFactorIso i ν t Z ⟨false, ha⟩)
  · exact P.centralTargetCornerIso i t Z E ⟨true, ha⟩ ≪≫
      E.mapIso (P.centralTargetFactorIso i ν t Z ⟨true, ha⟩)

/-- The four prescribed native principal maps: reservoir mate, the two
mixed bends, and probe mate. Only valid pure corners are used. -/
def centralFactorSigma (c : P.CrossCoeff) (i : I) (t : Sector I) (Z : P.H t) :
    ∀ (a : {a : Bool // StepValid (up i) a t})
      (b : {b : Bool // StepValid (dn i) b t}),
      P.centralSourceFactor i t Z a ⟶ P.centralTargetFactor i t Z b
  | ⟨false, hc⟩, ⟨false, _⟩ =>
    (rouquierMate
      (homContentPostSuperAdjunction P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hc))
      (homContentPostSuperAdjunction P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t))
      (homContentPostCrossing P.T.obj P.W i t.1 (P.muP t)
        (P.muM_postE i hc) (P.muM_postF i t))).app (D.parity i) Z
  | ⟨false, hc⟩, ⟨true, hb⟩ => reservoirToProbeBend c i t hb hc Z
  | ⟨true, _⟩, ⟨false, _⟩ => probeToReservoirBend c i t Z
  | ⟨true, _⟩, ⟨true, hb⟩ =>
    (rouquierMate
      (homContentSuperAdjunction P.T P.W.obj i (P.muM t) (P.muP_preE i t))
      (homContentSuperAdjunction P.T P.W.obj i (P.muM t) (P.muP_preF i hb))
      (homContentCrossing P.T P.W.obj i (P.muM t)
        (P.muP_preE i t) (P.muP_preF i hb))).app (D.parity i) Z

/-- All four literal sigma entries use these same prescribed maps in
the selected native factor charts. -/
theorem sigmaEntry_centralFactor (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (a : {a : Bool // StepValid (up i) a t})
    (b : {b : Bool // StepValid (dn i) b t}) :
    P.sigmaEntry c i i ν (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t a)
      (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t b) Z =
    (P.centralSourceFactorIso i ν t Z a).inv ≫ P.centralFactorSigma c i t Z a b ≫
      (P.centralTargetFactorIso i ν t Z b).hom := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a <;> cases b
  · exact P.sigmaEntry_reservoir_mate c i ν t ha Z
  · exact P.sigmaEntry_reservoirToProbe c i ν t hb ha Z
  · exact P.sigmaEntry_probeToReservoir c i ν t Z
  · exact P.sigmaEntry_probe_mate c i ν t hb Z

/-- The selected native dotted cap in either valid pure source. -/
def centralFactorCap (i : I) (t : Sector I) (Z : P.H t) (n : ℕ) :
    ∀ a : {a : Bool // StepValid (up i) a t}, P.centralSourceFactor i t Z a ⟶ Z
  | ⟨false, hc⟩ => homContentPostCap P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hc) n Z
  | ⟨true, _⟩ => homReservoirCap P.T P.W.obj i (P.muM t) (P.muP_preE i t) n Z

/-- The selected native dotted unit in either valid pure target. -/
def centralFactorUnit (i : I) (t : Sector I) (Z : P.H t) (n : ℕ) :
    ∀ b : {b : Bool // StepValid (dn i) b t}, Z ⟶ P.centralTargetFactor i t Z b
  | ⟨false, _⟩ => homContentPostCup P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t) n Z
  | ⟨true, hb⟩ => homReservoirCup P.T P.W.obj i (P.muM t) (P.muP_preF i hb) n Z

/-- Every cap exponent uses the prescribed factor row. -/
theorem epsEntry_centralFactor (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (a : {a : Bool // StepValid (up i) a t}) (n : ℕ) :
    P.epsEntry c i n ν (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t a) (.nil t) Z =
    (P.centralSourceFactorIso i ν t Z a).inv ≫ P.centralFactorCap i t Z n a := by
  rcases a with ⟨a, ha⟩
  cases a
  · exact P.epsEntry_reservoir_factor c i n ν ha (by trivial) (SPath.next_upDn_false_false ha) Z
  · exact P.epsEntry_probe_factor c i n ν (by simp [StepValid, nextSector])
      (SPath.next_upDn_true_true t) Z

/-- Every unit exponent uses the prescribed factor column. -/
theorem etaEntry_centralFactor (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (b : {b : Bool // StepValid (dn i) b t}) (n : ℕ) :
    P.etaEntry c i n ν (.nil t) (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t b) Z =
    P.centralFactorUnit i t Z n b ≫ (P.centralTargetFactorIso i ν t Z b).hom := by
  rcases b with ⟨b, hb⟩
  cases b
  · exact P.etaEntry_reservoir_factor c i n ν (by trivial) (by simp [StepValid, nextSector])
      (SPath.next_dnUp_false_false t) Z
  · exact P.etaEntry_probe_factor c i n ν hb (by trivial) (SPath.next_dnUp_true_true hb) Z

/-- A valid pure entry of the positive matrix is the prescribed sigma
entry in the selected cap/cup factor charts. -/
theorem augPosSectorMatrix_pure_entry (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E]
    (a : {a : Bool // StepValid (up i) a t})
    (b : {b : Bool // StepValid (dn i) b t}) :
    (P.augPosSectorMatrix c i ν t Z E)
      (sectorFamilyIndex (.inl a : Sum {a : Bool // StepValid (up i) a t} Empty))
      (sectorFamilyIndex (.inl b : Sum {b : Bool // StepValid (dn i) b t} (Fin (D.h i ν).toNat))) =
    (P.centralSourcePathIso (ι := Empty) i ν t Z E a).hom ≫
      E.map (P.sigmaEntry c i i ν
        (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t a)
        (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t b) Z) ≫
      (P.centralTargetPathIso (ι := Fin (D.h i ν).toNat) i ν t Z E b).inv := by
  let X' : SPath (wd D ν [up i, dn i]) t t → C :=
    fun p => E.obj ((P.pathFunctor p).obj Z)
  let Y' : Sum (SPath (wd D ν [dn i, up i]) t t)
      (Fin (D.h i ν).toNat × SPath (wd D ν []) t t) → C :=
    fun y => E.obj (Sum.elim (fun p => (P.pathFunctor p).obj Z)
      (fun nr => (P.pathFunctor nr.2).obj Z) y)
  let f : ∀ a b, X' a ⟶ Y' b := fun p y =>
    E.map (match y with
      | .inl q => P.sigmaEntry c i i ν p q Z
      | .inr nr => P.epsEntry c i nr.1 ν p nr.2 Z)
  have h := sectorFamilyMap_entry _ (centralSourceIndex (D := D) i ν t) X'
    (fun a => E.obj (P.centralSourceFactor i t Z a)) (E.obj Z)
    (fun a => E.mapIso (P.centralSourceFactorIso i ν t Z a)) (fun n => Empty.elim n)
    _ (centralAugTargetIndex (D := D) i ν t _) Y'
    (fun b => E.obj (P.centralTargetFactor i t Z b)) (E.obj Z)
    (fun b => E.mapIso (P.centralTargetFactorIso i ν t Z b)) (fun _ => Iso.refl _)
    f (.inl a) (.inl b)
  have hf : famHom f = E.mapMat_.map (P.augPosMat c i ν t t Z) := by
    apply Mat_.hom_ext
    intro x y
    dsimp only [famHom, Functor.mapMat_, augPosMat, f]
    cases (Fintype.equivFin (Sum (SPath (wd D ν [dn i, up i]) t t)
      (Fin (D.h i ν).toNat × SPath (wd D ν []) t t))).symm y <;> rfl
  rw [hf] at h
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a <;> cases b <;>
    simpa only [augPosSectorMatrix, augPosSourceIso, augPosTargetIso,
      centralSourcePathIso, centralTargetPathIso, centralSourceCornerIso, centralTargetCornerIso,
      centralSourceIndex_symm_inl, centralAugTargetIndex_symm_inl, sectorFamilyChartAt, X', Y', f,
      id_eq] using h

/-- Every valid pure entry of the negative matrix retains the prescribed
minus of the sigma entry, with no sign normalization of either factor. -/
theorem augNegSectorMatrix_pure_entry (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E]
    (a : {a : Bool // StepValid (up i) a t})
    (b : {b : Bool // StepValid (dn i) b t}) :
    (P.augNegSectorMatrix c i ν t Z E)
      (sectorFamilyIndex (.inl a : Sum {a : Bool // StepValid (up i) a t} (Fin (-D.h i ν).toNat)))
      (sectorFamilyIndex (.inl b : Sum {b : Bool // StepValid (dn i) b t} Empty)) =
    -((P.centralSourcePathIso (ι := Fin (-D.h i ν).toNat) i ν t Z E a).hom ≫
      E.map (P.sigmaEntry c i i ν
        (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t a)
        (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t b) Z) ≫
      (P.centralTargetPathIso (ι := Empty) i ν t Z E b).inv) := by
  let X' : Sum (SPath (wd D ν [up i, dn i]) t t)
      (Fin (-D.h i ν).toNat × SPath (wd D ν []) t t) → C :=
    fun x => E.obj (Sum.elim (fun p => (P.pathFunctor p).obj Z)
      (fun nr => (P.pathFunctor nr.2).obj Z) x)
  let Y' : SPath (wd D ν [dn i, up i]) t t → C :=
    fun q => E.obj ((P.pathFunctor q).obj Z)
  let f : ∀ a b, X' a ⟶ Y' b := fun x q =>
    E.map (match x with
      | .inl p => -P.sigmaEntry c i i ν p q Z
      | .inr nr => P.etaEntry c i nr.1 ν nr.2 q Z)
  have h := sectorFamilyMap_entry _ (centralAugSourceIndex (D := D) i ν t _) X'
    (fun a => E.obj (P.centralSourceFactor i t Z a)) (E.obj Z)
    (fun a => E.mapIso (P.centralSourceFactorIso i ν t Z a)) (fun _ => Iso.refl _)
    _ (centralTargetIndex (D := D) i ν t) Y'
    (fun b => E.obj (P.centralTargetFactor i t Z b)) (E.obj Z)
    (fun b => E.mapIso (P.centralTargetFactorIso i ν t Z b)) (fun n => Empty.elim n)
    f (.inl a) (.inl b)
  have hf : famHom f = E.mapMat_.map (P.augNegMat c i ν t t Z) := by
    apply Mat_.hom_ext
    intro x y
    dsimp only [famHom, Functor.mapMat_, augNegMat, f]
    cases (Fintype.equivFin (Sum (SPath (wd D ν [up i, dn i]) t t)
      (Fin (-D.h i ν).toNat × SPath (wd D ν []) t t))).symm x <;> rfl
  rw [hf] at h
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a <;> cases b <;>
    simpa only [augNegSectorMatrix, augNegSourceIso, augNegTargetIso,
      centralSourcePathIso, centralTargetPathIso, centralSourceCornerIso, centralTargetCornerIso,
      centralAugSourceIndex_symm_inl, centralTargetIndex_symm_inl, sectorFamilyChartAt, X', Y', f,
      id_eq, Functor.map_neg, Preadditive.comp_neg, Preadditive.neg_comp] using h

/-- Every positive window entry is the prescribed dotted cap at its
actual exponent and canonical identity path. -/
theorem augPosSectorMatrix_cap_entry (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E]
    (a : {a : Bool // StepValid (up i) a t}) (n : Fin (D.h i ν).toNat) :
    (P.augPosSectorMatrix c i ν t Z E)
      (sectorFamilyIndex (.inl a : Sum {a : Bool // StepValid (up i) a t} Empty))
      (sectorFamilyIndex (.inr n : Sum {b : Bool // StepValid (dn i) b t} (Fin (D.h i ν).toNat))) =
    (P.centralSourcePathIso (ι := Empty) i ν t Z E a).hom ≫
      E.map (P.epsEntry c i n ν
        (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t a) (.nil t) Z) ≫ 𝟙 (E.obj Z) := by
  let X' : SPath (wd D ν [up i, dn i]) t t → C :=
    fun p => E.obj ((P.pathFunctor p).obj Z)
  let Y' : Sum (SPath (wd D ν [dn i, up i]) t t)
      (Fin (D.h i ν).toNat × SPath (wd D ν []) t t) → C :=
    fun y => E.obj (Sum.elim (fun p => (P.pathFunctor p).obj Z)
      (fun nr => (P.pathFunctor nr.2).obj Z) y)
  let f : ∀ a b, X' a ⟶ Y' b := fun p y =>
    E.map (match y with
      | .inl q => P.sigmaEntry c i i ν p q Z
      | .inr nr => P.epsEntry c i nr.1 ν p nr.2 Z)
  have h := sectorFamilyMap_entry _ (centralSourceIndex (D := D) i ν t) X'
    (fun a => E.obj (P.centralSourceFactor i t Z a)) (E.obj Z)
    (fun a => E.mapIso (P.centralSourceFactorIso i ν t Z a)) (fun n => Empty.elim n)
    _ (centralAugTargetIndex (D := D) i ν t _) Y'
    (fun b => E.obj (P.centralTargetFactor i t Z b)) (E.obj Z)
    (fun b => E.mapIso (P.centralTargetFactorIso i ν t Z b)) (fun _ => Iso.refl _)
    f (.inl a) (.inr n)
  have hf : famHom f = E.mapMat_.map (P.augPosMat c i ν t t Z) := by
    apply Mat_.hom_ext
    intro x y
    dsimp only [famHom, Functor.mapMat_, augPosMat, f]
    cases (Fintype.equivFin (Sum (SPath (wd D ν [dn i, up i]) t t)
      (Fin (D.h i ν).toNat × SPath (wd D ν []) t t))).symm y <;> rfl
  rw [hf] at h
  rcases a with ⟨a, ha⟩
  cases a <;>
    simpa only [augPosSectorMatrix, augPosSourceIso, augPosTargetIso,
      centralSourcePathIso, centralSourceCornerIso,
      centralSourceIndex_symm_inl, centralAugTargetIndex_symm_inr, sectorFamilyChartAt, X', Y', f,
      id_eq, Iso.refl_inv, pathFunctor_nil, Functor.id_obj] using h

/-- Every negative window entry is the prescribed dotted unit at its
actual exponent and canonical identity path. -/
theorem augNegSectorMatrix_unit_entry (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E]
    (n : Fin (-D.h i ν).toNat) (b : {b : Bool // StepValid (dn i) b t}) :
    (P.augNegSectorMatrix c i ν t Z E)
      (sectorFamilyIndex (.inr n : Sum {a : Bool // StepValid (up i) a t} (Fin (-D.h i ν).toNat)))
      (sectorFamilyIndex (.inl b : Sum {b : Bool // StepValid (dn i) b t} Empty)) =
      𝟙 (E.obj Z) ≫ E.map (P.etaEntry c i n ν (.nil t)
        (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t b) Z) ≫
      (P.centralTargetPathIso (ι := Empty) i ν t Z E b).inv := by
  let X' : Sum (SPath (wd D ν [up i, dn i]) t t)
      (Fin (-D.h i ν).toNat × SPath (wd D ν []) t t) → C :=
    fun x => E.obj (Sum.elim (fun p => (P.pathFunctor p).obj Z)
      (fun nr => (P.pathFunctor nr.2).obj Z) x)
  let Y' : SPath (wd D ν [dn i, up i]) t t → C :=
    fun q => E.obj ((P.pathFunctor q).obj Z)
  let f : ∀ a b, X' a ⟶ Y' b := fun x q =>
    E.map (match x with
      | .inl p => -P.sigmaEntry c i i ν p q Z
      | .inr nr => P.etaEntry c i nr.1 ν nr.2 q Z)
  have h := sectorFamilyMap_entry _ (centralAugSourceIndex (D := D) i ν t _) X'
    (fun a => E.obj (P.centralSourceFactor i t Z a)) (E.obj Z)
    (fun a => E.mapIso (P.centralSourceFactorIso i ν t Z a)) (fun _ => Iso.refl _)
    _ (centralTargetIndex (D := D) i ν t) Y'
    (fun b => E.obj (P.centralTargetFactor i t Z b)) (E.obj Z)
    (fun b => E.mapIso (P.centralTargetFactorIso i ν t Z b)) (fun n => Empty.elim n)
    f (.inr n) (.inl b)
  have hf : famHom f = E.mapMat_.map (P.augNegMat c i ν t t Z) := by
    apply Mat_.hom_ext
    intro x y
    dsimp only [famHom, Functor.mapMat_, augNegMat, f]
    cases (Fintype.equivFin (Sum (SPath (wd D ν [up i, dn i]) t t)
      (Fin (-D.h i ν).toNat × SPath (wd D ν []) t t))).symm x <;> rfl
  rw [hf] at h
  rcases b with ⟨b, hb⟩
  cases b <;>
    simpa only [augNegSectorMatrix, augNegSourceIso, augNegTargetIso,
      centralTargetPathIso, centralTargetCornerIso,
      centralAugSourceIndex_symm_inr, centralTargetIndex_symm_inl, sectorFamilyChartAt, X', Y', f,
      id_eq, Iso.refl_hom, pathFunctor_nil, Functor.id_obj] using h
/-- Every positive principal block is the prescribed native factor map
in the conditional pure-slot charts. -/
theorem augPosSectorMatrix_pure_factor (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E]
    (a : {a : Bool // StepValid (up i) a t})
    (b : {b : Bool // StepValid (dn i) b t}) :
    (P.augPosSectorMatrix c i ν t Z E)
      (sectorFamilyIndex (.inl a : Sum {a : Bool // StepValid (up i) a t} Empty))
      (sectorFamilyIndex (.inl b : Sum {b : Bool // StepValid (dn i) b t} (Fin (D.h i ν).toNat))) =
    (P.centralSourceSlotIso (ι := Empty) i t Z E a).hom ≫
      E.map (P.centralFactorSigma c i t Z a b) ≫
      (P.centralTargetSlotIso (ι := Fin (D.h i ν).toNat) i t Z E b).inv := by
  rw [augPosSectorMatrix_pure_entry, sigmaEntry_centralFactor]
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a <;> cases b <;>
    exact mappedIsoEntry E _ _ _ _ _

/-- Every negative principal block is minus the same native factor map;
the selected mates and both mixed bends keep their original signs. -/
theorem augNegSectorMatrix_pure_factor (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E]
    (a : {a : Bool // StepValid (up i) a t})
    (b : {b : Bool // StepValid (dn i) b t}) :
    (P.augNegSectorMatrix c i ν t Z E)
      (sectorFamilyIndex (.inl a : Sum {a : Bool // StepValid (up i) a t} (Fin (-D.h i ν).toNat)))
      (sectorFamilyIndex (.inl b : Sum {b : Bool // StepValid (dn i) b t} Empty)) =
    -((P.centralSourceSlotIso (ι := Fin (-D.h i ν).toNat) i t Z E a).hom ≫
      E.map (P.centralFactorSigma c i t Z a b) ≫
      (P.centralTargetSlotIso (ι := Empty) i t Z E b).inv) := by
  rw [augNegSectorMatrix_pure_entry, sigmaEntry_centralFactor]
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a <;> cases b <;>
    exact congrArg Neg.neg (mappedIsoEntry E _ _ _ _ _)

/-- Every positive window entry is the selected native dotted cap. -/
theorem augPosSectorMatrix_cap_factor (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E]
    (a : {a : Bool // StepValid (up i) a t}) (n : Fin (D.h i ν).toNat) :
    (P.augPosSectorMatrix c i ν t Z E)
      (sectorFamilyIndex (.inl a : Sum {a : Bool // StepValid (up i) a t} Empty))
      (sectorFamilyIndex (.inr n : Sum {b : Bool // StepValid (dn i) b t} (Fin (D.h i ν).toNat))) =
    (P.centralSourceSlotIso (ι := Empty) i t Z E a).hom ≫
      E.map (P.centralFactorCap i t Z n a) := by
  rw [augPosSectorMatrix_cap_entry, epsEntry_centralFactor]
  rcases a with ⟨a, ha⟩
  cases a <;> exact mappedIsoCap E _ _ _

/-- Every negative window entry is the selected native dotted unit. -/
theorem augNegSectorMatrix_unit_factor (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E]
    (n : Fin (-D.h i ν).toNat) (b : {b : Bool // StepValid (dn i) b t}) :
    (P.augNegSectorMatrix c i ν t Z E)
      (sectorFamilyIndex (.inr n : Sum {a : Bool // StepValid (up i) a t} (Fin (-D.h i ν).toNat)))
      (sectorFamilyIndex (.inl b : Sum {b : Bool // StepValid (dn i) b t} Empty)) =
      E.map (P.centralFactorUnit i t Z n b) ≫
      (P.centralTargetSlotIso (ι := Empty) i t Z E b).inv := by
  rw [augNegSectorMatrix_unit_entry, etaEntry_centralFactor]
  rcases b with ⟨b, hb⟩
  cases b <;> exact mappedIsoUnit E _ _ _

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

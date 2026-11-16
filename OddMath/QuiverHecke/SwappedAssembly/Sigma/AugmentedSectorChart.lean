import OddMath.QuiverHecke.SwappedAssembly.Sigma.CentralPaths
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SectorFamilyChart
import OddMath.QuiverHecke.SwappedAssembly.Sigma.ProbeFactorCoordinates

/-! # Factor object charts for the central augmented matrices

The central path families of Brundan–Ellis (1.13)–(1.14) are charted
in the two pure factor objects and the identity window. Every valid path
is included. An absent reservoir source or probe target is represented
by a zero object after additive evaluation. No height bound or
invertibility premise is used.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM Classical
open scoped ZeroObject
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)
local instance pathFintype (w : List (Col I X)) (s t : Sector I) : Fintype (SPath w s t) :=
  Fintype.ofFinite _

/-- Native reservoir/probe objects in the source pure corners. -/
def centralSourceFactor (i : I) (t : Sector I) (Z : P.H t) :
    {a : Bool // StepValid (up i) a t} → P.H t
  | ⟨false, hc⟩ =>
    (homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hc)).obj
      ((homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hc)).obj Z)
  | ⟨true, _⟩ =>
    (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj
      ((homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj Z)

/-- Native reservoir/probe objects in the target pure corners. -/
def centralTargetFactor (i : I) (t : Sector I) (Z : P.H t) :
    {a : Bool // StepValid (dn i) a t} → P.H t
  | ⟨false, _⟩ =>
    (homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).obj
      ((homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).obj Z)
  | ⟨true, hb⟩ =>
    (homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).obj
      ((homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).obj Z)

/-- The selected cap factor chart, in the model-to-path orientation. -/
def centralSourceFactorIso (i : I) (ν : X) (t : Sector I) (Z : P.H t)
    (a : {a : Bool // StepValid (up i) a t}) :
    P.centralSourceFactor i t Z a ≅
      (P.pathFunctor (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t a)).obj Z := by
  rcases a with ⟨a, ha⟩
  cases a
  · exact (reservoirCapFactorIso i ν ha (by trivial) (SPath.next_upDn_false_false ha) Z).symm
  · exact (probeCapFactorIso i ν (by simp [StepValid, nextSector])
      (SPath.next_upDn_true_true t) Z).symm

/-- The selected cup factor chart, in the model-to-path orientation. -/
def centralTargetFactorIso (i : I) (ν : X) (t : Sector I) (Z : P.H t)
    (a : {a : Bool // StepValid (dn i) a t}) :
    P.centralTargetFactor i t Z a ≅
      (P.pathFunctor (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t a)).obj Z := by
  rcases a with ⟨a, ha⟩
  cases a
  · exact (reservoirCupFactorIso i ν (by trivial) (by simp [StepValid, nextSector])
      (SPath.next_dnUp_false_false t) Z).symm
  · exact (probeCupFactorIso i ν ha (by trivial) (SPath.next_dnUp_true_true ha) Z).symm

/-- The source pure paths, with no extra window. -/
def centralSourceIndex (i : I) (ν : X) (t : Sector I) :
    SPath (wd D ν [up i, dn i]) t t ≃ Sum {a : Bool // StepValid (up i) a t} Empty :=
  (SPath.centralUpDnEquiv i (SKM.wt D ν [dn i]) ν t).trans (Equiv.sumEmpty _ _).symm

/-- The target pure paths, with no extra window. -/
def centralTargetIndex (i : I) (ν : X) (t : Sector I) :
    SPath (wd D ν [dn i, up i]) t t ≃ Sum {a : Bool // StepValid (dn i) a t} Empty :=
  (SPath.centralDnUpEquiv i (SKM.wt D ν [up i]) ν t).trans (Equiv.sumEmpty _ _).symm

/-- The augmented source indices, including the whole identity window. -/
def centralAugSourceIndex (i : I) (ν : X) (t : Sector I) (n : ℕ) :
    Sum (SPath (wd D ν [up i, dn i]) t t)
      (Fin n × SPath (wd D ν []) t t) ≃
      Sum {a : Bool // StepValid (up i) a t} (Fin n) :=
  Equiv.sumCongr (SPath.centralUpDnEquiv i (SKM.wt D ν [dn i]) ν t)
    (((Equiv.refl (Fin n)).prodCongr (SPath.centralNilEquiv t)).trans (Equiv.prodUnique _ Unit))

/-- The augmented target indices, including the whole identity window. -/
def centralAugTargetIndex (i : I) (ν : X) (t : Sector I) (n : ℕ) :
    Sum (SPath (wd D ν [dn i, up i]) t t)
      (Fin n × SPath (wd D ν []) t t) ≃
      Sum {a : Bool // StepValid (dn i) a t} (Fin n) :=
  Equiv.sumCongr (SPath.centralDnUpEquiv i (SKM.wt D ν [up i]) ν t)
    (((Equiv.refl (Fin n)).prodCongr (SPath.centralNilEquiv t)).trans (Equiv.prodUnique _ Unit))

variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]

/-- Source chart for the positive matrix, with a zero reservoir corner
when the source reservoir content vanishes. -/
def augPosSourceIso (i : I) (ν : X) (t : Sector I) (Z : P.H t)
    (E : P.H t ⥤ C) [Functor.Additive E] :
    sectorFamilyObject (ι := Empty) (fun a => StepValid (up i) a t)
      (fun a => E.obj (P.centralSourceFactor i t Z a)) (E.obj Z) ≅
      E.mapMat_.obj (famObj (fun p : SPath (wd D ν [up i, dn i]) t t =>
        (P.pathFunctor p).obj Z)) :=
by
  change _ ≅ famObj (fun p : SPath (wd D ν [up i, dn i]) t t =>
    E.obj ((P.pathFunctor p).obj Z))
  exact sectorFamilyIso _ (centralSourceIndex (D := D) i ν t)
    (fun p => E.obj ((P.pathFunctor p).obj Z)) _ _
    (fun a => E.mapIso (P.centralSourceFactorIso i ν t Z a)) (fun n => Empty.elim n)

/-- Target chart for the positive matrix. All height-window indices are
included, also when the probe target corner is absent. -/
def augPosTargetIso (i : I) (ν : X) (t : Sector I) (Z : P.H t)
    (E : P.H t ⥤ C) [Functor.Additive E] :
    sectorFamilyObject (ι := Fin (D.h i ν).toNat) (fun a => StepValid (dn i) a t)
      (fun a => E.obj (P.centralTargetFactor i t Z a)) (E.obj Z) ≅
      E.mapMat_.obj (famObj (Sum.elim
        (fun p : SPath (wd D ν [dn i, up i]) t t => (P.pathFunctor p).obj Z)
        (fun nr : Fin (D.h i ν).toNat × SPath (wd D ν []) t t =>
          (P.pathFunctor nr.2).obj Z))) :=
by
  let X' : Sum (SPath (wd D ν [dn i, up i]) t t)
      (Fin (D.h i ν).toNat × SPath (wd D ν []) t t) → C :=
    fun y => E.obj (Sum.elim (fun p => (P.pathFunctor p).obj Z)
      (fun nr => (P.pathFunctor nr.2).obj Z) y)
  change _ ≅ famObj X'
  exact sectorFamilyIso _ (centralAugTargetIndex (D := D) i ν t _) X' _ _
    (fun a => E.mapIso (P.centralTargetFactorIso i ν t Z a)) (fun _ => Iso.refl _)

/-- Source chart for the negative matrix, retaining its entire cup window. -/
def augNegSourceIso (i : I) (ν : X) (t : Sector I) (Z : P.H t)
    (E : P.H t ⥤ C) [Functor.Additive E] :
    sectorFamilyObject (ι := Fin (-D.h i ν).toNat) (fun a => StepValid (up i) a t)
      (fun a => E.obj (P.centralSourceFactor i t Z a)) (E.obj Z) ≅
      E.mapMat_.obj (famObj (Sum.elim
        (fun p : SPath (wd D ν [up i, dn i]) t t => (P.pathFunctor p).obj Z)
        (fun nr : Fin (-D.h i ν).toNat × SPath (wd D ν []) t t =>
          (P.pathFunctor nr.2).obj Z))) :=
by
  let X' : Sum (SPath (wd D ν [up i, dn i]) t t)
      (Fin (-D.h i ν).toNat × SPath (wd D ν []) t t) → C :=
    fun y => E.obj (Sum.elim (fun p => (P.pathFunctor p).obj Z)
      (fun nr => (P.pathFunctor nr.2).obj Z) y)
  change _ ≅ famObj X'
  exact sectorFamilyIso _ (centralAugSourceIndex (D := D) i ν t _) X' _ _
    (fun a => E.mapIso (P.centralSourceFactorIso i ν t Z a)) (fun _ => Iso.refl _)

/-- Target chart for the negative matrix, retaining a zero probe corner
when the target probe content vanishes. -/
def augNegTargetIso (i : I) (ν : X) (t : Sector I) (Z : P.H t)
    (E : P.H t ⥤ C) [Functor.Additive E] :
    sectorFamilyObject (ι := Empty) (fun a => StepValid (dn i) a t)
      (fun a => E.obj (P.centralTargetFactor i t Z a)) (E.obj Z) ≅
      E.mapMat_.obj (famObj (fun p : SPath (wd D ν [dn i, up i]) t t =>
        (P.pathFunctor p).obj Z)) :=
by
  change _ ≅ famObj (fun p : SPath (wd D ν [dn i, up i]) t t =>
    E.obj ((P.pathFunctor p).obj Z))
  exact sectorFamilyIso _ (centralTargetIndex (D := D) i ν t)
    (fun p => E.obj ((P.pathFunctor p).obj Z)) _ _
    (fun a => E.mapIso (P.centralTargetFactorIso i ν t Z a)) (fun n => Empty.elim n)

/-- The positive augmented matrix in the two pure factor charts. -/
def augPosSectorMatrix (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E] :=
  matrixEmbeddingMap (P.augPosSourceIso i ν t Z E) (P.augPosTargetIso i ν t Z E)
    (E.mapMat_.map (P.augPosMat c i ν t t Z))

/-- The negative augmented matrix in the same factor charts. Its
principal entries retain the minus sign in (1.14). -/
def augNegSectorMatrix (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E] :=
  matrixEmbeddingMap (P.augNegSourceIso i ν t Z E) (P.augNegTargetIso i ν t Z E)
    (E.mapMat_.map (P.augNegMat c i ν t t Z))

/-- The positive literal coordinate square holds for every outer sector
and full Hom input, including absent pure corners and height zero. -/
theorem augPosSectorMatrix_square (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E] :
    (P.augPosSourceIso i ν t Z E).hom ≫ E.mapMat_.map (P.augPosMat c i ν t t Z) =
      P.augPosSectorMatrix c i ν t Z E ≫ (P.augPosTargetIso i ν t Z E).hom :=
  matrixEmbeddingMap_square _ _ _

/-- The negative literal coordinate square retains the prescribed
negative principal matrix and the full unit window. -/
theorem augNegSectorMatrix_square (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E] :
    (P.augNegSourceIso i ν t Z E).hom ≫ E.mapMat_.map (P.augNegMat c i ν t t Z) =
      P.augNegSectorMatrix c i ν t Z E ≫ (P.augNegTargetIso i ν t Z E).hom :=
  matrixEmbeddingMap_square _ _ _

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

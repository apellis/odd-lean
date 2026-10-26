import OddMath.SKM.RouquierHomContent

/-!
# Coherent movement of the content parity shift

This supplies the parity-shift comparisons required by the Hom construction
ported from `Categorification/TwoRep/RouqProduct.lean` and `RouqProductLeft.lean`.
Its downstream consumer is the pair of content-shifted postcomposition
adjoints in the reservoir–probe family. The Π comparisons are those of the
ambient Π-supercategory, including the negative self-interchange of Π.
These comparisons do not prove the original-datum multicolour KLR relations.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section Parity
variable {k : Type r} [CommRing k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [Supercategory k C] [PiSupercategory k C]

@[simp] theorem homParityShift_zero : homParityShift (k := k) (C := C) 0 = 𝟭 C := by
  simp [homParityShift]

@[simp] theorem homParityShift_one :
    homParityShift (k := k) (C := C) 1 = PiSupercategory.pi (R := k) := by
  simp [homParityShift]

/-- Addition of parity shifts uses the even square comparison for Π. -/
def homParityShiftAdd (p q : ZMod 2) :
    homParityShift (k := k) (C := C) p ⋙ homParityShift (k := k) q ≅
      homParityShift (k := k) (C := C) (p + q) := by
  by_cases hp : p = 0
  · subst p
    simpa only [zero_add, homParityShift_zero] using Functor.leftUnitor (homParityShift (k := k) (C := C) q)
  by_cases hq : q = 0
  · subst q
    simpa only [add_zero, homParityShift_zero] using Functor.rightUnitor (homParityShift (k := k) (C := C) p)
  have hp1 : p = 1 := by fin_cases p <;> simp_all
  have hq1 : q = 1 := by fin_cases q <;> simp_all
  subst p
  subst q
  exact PiSupercategory.ξIso

variable {D : Type*} [Category D] [Preadditive D] [Linear k D]
  [Supercategory k D] [PiSupercategory k D]

/-- Move the parity shift through a full superfunctor via the even β comparison. -/
def homParityShiftCommute (F : C ⥤ D) [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    (p : ZMod 2) :
    F ⋙ homParityShift (k := k) p ≅ homParityShift (k := k) p ⋙ F := by
  by_cases hp : p = 0
  · subst p
    exact (Functor.rightUnitor F) ≪≫ (Functor.leftUnitor F).symm
  · simpa only [homParityShift, ite_eq_right hp] using PiSupercategory.βIso (R := k) F

/-- Moving Π past a homogeneous transformation retains its full supernaturality,
including when the transformation is odd. -/
theorem homParityShiftCommute_supernatural
    (F G : C ⥤ D) [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    (p r : ZMod 2) (η : ∀ X, F.obj X ⟶ G.obj X) (hη : IsSupernatural k r η) (X : C) :
    (homParityShift (k := k) p).map (η X) ≫ (homParityShiftCommute G p).hom.app X =
      (homParityShiftCommute F p).hom.app X ≫ η ((homParityShift (k := k) p).obj X) := by
  by_cases hp : p = 0
  · subst p
    simp [homParityShiftCommute, homParityShift]
  have hp1 : p = 1 := by fin_cases p <;> simp_all
  subst p
  simp only [homParityShiftCommute, one_ne_zero, dite_false]
  change (PiSupercategory.pi (R := k)).map (η X) ≫ (PiSupercategory.β k G X).hom =
    (PiSupercategory.β k F X).hom ≫ η ((PiSupercategory.pi (R := k)).obj X)
  exact PiSupercategory.β_naturality_supernatural F G hη X

/-- Π exchanging with itself is negative, not the unsigned identity. -/
theorem homParityShiftCommute_pi (X : C) :
    (homParityShiftCommute (k := k) (PiSupercategory.pi (R := k) (C := C)) 1).hom.app X =
      -𝟙 ((PiSupercategory.pi (R := k)).obj ((PiSupercategory.pi (R := k)).obj X)) := by
  simp only [homParityShiftCommute, one_ne_zero, dite_false]
  change (PiSupercategory.β k (PiSupercategory.pi (R := k)) X).hom = _
  exact PiSupercategory.β_pi (R := k) X
end Parity

section Sectors
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}

/-- The lowering postcomposition functor with Π on its output side. -/
def homContentPostFOut (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM) :
    homWeightSector T W.obj muP nuM ⥤ homWeightSector T W.obj muP muM :=
  homPost (k := k) (W.F i h) ⋙ homParityShift (k := k) (homContentShift D i betaP)

instance (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM) :
    (homContentPostFOut T W i betaP muP h).Additive := by
  unfold homContentPostFOut
  infer_instance

instance (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM) :
    (homContentPostFOut T W i betaP muP h).Linear k := by
  unfold homContentPostFOut
  infer_instance

instance (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM) :
    IsSuperfunctor k (homContentPostFOut T W i betaP muP h) := by
  unfold homContentPostFOut
  infer_instance

/-- Move the previously constructed right adjoint's Π coherently to its output. -/
def homContentPostFOutIso (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM) :
    homContentPostF T W i betaP muP h ≅ homContentPostFOut T W i betaP muP h :=
  (homParityShiftCommute (homPost (k := k) (W.F i h)) (homContentShift D i betaP)).symm

/-- Both postcomposition adjoints can use the same output-shift convention. -/
def homContentPostOutAdjunction (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM) :
    homContentPostE T W i betaP muP h ⊣ homContentPostFOut T W i betaP muP h :=
  (homContentPostAdjunction T W i betaP muP h).ofNatIsoRight
    (homContentPostFOutIso T W i betaP muP h)
end Sectors
end OddMath.SKM

import OddMath.QuiverHecke.SwappedAssembly.ReservoirVacuumCrossing
import OddMath.QuiverHecke.SwappedAssembly.ReservoirLayerGenerators
import OddMath.QuiverHecke.SwappedAssembly.SlideAssembly

/-! # Distinct-colour factor crossings in reservoir matrices

SwappedVacuumCoordinates §§2–6: retain the terminal cast of the actual
source path when identifying the prescribed crossing image with its
reservoir factor crossing.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

private theorem transport_square {C : Type*} [Category* C] {A A' B B' : C}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    f ≫ eqToHom hB = eqToHom hA ≫ g := by
  subst A' B'
  cases h
  simp

private theorem chart_square {C : Type*} [Category* C] {A A' B B' S T : C}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (e : A' ≅ S) (d : B' ≅ T) (a : S ⟶ T)
    (h : HEq f g) (hg : g ≫ d.hom = e.hom ≫ a) :
    f ≫ (eqToIso hB ≪≫ d).hom = (eqToIso hA ≪≫ e).hom ≫ a := by
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [← Category.assoc, transport_square hA hB f g h, Category.assoc, hg]

namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

private def sourceValue (i j : I) (c : I →₀ ℕ)
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c)))
    (Z : P.H (nextSector (true,i) false (nextSector (true,j) false (0,c)))) :
    P.H (nextSector (true,j) false (nextSector (true,i) false (0,c))) := hs ▸ Z

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
private theorem edge (i j : I) (c : I →₀ ℕ)
    (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c))) :
    P.muM (nextSector (true,j) false (nextSector (true,i) false (0,c))) + D.α i =
      P.muM (nextSector (true,j) false (0,c)) := by rw [hs]; exact P.muM_postE i hw₂

/-- The source chart includes the actual two-letter path's terminal cast. -/
def reservoirCrossSourceIso (ν : X) (i j : I) (c : I →₀ ℕ)
    (hv₁ : StepValid (true,i) false (0,c))
    (hv₂ : StepValid (true,j) false (nextSector (true,i) false (0,c)))
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c)))
    (Z : P.H (nextSector (true,i) false (nextSector (true,j) false (0,c)))) :
    (P.pathFunctor (SPath.two (c₁ := ⟨up i, SKM.wt D ν [up j]⟩) (c₂ := ⟨up j,ν⟩)
      false false hv₁ hv₂ hs)).obj Z ≅
      sourceValue P i j c hs Z ≫ P.W.E j (P.muM_postE j hv₂) ≫ P.W.E i (P.muM_postE i hv₁) :=
  eqToIso (P.pathFunctor_two_obj (c₁ := ⟨up i, SKM.wt D ν [up j]⟩) (c₂ := ⟨up j,ν⟩) false false hv₁ hv₂ hs Z
    (sourceValue P i j c hs Z) (P.sector_heq hs Z)) ≪≫
    reservoirVacuumPairIso P.T.obj P.W i j (P.muP (0,c))
      (P.muM_postE j hv₂) (P.muM_postE i hv₁) (sourceValue P i j c hs Z)

/-- The target chart keeps the target sector before reversing its
prescribed transport to the common factor source. -/
def reservoirCrossTargetIso (ν : X) (i j : I) (c : I →₀ ℕ)
    (hw₁ : StepValid (true,j) false (0,c))
    (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c)))
    (Z : P.H (nextSector (true,i) false (nextSector (true,j) false (0,c)))) :
    (P.pathFunctor (SPath.two (c₁ := ⟨up j, SKM.wt D ν [up i]⟩) (c₂ := ⟨up i,ν⟩)
      false false hw₁ hw₂ rfl)).obj Z ≅
      sourceValue P i j c hs Z ≫ P.W.E i (edge P i j c hw₂ hs) ≫ P.W.E j (P.muM_postE j hw₁) :=
  eqToIso (P.pathFunctor_two_obj (c₁ := ⟨up j, SKM.wt D ν [up i]⟩) (c₂ := ⟨up i,ν⟩) false false hw₁ hw₂ rfl Z Z HEq.rfl) ≪≫
    P.reservoirVacuumCrossTargetIso i j c hw₁ hw₂ hs Z

/-- The literal distinct branch of `crossImage`, including the source
path cast, is the given factor crossing in the two specified charts. -/
theorem crossImage_reservoirVacuum (a : P.CrossCoeff) (ν : X) (i j : I) (hij : i ≠ j) (c : I →₀ ℕ)
    (hv₁ : StepValid (true,i) false (0,c))
    (hv₂ : StepValid (true,j) false (nextSector (true,i) false (0,c)))
    (hw₁ : StepValid (true,j) false (0,c))
    (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c)))
    (Z : P.H (nextSector (true,i) false (nextSector (true,j) false (0,c)))) :
    P.crossImage a i j ν (SPath.two false false hv₁ hv₂ hs)
        (SPath.two false false hw₁ hw₂ rfl) Z ≫
        (P.reservoirCrossTargetIso ν i j c hw₁ hw₂ hs Z).hom =
      (P.reservoirCrossSourceIso ν i j c hv₁ hv₂ hs Z).hom ≫
        sourceValue P i j c hs Z ◁ P.W.cross i j (P.muM_postE j hv₂) (P.muM_postE i hv₁)
          (edge P i j c hw₂ hs) (P.muM_postE j hw₁) := by
  have hraw : HEq (P.crossImage a i j ν (SPath.two false false hv₁ hv₂ hs)
      (SPath.two false false hw₁ hw₂ rfl) Z) (P.postCrossNe i j (0,c) hv₁ hv₂ hw₁ hw₂ hs Z) := by
    rw [P.crossImage_ne a hij]
    exact P.twoTwo_two_heq ⟨up i, SKM.wt D ν [up j]⟩ ⟨up j,ν⟩
      ⟨up j, SKM.wt D ν [up i]⟩ ⟨up i,ν⟩ (P.crossNeEntry i j _ _ _ _)
      false false false false hv₁ hv₂ hw₁ hw₂ hs rfl rfl Z Z HEq.rfl
  exact chart_square _ _ _ _ _ _ _ hraw (P.postCrossNe_reservoirVacuum i j c hv₁ hv₂ hw₁ hw₂ hs Z)

/-- The source-path chart, including both actual append contexts. -/
def reservoirLayerCrossSourceIso (ν : X) (u v : List (Letter I)) (i j : I)
    {sl : Sector I} {c d : I →₀ ℕ}
    (hv₁ : StepValid (true,i) false (0,c))
    (hv₂ : StepValid (true,j) false (nextSector (true,i) false (0,c)))
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c)))
    (pu : SPath (SKM.lay D ν u (.cross i j) v).left sl (0,c))
    (pv : SPath (SKM.lay D ν u (.cross i j) v).right
      (nextSector (true,i) false (nextSector (true,j) false (0,c))) (0,d))
    (Z : P.H (0,d)) :
    (P.pathFunctor ((pu.append (SPath.two
      (c₁ := ⟨up i, SKM.wt D (SKM.wt D ν v) [up j]⟩) (c₂ := ⟨up j,SKM.wt D ν v⟩)
      false false hv₁ hv₂ hs)).append pv)).obj Z ≅
      (P.pathFunctor pu).obj (sourceValue P i j c hs ((P.pathFunctor pv).obj Z) ≫
        P.W.E j (P.muM_postE j hv₂) ≫ P.W.E i (P.muM_postE i hv₁)) :=
  eqToIso (P.pathFunctor_append_append_obj pu (SPath.two (c₁ := ⟨up i, SKM.wt D (SKM.wt D ν v) [up j]⟩) (c₂ := ⟨up j,SKM.wt D ν v⟩) false false hv₁ hv₂ hs) pv Z) ≪≫
    (P.pathFunctor pu).mapIso (P.reservoirCrossSourceIso (SKM.wt D ν v) i j c hv₁ hv₂ hs
      ((P.pathFunctor pv).obj Z))

/-- The target chart reverses the original target-sector transport and
retains both actual append contexts. -/
def reservoirLayerCrossTargetIso (ν : X) (u v : List (Letter I)) (i j : I)
    {sl : Sector I} {c d : I →₀ ℕ}
    (hw₁ : StepValid (true,j) false (0,c))
    (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c)))
    (pu : SPath (SKM.lay D ν u (.cross i j) v).left sl (0,c))
    (pv : SPath (SKM.lay D ν u (.cross i j) v).right
      (nextSector (true,i) false (nextSector (true,j) false (0,c))) (0,d))
    (Z : P.H (0,d)) :
    (P.pathFunctor ((pu.append (SPath.two
      (c₁ := ⟨up j, SKM.wt D (SKM.wt D ν v) [up i]⟩) (c₂ := ⟨up i,SKM.wt D ν v⟩)
      false false hw₁ hw₂ rfl)).append pv)).obj Z ≅
      (P.pathFunctor pu).obj (sourceValue P i j c hs ((P.pathFunctor pv).obj Z) ≫
        P.W.E i (edge P i j c hw₂ hs) ≫ P.W.E j (P.muM_postE j hw₁)) :=
  eqToIso (P.pathFunctor_append_append_obj pu (SPath.two (c₁ := ⟨up j, SKM.wt D (SKM.wt D ν v) [up i]⟩) (c₂ := ⟨up i,SKM.wt D ν v⟩) false false hw₁ hw₂ rfl) pv Z) ≪≫
    (P.pathFunctor pu).mapIso (P.reservoirCrossTargetIso (SKM.wt D ν v) i j c hw₁ hw₂ hs
      ((P.pathFunctor pv).obj Z))

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

import OddMath.QuiverHecke.SwappedAssembly.ReservoirWordFunctor
import OddMath.QuiverHecke.SwappedAssembly.ReservoirLayerGenerators
import OddMath.QuiverHecke.SwappedAssembly.ReservoirLayerCrossings

/-! # Word coordinates on both reservoir path contexts

SwappedVacuumCoordinates §§2–6: transport both actual outer path
contexts to their reversed reservoir induction words. The right chart is
even, so its interchange with any generator map introduces no extra sign.
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
omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
private theorem context_square {a b c d : B}
    (F : (a ⟶ c) ⥤ (a ⟶ d)) (K : c ⟶ d) (e : F ≅ homPost (k := k) K)
    {Z Z' : a ⟶ b} (r : Z ≅ Z') (hr : r.hom ∈ parity (R := k) _ _ 0)
    {A B₁ : b ⟶ c} (g : A ⟶ B₁) :
    F.map (Z ◁ g) ≫ (F.map (r.hom ▷ B₁) ≫ e.hom.app (Z' ≫ B₁)) =
      (F.map (r.hom ▷ A) ≫ e.hom.app (Z' ≫ A)) ≫ (Z' ◁ g) ▷ K := by
  have hright := (TwoSupercategory.whisker_exchange_of_even_left hr g).symm
  have hleft := e.hom.naturality (Z' ◁ g)
  change F.map (Z' ◁ g) ≫ e.hom.app (Z' ≫ B₁) =
    e.hom.app (Z' ≫ A) ≫ (Z' ◁ g) ▷ K at hleft
  rw [← Category.assoc, ← F.map_comp, hright, F.map_comp, Category.assoc, hleft]
  simp only [Category.assoc]

namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

/-- Both reservoir context functors become their prescribed words.
The intervening factor 1-morphism is left unchanged. -/
def reservoirContextIso {l r : List (Col I X)} {cL cM cR d : I →₀ ℕ}
    (pu : SPath l (0,cL) (0,cM)) (hu : ∀ a ∈ l, a.l.1 = true)
    (pv : SPath r (0,cR) (0,d)) (hv : ∀ a ∈ r, a.l.1 = true)
    (Y : P.H (0,d)) (A : P.W.obj (P.muM (0,cR)) ⟶ P.W.obj (P.muM (0,cM))) :
    (P.pathFunctor pu).obj ((P.pathFunctor pv).obj Y ≫ A) ≅
      ((Y ≫ ReservoirWord.word P.W.toRouquierData P.ΛR pv hv) ≫ A) ≫
        ReservoirWord.word P.W.toRouquierData P.ΛR pu hu :=
  (P.pathFunctor pu).mapIso (TwoSupercategory.whiskerRightIso (R := k)
    ((P.reservoirWordFunctorIso pv hv).app Y) A) ≪≫
    (P.reservoirWordFunctorIso pu hu).app ((Y ≫
      ReservoirWord.word P.W.toRouquierData P.ΛR pv hv) ≫ A)

/-- The prescribed factor map in both actual path contexts becomes its
literal two-whiskered word map. The map may have arbitrary parity
components; evenness of the right chart is the only interchange input. -/
theorem reservoirContext_square {l r : List (Col I X)} {cL cM cR d : I →₀ ℕ}
    (pu : SPath l (0,cL) (0,cM)) (hu : ∀ a ∈ l, a.l.1 = true)
    (pv : SPath r (0,cR) (0,d)) (hv : ∀ a ∈ r, a.l.1 = true)
    (Y : P.H (0,d)) {A B₁ : P.W.obj (P.muM (0,cR)) ⟶ P.W.obj (P.muM (0,cM))}
    (a : A ⟶ B₁) :
    (P.pathFunctor pu).map (((P.pathFunctor pv).obj Y) ◁ a) ≫
        (P.reservoirContextIso pu hu pv hv Y B₁).hom =
      (P.reservoirContextIso pu hu pv hv Y A).hom ≫
        ((Y ≫ ReservoirWord.word P.W.toRouquierData P.ΛR pv hv) ◁ a) ▷
          ReservoirWord.word P.W.toRouquierData P.ΛR pu hu := by
  exact context_square (a := P.T.obj (-P.muP (0,cM)))
    (b := P.W.obj (P.muM (0,cR))) (c := P.W.obj (P.muM (0,cM)))
    (d := P.W.obj (P.muM (0,cL))) (A := A) (B₁ := B₁) (P.pathFunctor pu) (ReservoirWord.word P.W.toRouquierData P.ΛR pu hu)
    (P.reservoirWordFunctorIso pu hu) ((P.reservoirWordFunctorIso pv hv).app Y)
    (P.reservoirWordFunctorIso_hom_mem pv hv Y) a

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

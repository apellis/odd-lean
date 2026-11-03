import OddMath.QuiverHecke.SwappedAssembly.ReservoirContextCoordinates
import OddMath.QuiverHecke.SwappedAssembly.ReservoirLayerDistinctCrossings

/-! # Distinct reservoir crossings in both word contexts

SwappedVacuumCoordinates §§2–6: retain the original source/target sector
transport when moving the actual distinct-colour layer matrix into both
reversed reservoir-word contexts.
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

private theorem refine_entry_square {C : Type*} [Category* C] {G X X' S T S' T' : C}
    (x : G ⟶ X) (m : G ⟶ X') (e : X ≅ S) (d : X' ≅ T) (f : S ≅ S') (g : T ≅ T')
    (a : S ⟶ T) (b : S' ⟶ T') (hm : m ≫ d.hom = x ≫ e.hom ≫ a)
    (ha : a ≫ g.hom = f.hom ≫ b) :
    m ≫ (d ≪≫ g).hom = x ≫ (e ≪≫ f).hom ≫ b := by
  calc
    m ≫ (d ≪≫ g).hom = (m ≫ d.hom) ≫ g.hom := by simp only [Iso.trans_hom, Category.assoc]
    _ = (x ≫ e.hom ≫ a) ≫ g.hom := congrArg (fun z => z ≫ g.hom) hm
    _ = x ≫ (e ≪≫ f).hom ≫ b := by
      simp only [Iso.trans_hom, Category.assoc]
      rw [ha]

namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

private def rightPath {r : List (Col I X)} {cR cR' d : I →₀ ℕ}
    (h : cR = cR') (pv : SPath r (0,cR') (0,d)) : SPath r (0,cR) (0,d) := by
  subst cR'
  exact pv

private def rightValue {cR cR' : I →₀ ℕ} (h : ((0,cR) : Sector I) = (0,cR'))
    (Z : P.H (0,cR')) : P.H (0,cR) := h ▸ Z

private def castContextIso {l r : List (Col I X)} {cL cM cR cR' d : I →₀ ℕ}
    (h : ((0,cR) : Sector I) = (0,cR'))
    (pu : SPath l (0,cL) (0,cM)) (hu : ∀ a ∈ l, a.l.1 = true)
    (pv : SPath r (0,cR') (0,d)) (hr : ∀ a ∈ r, a.l.1 = true)
    (Y : P.H (0,d)) (A : P.W.obj (P.muM (0,cR)) ⟶ P.W.obj (P.muM (0,cM))) :
    (P.pathFunctor pu).obj (rightValue P (cR := cR) (cR' := cR') h ((P.pathFunctor pv).obj Y) ≫ A) ≅
      ((Y ≫ ReservoirWord.word P.W.toRouquierData P.ΛR (rightPath (congrArg Prod.snd h) pv) hr) ≫ A) ≫
        ReservoirWord.word P.W.toRouquierData P.ΛR pu hu := by
  have hc : cR = cR' := congrArg Prod.snd h
  subst cR'
  exact P.reservoirContextIso pu hu pv hr Y A

private theorem castContext_square {l r : List (Col I X)} {cL cM cR cR' d : I →₀ ℕ}
    (h : ((0,cR) : Sector I) = (0,cR'))
    (pu : SPath l (0,cL) (0,cM)) (hu : ∀ a ∈ l, a.l.1 = true)
    (pv : SPath r (0,cR') (0,d)) (hr : ∀ a ∈ r, a.l.1 = true)
    (Y : P.H (0,d)) {A B₁ : P.W.obj (P.muM (0,cR)) ⟶ P.W.obj (P.muM (0,cM))} (a : A ⟶ B₁) :
    (P.pathFunctor pu).map (rightValue P (cR := cR) (cR' := cR') h ((P.pathFunctor pv).obj Y) ◁ a) ≫
        (castContextIso P h pu hu pv hr Y B₁).hom =
      (castContextIso P h pu hu pv hr Y A).hom ≫
        ((Y ≫ ReservoirWord.word P.W.toRouquierData P.ΛR (rightPath (congrArg Prod.snd h) pv) hr) ◁ a) ▷
          ReservoirWord.word P.W.toRouquierData P.ΛR pu hu := by
  have hc : cR = cR' := congrArg Prod.snd h
  subst cR'
  exact P.reservoirContext_square pu hu pv hr Y a

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
private theorem crossEdge (i j : I) (c : I →₀ ℕ)
    (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c))) :
    P.muM (0,c - Finsupp.single i 1 - Finsupp.single j 1) + D.α i =
      P.muM (0,c - Finsupp.single j 1) := by
  change P.muM (nextSector (true,j) false (nextSector (true,i) false (0,c))) + D.α i = _
  rw [hs]
  exact P.reservoirVacuumEdge i (c - Finsupp.single j 1) hw₂

/-- The source layer chart retains the actual right path reindexed by
the crossing's equality of formal endpoints, then both reversed words. -/
def reservoirLayerCrossSourceWordIso (ν : X) (u v : List (Letter I)) (i j : I)
    {cL c d : I →₀ ℕ}
    (hv₁ : StepValid (true,i) false (0,c))
    (hv₂ : StepValid (true,j) false (nextSector (true,i) false (0,c)))
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c)))
    (pu : SPath (SKM.lay D ν u (.cross i j) v).left (0,cL) (0,c))
    (hu : ∀ a ∈ (SKM.lay D ν u (.cross i j) v).left, a.l.1 = true)
    (pv : SPath (SKM.lay D ν u (.cross i j) v).right
      (0,c - Finsupp.single j 1 - Finsupp.single i 1) (0,d))
    (hr : ∀ a ∈ (SKM.lay D ν u (.cross i j) v).right, a.l.1 = true)
    (Y : P.H (0,d)) :
    (P.pathFunctor ((pu.append (SPath.two
      (c₁ := ⟨up i, SKM.wt D (SKM.wt D ν v) [up j]⟩) (c₂ := ⟨up j,SKM.wt D ν v⟩)
      false false hv₁ hv₂ hs)).append pv)).obj Y ≅
      ((Y ≫ ReservoirWord.word P.W.toRouquierData P.ΛR (rightPath (congrArg Prod.snd hs) pv) hr) ≫
        P.W.E j (P.reservoirVacuumEdge j (c - Finsupp.single i 1) hv₂) ≫
        P.W.E i (P.reservoirVacuumEdge i c hv₁)) ≫
          ReservoirWord.word P.W.toRouquierData P.ΛR pu hu :=
  P.reservoirLayerCrossSourceIso ν u v i j hv₁ hv₂ hs pu pv Y ≪≫
    castContextIso P hs pu hu pv hr Y (P.W.E j (P.reservoirVacuumEdge j (c - Finsupp.single i 1) hv₂) ≫
      P.W.E i (P.reservoirVacuumEdge i c hv₁))

/-- The target layer chart uses the same transported right reservoir
word as the source, with the original target-sector transport retained. -/
def reservoirLayerCrossTargetWordIso (ν : X) (u v : List (Letter I)) (i j : I)
    {cL c d : I →₀ ℕ}
    (hw₁ : StepValid (true,j) false (0,c))
    (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c)))
    (pu : SPath (SKM.lay D ν u (.cross i j) v).left (0,cL) (0,c))
    (hu : ∀ a ∈ (SKM.lay D ν u (.cross i j) v).left, a.l.1 = true)
    (pv : SPath (SKM.lay D ν u (.cross i j) v).right
      (0,c - Finsupp.single j 1 - Finsupp.single i 1) (0,d))
    (hr : ∀ a ∈ (SKM.lay D ν u (.cross i j) v).right, a.l.1 = true)
    (Y : P.H (0,d)) :
    (P.pathFunctor ((pu.append (SPath.two
      (c₁ := ⟨up j, SKM.wt D (SKM.wt D ν v) [up i]⟩) (c₂ := ⟨up i,SKM.wt D ν v⟩)
      false false hw₁ hw₂ rfl)).append pv)).obj Y ≅
      ((Y ≫ ReservoirWord.word P.W.toRouquierData P.ΛR (rightPath (congrArg Prod.snd hs) pv) hr) ≫
        P.W.E i (crossEdge P i j c hw₂ hs) ≫ P.W.E j (P.reservoirVacuumEdge j c hw₁)) ≫
          ReservoirWord.word P.W.toRouquierData P.ΛR pu hu :=
  P.reservoirLayerCrossTargetIso ν u v i j hw₁ hw₂ hs pu pv Y ≪≫
    castContextIso P hs pu hu pv hr Y (P.W.E i (crossEdge P i j c hw₂ hs) ≫
      P.W.E j (P.reservoirVacuumEdge j c hw₁))

/-- The actual distinct-colour layer matrix, in both reversed reservoir
word contexts, is the unchanged two-whiskered factor crossing. All
input matrix entries and all parity components are retained. -/
theorem layerMap_reservoir_cross_ne_word (a : P.CrossCoeff) {Gs Ys : ∀ s, P.H s}
    (ν : X) (u v : List (Letter I)) (i j : I) (hij : i ≠ j)
    (x : P.Mod Gs Ys (SKM.lay D ν u (.cross i j) v).dom)
    {cL c d : I →₀ ℕ}
    (hv₁ : StepValid (true,i) false (0,c))
    (hv₂ : StepValid (true,j) false (nextSector (true,i) false (0,c)))
    (hw₁ : StepValid (true,j) false (0,c))
    (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c)))
    (pu : SPath (SKM.lay D ν u (.cross i j) v).left (0,cL) (0,c))
    (hu : ∀ b ∈ (SKM.lay D ν u (.cross i j) v).left, b.l.1 = true)
    (pv : SPath (SKM.lay D ν u (.cross i j) v).right
      (0,c - Finsupp.single j 1 - Finsupp.single i 1) (0,d))
    (hr : ∀ b ∈ (SKM.lay D ν u (.cross i j) v).right, b.l.1 = true)
    (hq : P.wt (0,d) = (SKM.lay D ν u (.cross i j) v).cod.endR) :
    P.layerMap (P.upwardGens a) (SKM.lay D ν u (.cross i j) v) x (0,cL) ⟨(0,d),hq⟩
        ((pu.append (SPath.two false false hw₁ hw₂ rfl)).append pv) ≫
        (P.reservoirLayerCrossTargetWordIso ν u v i j hw₁ hw₂ hs pu hu pv hr (Ys (0,d))).hom =
      x (0,cL) ⟨(0,d),hq.trans (SKM.lay_valid D ν u (.cross i j) v).endR_eq⟩
        ((pu.append (SPath.two false false hv₁ hv₂ hs)).append pv) ≫
        (P.reservoirLayerCrossSourceWordIso ν u v i j hv₁ hv₂ hs pu hu pv hr (Ys (0,d))).hom ≫
        (((Ys (0,d) ≫ ReservoirWord.word P.W.toRouquierData P.ΛR
          (rightPath (congrArg Prod.snd hs) pv) hr) ◁
            P.W.cross i j (P.reservoirVacuumEdge j (c - Finsupp.single i 1) hv₂)
              (P.reservoirVacuumEdge i c hv₁) (crossEdge P i j c hw₂ hs)
              (P.reservoirVacuumEdge j c hw₁)) ▷
          ReservoirWord.word P.W.toRouquierData P.ΛR pu hu) := by
  exact refine_entry_square _ _ (P.reservoirLayerCrossSourceIso ν u v i j hv₁ hv₂ hs pu pv (Ys (0,d)))
    (P.reservoirLayerCrossTargetIso ν u v i j hw₁ hw₂ hs pu pv (Ys (0,d)))
    (castContextIso P hs pu hu pv hr (Ys (0,d))
      (P.W.E j (P.reservoirVacuumEdge j (c - Finsupp.single i 1) hv₂) ≫
        P.W.E i (P.reservoirVacuumEdge i c hv₁)))
    (castContextIso P hs pu hu pv hr (Ys (0,d))
      (P.W.E i (crossEdge P i j c hw₂ hs) ≫ P.W.E j (P.reservoirVacuumEdge j c hw₁))) _ _
    (P.layerMap_reservoir_cross_ne a ν u v i j hij hr x hv₁ hv₂ hw₁ hw₂ hs pu pv hq)
    (castContext_square P hs pu hu pv hr (Ys (0,d))
      (P.W.cross i j (P.reservoirVacuumEdge j (c - Finsupp.single i 1) hv₂)
        (P.reservoirVacuumEdge i c hv₁) (crossEdge P i j c hw₂ hs) (P.reservoirVacuumEdge j c hw₁)))

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

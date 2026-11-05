import OddMath.SKM.RouquierHomPostPowers
import OddMath.SKM.RouquierReflectedLocal

/-!
# Content-shifted postcomposition augmented inverses

The finite-window construction of `HomProbeMatrix.md` §4 (10)–(13) uses
all entries of the specified factor inverse. No biproduct objects or inverse
for the content-shifted sector are assumed. `homContentPostInvPos` and
`homContentPostInvNeg` supply all five products over any commutative ring,
for both colour parities and every fixed content, including height zero.

The `_even` theorems give all products on literal parity-shifted summands;
the `_even_principal` and `_even_dotted` comparisons retain these objects.
The even source and target coordinates commute with the parity-shift datum
by its naturality law, without dropping a shift or a Koszul scalar.

These are pointwise inverse data. Bundling natural transformations in the
probe variable, a full Hom Rouquier family, a fused action, and existence of
a nonzero factor representation are separate tasks and are not claimed here.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section Transport
variable {k : Type r} [CommRing k]
  {C C' : Type*} [Category C] [Category C']
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive C'] [Linear k C'] [Supercategory k C']
  (F : C ⥤ C') [F.Additive] [F.Linear k] [IsSuperfunctor k F]
  {A B Z : C} {A' B' Z' : C'}
  (a : A' ≅ F.obj A) (b : B' ≅ F.obj B) (c : Z' ≅ F.obj Z)
  (ha : a.hom ∈ parity (R := k) _ _ 0)
  (hb : b.hom ∈ parity (R := k) _ _ 0)
  (hc : c.hom ∈ parity (R := k) _ _ 0)
  {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}

/-- Transport all rows and columns, preserving the finite-window equations. -/
def SuperSumInvTo.mapCoordinates {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
    (J : SuperSumInvTo (k := k) f g p q n) :
    SuperSumInvTo (k := k) (a.hom ≫ F.map f ≫ b.inv)
      (fun m => a.hom ≫ F.map (g m) ≫ c.inv) p q n where
  f' := b.hom ≫ F.map J.f' ≫ a.inv
  g' m := c.hom ≫ F.map (J.g' m) ≫ a.inv
  f_mem := by simpa using comp_mem ha (comp_mem (map_mem F J.f_mem) (inv_mem b hb))
  g_mem m := by simpa using comp_mem ha (comp_mem (map_mem F (J.g_mem m)) (inv_mem c hc))
  f'_mem := by simpa using comp_mem hb (comp_mem (map_mem F J.f'_mem) (inv_mem a ha))
  g'_mem m := by simpa using comp_mem hc (comp_mem (map_mem F (J.g'_mem m)) (inv_mem a ha))
  total := by
    have ht := congrArg (fun t => a.hom ≫ F.map t ≫ a.inv) J.total
    simpa [Functor.map_add, Functor.map_sum, Functor.map_comp, Preadditive.comp_add,
      Preadditive.add_comp, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc] using ht
  ff := by simp [Category.assoc, ← F.map_comp_assoc, J.ff]
  fg m hm := by simp [Category.assoc, ← F.map_comp_assoc, J.fg m hm]
  gf m hm := by simp [Category.assoc, ← F.map_comp_assoc, J.gf m hm]
  gg m l hm hl := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← F.map_comp_assoc]
    rw [J.gg m l hm hl]
    split_ifs <;> simp

/-- Transport the column presentation, including every inverse row. -/
def SuperSumInvFrom.mapCoordinates {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    (J : SuperSumInvFrom (k := k) f g p q n) :
    SuperSumInvFrom (k := k) (b.hom ≫ F.map f ≫ a.inv)
      (fun m => c.hom ≫ F.map (g m) ≫ a.inv) p q n where
  f' := a.hom ≫ F.map J.f' ≫ b.inv
  g' m := a.hom ≫ F.map (J.g' m) ≫ c.inv
  f_mem := by simpa using comp_mem hb (comp_mem (map_mem F J.f_mem) (inv_mem a ha))
  g_mem m := by simpa using comp_mem hc (comp_mem (map_mem F (J.g_mem m)) (inv_mem a ha))
  f'_mem := by simpa using comp_mem ha (comp_mem (map_mem F J.f'_mem) (inv_mem b hb))
  g'_mem m := by simpa using comp_mem ha (comp_mem (map_mem F (J.g'_mem m)) (inv_mem c hc))
  total := by
    have ht := congrArg (fun t => a.hom ≫ F.map t ≫ a.inv) J.total
    simpa [Functor.map_add, Functor.map_sum, Functor.map_comp, Preadditive.comp_add,
      Preadditive.add_comp, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc] using ht
  ff := by simp [Category.assoc, ← F.map_comp_assoc, J.ff]
  fg m hm := by simp [Category.assoc, ← F.map_comp_assoc, J.fg m hm]
  gf m hm := by simp [Category.assoc, ← F.map_comp_assoc, J.gf m hm]
  gg m l hm hl := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← F.map_comp_assoc]
    rw [J.gg m l hm hl]
    split_ifs <;> simp
end Transport

section EvenCoordinates
variable {k : Type r} [CommRing k] {C : Type*} [Category C]
  [Preadditive C] [Linear k C] [Supercategory k C] [PiSupercategory k C]

end EvenCoordinates

section Post
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
  (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM rhoM : X}
  (h : muM + D.α i = nuM) (h₂ : nuM + D.α i = rhoM)

/-- The source coordinate including its even associator. -/
def homContentPostInverseSource (Z : homWeightSector T W.obj muP nuM) :=
  homContentPostSourceIso T W i betaP muP h Z ≪≫ associator Z (W.F i h) (W.E i h)

/-- The target coordinate including its even associator. -/
def homContentPostInverseTarget (Z : homWeightSector T W.obj muP nuM) :=
  homContentPostTargetIso T W i betaP muP h₂ Z ≪≫ associator Z (W.E i h₂) (W.F i h₂)

theorem homContentPostInverseSource_mem (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostInverseSource T W i betaP muP h Z).hom ∈ parity (R := k) _ _ 0 :=
  by
    dsimp only [homContentPostInverseSource, Iso.trans_hom, homContentPostSourceIso]
    exact comp_mem (homShiftConjugationIso_mem
      (homPost (k := k) (W.F i h) ⋙ homPost (k := k) (W.E i h))
      (homContentShift D i betaP) Z)
      (TwoSupercategory.associator_hom_mem (R := k) Z (W.F i h) (W.E i h))

theorem homContentPostInverseTarget_mem (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostInverseTarget T W i betaP muP h₂ Z).hom ∈ parity (R := k) _ _ 0 :=
  comp_mem (map_mem (homPost (k := k) (W.F i h₂)) (homParityShiftSquare_mem _ _))
    (TwoSupercategory.associator_hom_mem (R := k) _ _ _)

/-- The prescribed principal mate, not defined by a coordinate conjugation. -/
def homContentPostMate (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostE T W i betaP muP h).obj ((homContentPostF T W i betaP muP h).obj Z) ⟶
      (homContentPostF T W i betaP muP h₂).obj ((homContentPostE T W i betaP muP h₂).obj Z) :=
  (rouquierMate (homContentPostSuperAdjunction T W i betaP muP h)
    (homContentPostSuperAdjunction T W i betaP muP h₂)
    (homContentPostCrossing T W i betaP muP h h₂)).app (D.parity i) Z

theorem homContentPostMate_coordinates (Z : homWeightSector T W.obj muP nuM) :
    homContentPostMate T W i betaP muP h h₂ Z =
      (homContentPostInverseSource T W i betaP muP h Z).hom ≫
        Z ◁ (W.loc i h h₂).sig ≫ (homContentPostInverseTarget T W i betaP muP h₂ Z).inv := by
  have ht := homContentPostCrossing_principal T W i betaP muP h h₂ Z
  apply (cancel_mono (homContentPostTargetIso T W i betaP muP h₂ Z).hom).mp
  apply (cancel_epi (homContentPostSourceIso T W i betaP muP h Z).inv).mp
  simpa [homContentPostMate, homContentPostInverseSource, homContentPostInverseTarget,
    Category.assoc] using ht

theorem homContentPostCap_factor (n : ℕ) (Z : homWeightSector T W.obj muP nuM) :
    homContentPostCap T W i betaP muP h n Z =
      (homContentPostInverseSource T W i betaP muP h Z).hom ≫
        Z ◁ ((W.F i h) ◁ rouquierPower (W.dot i h) n ≫ (W.adj i h).counit) ≫
        (rightUnitor Z).hom := by
  rw [homContentPostCap_coordinates]
  simp only [homContentPostInverseSource, Iso.trans_hom, TwoSupercategory.whiskerLeft_comp (R := k),
    Category.assoc]
  rw [← TwoSupercategory.associator_naturality_right_assoc (R := k)]

theorem homContentPostCup_factor (n : ℕ) (Z : homWeightSector T W.obj muP nuM) :
    homContentPostCup T W i betaP muP h₂ n Z =
      (rightUnitor Z).inv ≫
        Z ◁ ((W.adj i h₂).unit ≫ rouquierPower (W.dot i h₂) n ▷ W.F i h₂) ≫
        (homContentPostInverseTarget T W i betaP muP h₂ Z).inv := by
  apply (cancel_mono (homContentPostTargetIso T W i betaP muP h₂ Z).hom).mp
  rw [homContentPostCup_coordinates]
  simp only [homContentPostInverseTarget, Iso.trans_inv,
    TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [TwoSupercategory.associator_inv_naturality_middle (R := k)]

/-- The entire specified positive-height inverse after postcomposition and
content shift. The forward entries are the mate and dotted counits. -/
def homContentPostInvPos (hh : 0 ≤ D.h i nuM) (Z : homWeightSector T W.obj muP nuM) :
    SuperSumInvTo (k := k) (homContentPostMate T W i betaP muP h h₂ Z)
      (fun n => homContentPostCap T W i betaP muP h n Z)
      (D.parity i) (fun n => n * D.parity i) (D.h i nuM).toNat :=
  ((W.loc i h h₂).invPos hh |>.mapCoordinates (homPre (k := k) Z)
    (homContentPostInverseSource T W i betaP muP h Z)
    (homContentPostInverseTarget T W i betaP muP h₂ Z) (rightUnitor Z).symm
    (homContentPostInverseSource_mem T W i betaP muP h Z)
    (homContentPostInverseTarget_mem T W i betaP muP h₂ Z)
    (inv_mem (rightUnitor Z) (TwoSupercategory.rightUnitor_hom_mem (R := k) Z))).copyMaps
      _ _ (homContentPostMate_coordinates T W i betaP muP h h₂ Z)
      (funext fun n => homContentPostCap_factor T W i betaP muP h n Z)

/-- The entire specified negative-height inverse. The forward columns are
still the prescribed mate and dotted units, including the empty window. -/
def homContentPostInvNeg (hh : D.h i nuM ≤ 0) (Z : homWeightSector T W.obj muP nuM) :
    SuperSumInvFrom (k := k) (homContentPostMate T W i betaP muP h h₂ Z)
      (fun n => homContentPostCup T W i betaP muP h₂ n Z)
      (D.parity i) (fun n => n * D.parity i) (-D.h i nuM).toNat :=
  ((W.loc i h h₂).invNeg hh |>.mapCoordinates (homPre (k := k) Z)
    (homContentPostInverseTarget T W i betaP muP h₂ Z)
    (homContentPostInverseSource T W i betaP muP h Z) (rightUnitor Z).symm
    (homContentPostInverseTarget_mem T W i betaP muP h₂ Z)
    (homContentPostInverseSource_mem T W i betaP muP h Z)
    (inv_mem (rightUnitor Z) (TwoSupercategory.rightUnitor_hom_mem (R := k) Z))).copyMaps
      _ _ (homContentPostMate_coordinates T W i betaP muP h h₂ Z)
      (funext fun n => homContentPostCup_factor T W i betaP muP h₂ n Z)

/-- The inverse principal entry is the target coordinate, the specified factor
inverse, and the inverse source coordinate, in execution order. -/
theorem homContentPostInvPos_principal (hh : 0 ≤ D.h i nuM)
    (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostInvPos T W i betaP muP h h₂ hh Z).f' =
      (homContentPostInverseTarget T W i betaP muP h₂ Z).hom ≫
        Z ◁ ((W.loc i h h₂).invPos hh).f' ≫
        (homContentPostInverseSource T W i betaP muP h Z).inv := rfl

theorem homContentPostInvPos_column (hh : 0 ≤ D.h i nuM)
    (Z : homWeightSector T W.obj muP nuM) (n : ℕ) :
    (homContentPostInvPos T W i betaP muP h h₂ hh Z).g' n =
      (rightUnitor Z).inv ≫ Z ◁ ((W.loc i h h₂).invPos hh).g' n ≫
        (homContentPostInverseSource T W i betaP muP h Z).inv := rfl

theorem homContentPostInvNeg_principal (hh : D.h i nuM ≤ 0)
    (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostInvNeg T W i betaP muP h h₂ hh Z).f' =
      (homContentPostInverseTarget T W i betaP muP h₂ Z).hom ≫
        Z ◁ ((W.loc i h h₂).invNeg hh).f' ≫
        (homContentPostInverseSource T W i betaP muP h Z).inv := rfl

theorem homContentPostInvNeg_row (hh : D.h i nuM ≤ 0)
    (Z : homWeightSector T W.obj muP nuM) (n : ℕ) :
    (homContentPostInvNeg T W i betaP muP h h₂ hh Z).g' n =
      (homContentPostInverseTarget T W i betaP muP h₂ Z).hom ≫
        Z ◁ ((W.loc i h h₂).invNeg hh).g' n ≫ (rightUnitor Z).hom := rfl

end Post
end OddMath.SKM

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

private theorem shift_even_hom (p : ZMod 2) {A B : C} (e : A ⟶ B)
    (he : e ∈ parity (R := k) _ _ 0) :
    ((homParityShiftDatum (k := k) p).iso A).hom ≫ e =
      (homParityShift (k := k) p).map e ≫ ((homParityShiftDatum (k := k) p).iso B).hom := by
  simpa using ((homParityShiftDatum (k := k) p).hom_naturality he).symm

private theorem shift_even_inv (p : ZMod 2) {A B : C} (e : A ⟶ B)
    (he : e ∈ parity (R := k) _ _ 0) :
    ((homParityShiftDatum (k := k) p).iso A).inv ≫ (homParityShift (k := k) p).map e =
      e ≫ ((homParityShiftDatum (k := k) p).iso B).inv := by
  apply (cancel_epi ((homParityShiftDatum (k := k) p).iso A).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    reassoc_of% (shift_even_hom p e he), Iso.hom_inv_id, Category.comp_id]
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
/-- The zeroth cap is exactly the specified counit. -/
theorem homContentPostCap_zero (Z : homWeightSector T W.obj muP nuM) :
    homContentPostCap T W i betaP muP h 0 Z =
      (homContentPostAdjunction T W i betaP muP h).counit.app Z := by
  simp [homContentPostCap]

/-- The zeroth cup is exactly the specified unit. -/
theorem homContentPostCup_zero (Z : homWeightSector T W.obj muP muM) :
    homContentPostCup T W i betaP muP h 0 Z =
      (homContentPostAdjunction T W i betaP muP h).unit.app Z := by
  simp [homContentPostCup]

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

/-- Both zero-height presentations have the same principal inverse. -/
theorem homContentPostInv_zero (hh : D.h i nuM = 0)
    (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostInvPos T W i betaP muP h h₂ (le_of_eq hh.symm) Z).f' =
      (homContentPostInvNeg T W i betaP muP h h₂ (le_of_eq hh) Z).f' := by
  let P := homContentPostInvPos T W i betaP muP h h₂ (le_of_eq hh.symm) Z
  let N := homContentPostInvNeg T W i betaP muP h h₂ (le_of_eq hh) Z
  have hn : homContentPostMate T W i betaP muP h h₂ Z ≫ N.f' = 𝟙 _ := N.ff
  calc P.f' = P.f' ≫ (homContentPostMate T W i betaP muP h h₂ Z ≫ N.f') := by rw [hn, Category.comp_id]
       _ = N.f' := by rw [← Category.assoc, P.ff, Category.id_comp]
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
/-- Literal parity-shifted components are even and satisfy every inverse
product. The diagonal identity is on the shifted object itself. -/
theorem homContentPostInvPos_even (hh : 0 ≤ D.h i nuM)
    (Z : homWeightSector T W.obj muP nuM) :
    let J := homContentPostInvPos T W i betaP muP h h₂ hh Z
    let z := (homParityShiftDatum (k := k) (D.parity i)).iso ((homContentPostF T W i betaP muP h₂).obj ((homContentPostE T W i betaP muP h₂).obj Z))
    let zs := fun n : ℕ => (homParityShiftDatum (k := k) (n * D.parity i)).iso Z
    let f := homContentPostMate T W i betaP muP h h₂ Z ≫ z.inv
    let g := fun n => homContentPostCap T W i betaP muP h n Z ≫ (zs n).inv
    let j := z.hom ≫ J.f'
    let a := fun n => (zs n).hom ≫ J.g' n
    (f ∈ parity (R := k) _ _ 0) ∧
    (∀ n, g n ∈ parity (R := k) _ _ 0) ∧
    (j ∈ parity (R := k) _ _ 0) ∧
    (∀ n, a n ∈ parity (R := k) _ _ 0) ∧
    (f ≫ j + ∑ n ∈ Finset.range (D.h i nuM).toNat, g n ≫ a n = 𝟙 _) ∧
    (j ≫ f = 𝟙 _) ∧
    (∀ n, n < (D.h i nuM).toNat → j ≫ g n = 0) ∧
    (∀ n, n < (D.h i nuM).toNat → a n ≫ f = 0) ∧
    (∀ n, n < (D.h i nuM).toNat → a n ≫ g n = 𝟙 _) ∧
    (∀ n m, n < (D.h i nuM).toNat → m < (D.h i nuM).toNat → n ≠ m → a n ≫ g m = 0) := by
  let J := homContentPostInvPos T W i betaP muP h h₂ hh Z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [zmod2_add_self] using comp_mem J.f_mem ((homParityShiftDatum (k := k) (D.parity i)).inv_mem _)
  · intro n
    simpa only [zmod2_add_self] using comp_mem (J.g_mem n) ((homParityShiftDatum (k := k) (n * D.parity i)).inv_mem _)
  · simpa only [zmod2_add_self] using comp_mem ((homParityShiftDatum (k := k) (D.parity i)).hom_mem _) J.f'_mem
  · intro n
    simpa only [zmod2_add_self] using comp_mem ((homParityShiftDatum (k := k) (n * D.parity i)).hom_mem _) (J.g'_mem n)
  · simpa only [Category.assoc, Iso.inv_hom_id_assoc] using J.total
  · simp only [Category.assoc]
    rw [← Category.assoc J.f', J.ff]
    simp
  · intro n hn
    simp only [Category.assoc]
    rw [← Category.assoc J.f', J.fg n hn]
    simp
  · intro n hn
    simp only [Category.assoc]
    rw [← Category.assoc (J.g' n), J.gf n hn]
    simp
  · intro n hn
    simp only [Category.assoc]
    rw [← Category.assoc (J.g' n), J.gg n n hn hn]
    simp
  · intro n m hn hm hnm
    simp only [Category.assoc]
    rw [← Category.assoc (J.g' n), J.gg n m hn hm]
    simp [hnm]

/-- Literal parity-shifted components are even and satisfy every inverse
product. The diagonal identity is on the shifted object itself. -/
theorem homContentPostInvNeg_even (hh : D.h i nuM ≤ 0)
    (Z : homWeightSector T W.obj muP nuM) :
    let J := homContentPostInvNeg T W i betaP muP h h₂ hh Z
    let z := (homParityShiftDatum (k := k) (D.parity i)).iso ((homContentPostE T W i betaP muP h).obj ((homContentPostF T W i betaP muP h).obj Z))
    let zs := fun n : ℕ => (homParityShiftDatum (k := k) (n * D.parity i)).iso Z
    let f := z.hom ≫ homContentPostMate T W i betaP muP h h₂ Z
    let g := fun n => (zs n).hom ≫ homContentPostCup T W i betaP muP h₂ n Z
    let j := J.f' ≫ z.inv
    let a := fun n => J.g' n ≫ (zs n).inv
    (f ∈ parity (R := k) _ _ 0) ∧
    (∀ n, g n ∈ parity (R := k) _ _ 0) ∧
    (j ∈ parity (R := k) _ _ 0) ∧
    (∀ n, a n ∈ parity (R := k) _ _ 0) ∧
    (j ≫ f + ∑ n ∈ Finset.range (-D.h i nuM).toNat, a n ≫ g n = 𝟙 _) ∧
    (f ≫ j = 𝟙 _) ∧
    (∀ n, n < (-D.h i nuM).toNat → f ≫ a n = 0) ∧
    (∀ n, n < (-D.h i nuM).toNat → g n ≫ j = 0) ∧
    (∀ n, n < (-D.h i nuM).toNat → g n ≫ a n = 𝟙 _) ∧
    (∀ n m, n < (-D.h i nuM).toNat → m < (-D.h i nuM).toNat → n ≠ m → g n ≫ a m = 0) := by
  let J := homContentPostInvNeg T W i betaP muP h h₂ hh Z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [zmod2_add_self] using comp_mem ((homParityShiftDatum (k := k) (D.parity i)).hom_mem _) J.f_mem
  · intro n
    simpa only [zmod2_add_self] using comp_mem ((homParityShiftDatum (k := k) (n * D.parity i)).hom_mem _) (J.g_mem n)
  · simpa only [zmod2_add_self] using comp_mem J.f'_mem ((homParityShiftDatum (k := k) (D.parity i)).inv_mem _)
  · intro n
    simpa only [zmod2_add_self] using comp_mem (J.g'_mem n) ((homParityShiftDatum (k := k) (n * D.parity i)).inv_mem _)
  · simpa only [Category.assoc, Iso.inv_hom_id_assoc] using J.total
  · simp only [Category.assoc]
    rw [← Category.assoc (homContentPostMate T W i betaP muP h h₂ Z), J.ff]
    simp
  · intro n hn
    simp only [Category.assoc]
    rw [← Category.assoc (homContentPostMate T W i betaP muP h h₂ Z), J.fg n hn]
    simp
  · intro n hn
    simp only [Category.assoc]
    rw [← Category.assoc (homContentPostCup T W i betaP muP h₂ n Z), J.gf n hn]
    simp
  · intro n hn
    simp only [Category.assoc]
    rw [← Category.assoc (homContentPostCup T W i betaP muP h₂ n Z), J.gg n n hn hn]
    simp
  · intro n m hn hm hnm
    simp only [Category.assoc]
    rw [← Category.assoc (homContentPostCup T W i betaP muP h₂ n Z), J.gg n m hn hm]
    simp [hnm]
/-- Even principal row comparison: naturality against the even target
coordinate introduces no Koszul scalar. -/
theorem homContentPostMate_even_to (Z : homWeightSector T W.obj muP nuM) :
    let a := homContentPostInverseSource T W i betaP muP h Z
    let b := homContentPostInverseTarget T W i betaP muP h₂ Z
    let S := homParityShift (k := k) (D.parity i)
    let z := homParityShiftDatum (k := k) (D.parity i)
    homContentPostMate T W i betaP muP h h₂ Z ≫ (z.iso _).inv ≫ S.map b.hom =
      a.hom ≫ Z ◁ (W.loc i h h₂).sig ≫ (z.iso _).inv := by
  dsimp only
  rw [shift_even_inv _ _ (homContentPostInverseTarget_mem T W i betaP muP h₂ Z),
    homContentPostMate_coordinates]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Even inverse column comparison, with the same shifted target coordinate. -/
theorem homContentPostInvPos_even_principal (hh : 0 ≤ D.h i nuM)
    (Z : homWeightSector T W.obj muP nuM) :
    let a := homContentPostInverseSource T W i betaP muP h Z
    let b := homContentPostInverseTarget T W i betaP muP h₂ Z
    let S := homParityShift (k := k) (D.parity i)
    let z := homParityShiftDatum (k := k) (D.parity i)
    (z.iso _).hom ≫ (homContentPostInvPos T W i betaP muP h h₂ hh Z).f' =
      S.map b.hom ≫ (z.iso _).hom ≫ Z ◁ ((W.loc i h h₂).invPos hh).f' ≫ a.inv := by
  dsimp only
  rw [homContentPostInvPos_principal,
    ← Category.assoc ((homParityShiftDatum (k := k) (D.parity i)).iso _).hom,
    shift_even_hom _ _ (homContentPostInverseTarget_mem T W i betaP muP h₂ Z)]
  simp only [Category.assoc]

/-- Even principal column comparison uses the shifted source coordinate. -/
theorem homContentPostMate_even_from (Z : homWeightSector T W.obj muP nuM) :
    let a := homContentPostInverseSource T W i betaP muP h Z
    let b := homContentPostInverseTarget T W i betaP muP h₂ Z
    let S := homParityShift (k := k) (D.parity i)
    let z := homParityShiftDatum (k := k) (D.parity i)
    (z.iso _).hom ≫ homContentPostMate T W i betaP muP h h₂ Z =
      S.map a.hom ≫ (z.iso _).hom ≫ Z ◁ (W.loc i h h₂).sig ≫ b.inv := by
  dsimp only
  rw [homContentPostMate_coordinates,
    ← Category.assoc ((homParityShiftDatum (k := k) (D.parity i)).iso _).hom,
    shift_even_hom _ _ (homContentPostInverseSource_mem T W i betaP muP h Z)]
  simp only [Category.assoc]

/-- Even inverse row comparison retains the literal source parity shift. -/
theorem homContentPostInvNeg_even_principal (hh : D.h i nuM ≤ 0)
    (Z : homWeightSector T W.obj muP nuM) :
    let a := homContentPostInverseSource T W i betaP muP h Z
    let b := homContentPostInverseTarget T W i betaP muP h₂ Z
    let S := homParityShift (k := k) (D.parity i)
    let z := homParityShiftDatum (k := k) (D.parity i)
    (homContentPostInvNeg T W i betaP muP h h₂ hh Z).f' ≫ (z.iso _).inv ≫ S.map a.hom =
      b.hom ≫ Z ◁ ((W.loc i h h₂).invNeg hh).f' ≫ (z.iso _).inv := by
  dsimp only
  rw [shift_even_inv _ _ (homContentPostInverseSource_mem T W i betaP muP h Z),
    homContentPostInvNeg_principal]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
/-- Both even identity-summand components use the same literal shifted object;
its coordinate is the identity, not a shift removal. -/
theorem homContentPostInvPos_even_dotted (hh : 0 ≤ D.h i nuM)
    (Z : homWeightSector T W.obj muP nuM) (n : ℕ) :
    let a := homContentPostInverseSource T W i betaP muP h Z
    let z := (homParityShiftDatum (k := k) (n * D.parity i)).iso Z
    (homContentPostCap T W i betaP muP h n Z ≫ z.inv =
      a.hom ≫ Z ◁ ((W.F i h) ◁ rouquierPower (W.dot i h) n ≫ (W.adj i h).counit) ≫
        (rightUnitor Z).hom ≫ z.inv) ∧
    (z.hom ≫ (homContentPostInvPos T W i betaP muP h h₂ hh Z).g' n =
      z.hom ≫ (rightUnitor Z).inv ≫ Z ◁ ((W.loc i h h₂).invPos hh).g' n ≫ a.inv) := by
  dsimp only
  constructor
  · rw [homContentPostCap_factor]
    simp only [Category.assoc]
  · rw [homContentPostInvPos_column]

/-- The negative-height identity summands are shifted on the source side,
with no unsigned identification of their objects. -/
theorem homContentPostInvNeg_even_dotted (hh : D.h i nuM ≤ 0)
    (Z : homWeightSector T W.obj muP nuM) (n : ℕ) :
    let b := homContentPostInverseTarget T W i betaP muP h₂ Z
    let z := (homParityShiftDatum (k := k) (n * D.parity i)).iso Z
    (z.hom ≫ homContentPostCup T W i betaP muP h₂ n Z =
      z.hom ≫ (rightUnitor Z).inv ≫
        Z ◁ ((W.adj i h₂).unit ≫ rouquierPower (W.dot i h₂) n ▷ W.F i h₂) ≫ b.inv) ∧
    ((homContentPostInvNeg T W i betaP muP h h₂ hh Z).g' n ≫ z.inv =
      b.hom ≫ Z ◁ ((W.loc i h h₂).invNeg hh).g' n ≫ (rightUnitor Z).hom ≫ z.inv) := by
  dsimp only
  constructor
  · rw [homContentPostCup_factor]
  · rw [homContentPostInvNeg_row]
    simp only [Category.assoc]
end Post
end OddMath.SKM

import OddMath.SKM.RouquierSupernaturalInverse

/-!
# Postcomposition augmented inverses in SCat

The prescribed content-shifted postcomposition maps form both augmented
inverse presentations in the superfunctor category. These data retain all
homogeneous components and all natural-number window entries.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
  (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM rhoM : X}
  (h : muM + D.α i = nuM) (h₂ : nuM + D.α i = rhoM)

/-- Homogeneous lift of the specified principal mate. -/
def homContentPostSuperMate :
    homContentPostSuperF T W i betaP muP h ≫ homContentPostSuperE T W i betaP muP h ⟶
      homContentPostSuperE T W i betaP muP h₂ ≫ homContentPostSuperF T W i betaP muP h₂ :=
  (homContentPostMate_supernatural T W i betaP muP h h₂).toSuperNatTrans

/-- The bundled principal map equals the actual cup–crossing–cap mate. -/
theorem homContentPostSuperMate_eq : homContentPostSuperMate T W i betaP muP h h₂ =
    rouquierMate (homContentPostSuperAdjunction T W i betaP muP h)
      (homContentPostSuperAdjunction T W i betaP muP h₂)
      (homContentPostCrossing T W i betaP muP h h₂) := by
  have hm := rouquierMate_homogeneous
    (homContentPostSuperAdjunction T W i betaP muP h)
    (homContentPostSuperAdjunction T W i betaP muP h₂)
    (homContentPostCrossing_mem T W i betaP muP h h₂)
  apply Superfunctor.hom_ext
  intro q Z
  change (if q = D.parity i then _ else 0) = _
  by_cases hq : q = D.parity i
  · subst q; rw [ite_eq_left rfl]; rfl
  · rw [ite_eq_right hq]
    exact (Superfunctor.app_eq_zero_of_mem hm hq Z).symm

/-- Homogeneous dotted counit, with the prescribed dot powers. -/
def homContentPostSuperCap (n : ℕ) :
    homContentPostSuperF T W i betaP muP h ≫ homContentPostSuperE T W i betaP muP h ⟶
      𝟙 (SCat.of k (homWeightSector T W.obj muP nuM)) :=
  (homContentPostCap_supernatural T W i betaP muP h n).toSuperNatTrans

/-- Homogeneous dotted unit of the prescribed adjunction. -/
def homContentPostSuperCup (n : ℕ) :
    𝟙 (SCat.of k (homWeightSector T W.obj muP muM)) ⟶
      homContentPostSuperE T W i betaP muP h ≫ homContentPostSuperF T W i betaP muP h :=
  (homContentPostCup_supernatural T W i betaP muP h n).toSuperNatTrans

/-- Every component is the actual dot power followed by the specified counit. -/
theorem homContentPostSuperCap_app (n : ℕ) (q : ZMod 2)
    (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostSuperCap T W i betaP muP h n).app q Z =
      if q = n * D.parity i then
        (homContentPostDot T W i betaP muP h ((homContentPostF T W i betaP muP h).obj Z) ^ n) ≫
          (homContentPostAdjunction T W i betaP muP h).counit.app Z
      else 0 := rfl

/-- Every component uses the specified unit and actual dot power under the right adjoint. -/
theorem homContentPostSuperCup_app (n : ℕ) (q : ZMod 2)
    (Z : homWeightSector T W.obj muP muM) :
    (homContentPostSuperCup T W i betaP muP h n).app q Z =
      if q = n * D.parity i then
        (homContentPostAdjunction T W i betaP muP h).unit.app Z ≫
          (homContentPostF T W i betaP muP h).map (homContentPostDot T W i betaP muP h Z ^ n)
      else 0 := rfl

/-- All five positive-height inverse identities in the existing SCat Hom category. -/
def homContentPostSuperInvPos (hh : 0 ≤ D.h i nuM) :
    SuperSumInvTo (k := k) (homContentPostSuperMate T W i betaP muP h h₂)
      (homContentPostSuperCap T W i betaP muP h)
      (D.parity i) (fun n => n * D.parity i) (D.h i nuM).toNat :=
  SuperSumInvTo.supernatural (homContentPostInvPos T W i betaP muP h h₂ hh)
    (homContentPostMate_supernatural T W i betaP muP h h₂)
    (homContentPostCap_supernatural T W i betaP muP h)
    (homContentPostInvPos_principal_supernatural T W i betaP muP h h₂ hh)
    (homContentPostInvPos_column_supernatural T W i betaP muP h h₂ hh)

/-- All five negative-height inverse identities, retaining every raw inverse row. -/
def homContentPostSuperInvNeg (hh : D.h i nuM ≤ 0) :
    SuperSumInvFrom (k := k) (homContentPostSuperMate T W i betaP muP h h₂)
      (homContentPostSuperCup T W i betaP muP h₂)
      (D.parity i) (fun n => n * D.parity i) (-D.h i nuM).toNat :=
  SuperSumInvFrom.supernatural (homContentPostInvNeg T W i betaP muP h h₂ hh)
    (homContentPostMate_supernatural T W i betaP muP h h₂)
    (homContentPostCup_supernatural T W i betaP muP h₂)
    (homContentPostInvNeg_principal_supernatural T W i betaP muP h h₂ hh)
    (homContentPostInvNeg_row_supernatural T W i betaP muP h h₂ hh)

/-- The homogeneous inverse component is exactly the specified pointwise factor lift. -/
theorem homContentPostSuperInvPos_principal_app (hh : 0 ≤ D.h i nuM)
    (q : ZMod 2) (Z : homWeightSector T W.obj muP nuM) :
    ((homContentPostSuperInvPos T W i betaP muP h h₂ hh).f').app q Z =
      if q = D.parity i then (homContentPostInvPos T W i betaP muP h h₂ hh Z).f'
      else 0 := rfl

/-- The homogeneous inverse component is exactly the specified pointwise factor lift. -/
theorem homContentPostSuperInvNeg_principal_app (hh : D.h i nuM ≤ 0)
    (q : ZMod 2) (Z : homWeightSector T W.obj muP nuM) :
    ((homContentPostSuperInvNeg T W i betaP muP h h₂ hh).f').app q Z =
      if q = D.parity i then (homContentPostInvNeg T W i betaP muP h h₂ hh Z).f'
      else 0 := rfl

/-- The homogeneous inverse component is exactly the specified pointwise factor lift. -/
theorem homContentPostSuperInvPos_column_app (hh : 0 ≤ D.h i nuM) (n : ℕ)
    (q : ZMod 2) (Z : homWeightSector T W.obj muP nuM) :
    ((homContentPostSuperInvPos T W i betaP muP h h₂ hh).g' n).app q Z =
      if q = n * D.parity i then (homContentPostInvPos T W i betaP muP h h₂ hh Z).g' n
      else 0 := rfl

/-- The homogeneous inverse component is exactly the specified pointwise factor lift. -/
theorem homContentPostSuperInvNeg_row_app (hh : D.h i nuM ≤ 0) (n : ℕ)
    (q : ZMod 2) (Z : homWeightSector T W.obj muP nuM) :
    ((homContentPostSuperInvNeg T W i betaP muP h h₂ hh).g' n).app q Z =
      if q = n * D.parity i then (homContentPostInvNeg T W i betaP muP h h₂ hh Z).g' n
      else 0 := rfl

/-- The two zero-height inverses agree as supernatural transformations. -/
theorem homContentPostSuperInv_zero (hh : D.h i nuM = 0) :
    (homContentPostSuperInvPos T W i betaP muP h h₂ (le_of_eq hh.symm)).f' =
      (homContentPostSuperInvNeg T W i betaP muP h h₂ (le_of_eq hh)).f' := by
  apply Superfunctor.hom_ext
  intro p Z
  change (if p = D.parity i then _ else 0) = (if p = D.parity i then _ else 0)
  rw [homContentPostInv_zero T W i betaP muP h h₂ hh Z]

/-- Even natural transformation with literal `homParityShiftDatum` comparison. -/
def homContentPostEvenMateTo  :=
  (IsSupernatural.shiftTarget (homContentPostMate_supernatural T W i betaP muP h h₂)).toNatTrans

/-- Even natural transformation with literal `homParityShiftDatum` comparison. -/
def homContentPostEvenMateFrom  :=
  (IsSupernatural.shiftSource (homContentPostMate_supernatural T W i betaP muP h h₂)).toNatTrans

/-- Even natural transformation with literal `homParityShiftDatum` comparison. -/
def homContentPostEvenCap (n : ℕ) :=
  (IsSupernatural.shiftTarget (homContentPostCap_supernatural T W i betaP muP h n)).toNatTrans

/-- Even natural transformation with literal `homParityShiftDatum` comparison. -/
def homContentPostEvenCup (n : ℕ) :=
  (IsSupernatural.shiftSource (homContentPostCup_supernatural T W i betaP muP h n)).toNatTrans

/-- Even natural transformation with literal `homParityShiftDatum` comparison. -/
def homContentPostEvenInvPosPrincipal (hh : 0 ≤ D.h i nuM) :=
  (IsSupernatural.shiftSource (homContentPostInvPos_principal_supernatural T W i betaP muP h h₂ hh)).toNatTrans

/-- Even natural transformation with literal `homParityShiftDatum` comparison. -/
def homContentPostEvenInvPosColumn (hh : 0 ≤ D.h i nuM) (n : ℕ) :=
  (IsSupernatural.shiftSource (homContentPostInvPos_column_supernatural T W i betaP muP h h₂ hh n)).toNatTrans

/-- Even natural transformation with literal `homParityShiftDatum` comparison. -/
def homContentPostEvenInvNegPrincipal (hh : D.h i nuM ≤ 0) :=
  (IsSupernatural.shiftTarget (homContentPostInvNeg_principal_supernatural T W i betaP muP h h₂ hh)).toNatTrans

/-- Even natural transformation with literal `homParityShiftDatum` comparison. -/
def homContentPostEvenInvNegRow (hh : D.h i nuM ≤ 0) (n : ℕ) :=
  (IsSupernatural.shiftTarget (homContentPostInvNeg_row_supernatural T W i betaP muP h h₂ hh n)).toNatTrans

/-- Literal-Π even natural transformations satisfy every augmented inverse product. -/
theorem homContentPostEvenInvPos_products (hh : 0 ≤ D.h i nuM) :
    let f := homContentPostEvenMateTo T W i betaP muP h h₂
    let g := homContentPostEvenCap T W i betaP muP h
    let j := homContentPostEvenInvPosPrincipal T W i betaP muP h h₂ hh
    let a := homContentPostEvenInvPosColumn T W i betaP muP h h₂ hh
    (f ≫ j + ∑ n ∈ Finset.range (D.h i nuM).toNat, g n ≫ a n = 𝟙 _) ∧
    (j ≫ f = 𝟙 _) ∧
    (∀ n, n < (D.h i nuM).toNat → j ≫ g n = 0) ∧
    (∀ n, n < (D.h i nuM).toNat → a n ≫ f = 0) ∧
    (∀ n, n < (D.h i nuM).toNat → a n ≫ g n = 𝟙 _) ∧
    (∀ n m, n < (D.h i nuM).toNat → m < (D.h i nuM).toNat → n ≠ m → a n ≫ g m = 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply NatTrans.ext
    funext Z
    simp only [NatTrans.comp_app, NatTrans.app_add, NatTrans.app_sum, NatTrans.id_app]
    exact (homContentPostInvPos_even T W i betaP muP h h₂ hh Z).2.2.2.2.1
  · apply NatTrans.ext
    funext Z
    simp only [NatTrans.comp_app, NatTrans.id_app]
    exact (homContentPostInvPos_even T W i betaP muP h h₂ hh Z).2.2.2.2.2.1
  · intro n hn
    apply NatTrans.ext
    funext Z
    simp only [NatTrans.comp_app, NatTrans.app_zero]
    exact (homContentPostInvPos_even T W i betaP muP h h₂ hh Z).2.2.2.2.2.2.1 n hn
  · intro n hn
    apply NatTrans.ext
    funext Z
    simp only [NatTrans.comp_app, NatTrans.app_zero]
    exact (homContentPostInvPos_even T W i betaP muP h h₂ hh Z).2.2.2.2.2.2.2.1 n hn
  · intro n hn
    apply NatTrans.ext
    funext Z
    simp only [NatTrans.comp_app, NatTrans.id_app]
    exact (homContentPostInvPos_even T W i betaP muP h h₂ hh Z).2.2.2.2.2.2.2.2.1 n hn
  · intro n m hn hm hnm
    apply NatTrans.ext
    funext Z
    simp only [NatTrans.comp_app, NatTrans.app_zero]
    exact (homContentPostInvPos_even T W i betaP muP h h₂ hh Z).2.2.2.2.2.2.2.2.2 n m hn hm hnm

/-- Literal-Π even natural transformations satisfy every augmented inverse product. -/
theorem homContentPostEvenInvNeg_products (hh : D.h i nuM ≤ 0) :
    let f := homContentPostEvenMateFrom T W i betaP muP h h₂
    let g := homContentPostEvenCup T W i betaP muP h₂
    let j := homContentPostEvenInvNegPrincipal T W i betaP muP h h₂ hh
    let a := homContentPostEvenInvNegRow T W i betaP muP h h₂ hh
    (j ≫ f + ∑ n ∈ Finset.range (-D.h i nuM).toNat, a n ≫ g n = 𝟙 _) ∧
    (f ≫ j = 𝟙 _) ∧
    (∀ n, n < (-D.h i nuM).toNat → f ≫ a n = 0) ∧
    (∀ n, n < (-D.h i nuM).toNat → g n ≫ j = 0) ∧
    (∀ n, n < (-D.h i nuM).toNat → g n ≫ a n = 𝟙 _) ∧
    (∀ n m, n < (-D.h i nuM).toNat → m < (-D.h i nuM).toNat → n ≠ m → g n ≫ a m = 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply NatTrans.ext
    funext Z
    simp only [NatTrans.comp_app, NatTrans.app_add, NatTrans.app_sum, NatTrans.id_app]
    exact (homContentPostInvNeg_even T W i betaP muP h h₂ hh Z).2.2.2.2.1
  · apply NatTrans.ext
    funext Z
    simp only [NatTrans.comp_app, NatTrans.id_app]
    exact (homContentPostInvNeg_even T W i betaP muP h h₂ hh Z).2.2.2.2.2.1
  · intro n hn
    apply NatTrans.ext
    funext Z
    simp only [NatTrans.comp_app, NatTrans.app_zero]
    exact (homContentPostInvNeg_even T W i betaP muP h h₂ hh Z).2.2.2.2.2.2.1 n hn
  · intro n hn
    apply NatTrans.ext
    funext Z
    simp only [NatTrans.comp_app, NatTrans.app_zero]
    exact (homContentPostInvNeg_even T W i betaP muP h h₂ hh Z).2.2.2.2.2.2.2.1 n hn
  · intro n hn
    apply NatTrans.ext
    funext Z
    simp only [NatTrans.comp_app, NatTrans.id_app]
    exact (homContentPostInvNeg_even T W i betaP muP h h₂ hh Z).2.2.2.2.2.2.2.2.1 n hn
  · intro n m hn hm hnm
    apply NatTrans.ext
    funext Z
    simp only [NatTrans.comp_app, NatTrans.app_zero]
    exact (homContentPostInvNeg_even T W i betaP muP h h₂ hh Z).2.2.2.2.2.2.2.2.2 n m hn hm hnm

end OddMath.SKM

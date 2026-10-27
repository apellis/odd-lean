import OddMath.SKM.RouquierHomPreInverse
import OddMath.SKM.RouquierSupernaturalInverse

/-!
# Precomposition augmented inverses in the Hom supercategory

The normalized precomposition mate and its dotted windows from
`SwappedHomInversion.md`, §2, retain signed naturality on odd Hom maps.
The homogeneous shift removals are themselves supernatural of the
left-adjunction parity; their two contributions cancel in inverse entries.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

private theorem preParity_cancel_super (σ q : ZMod 2) : σ + (q + σ) = q := by
  fin_cases σ <;> fin_cases q <;> rfl

/-- An invertible homogeneous supernatural family has a supernatural inverse. -/
theorem isSupernatural_iso_inv {k : Type r} [CommRing k]
    {C C' : Type*} [Category C] [Category C']
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive C'] [Linear k C'] [Supercategory k C']
    {F G : C ⥤ C'} [F.Additive] [F.Linear k] [G.Additive] [G.Linear k]
    {p : ZMod 2} (a : ∀ Z, F.obj Z ≅ G.obj Z)
    (ha : IsSupernatural k p (fun Z => (a Z).hom)) :
    IsSupernatural k p (F := G) (G := F) (fun Z => (a Z).inv) where
  mem Z := inv_mem (a Z) (ha.mem Z)
  naturality := by
    intro Z Z' q f hf
    have hn := ha.naturality hf
    apply (cancel_mono (a Z').hom).mp
    simp only [Linear.smul_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn, Linear.comp_smul, smul_smul, sign_mul_self,
      one_smul, Iso.inv_hom_id_assoc]

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) (W : X → B)
  (i : I) (muM : X) {muP nuP rhoP : X}
  (h : -nuP + D.α i = -muP) (h₂ : -rhoP + D.α i = -nuP)

/-- Source shift removal, followed by the even associator, is signed natural. -/
theorem homContentPreInverseSource_supernatural :
    IsSupernatural k (leftAdjParity D i (-nuP))
      (F := homContentPreF T W i muM h ⋙ homContentPreE T W i muM h)
      (G := homPre (k := k) (c := W muM) (T.E i h ≫ T.F i h))
      (fun Z => (homContentPreInverseSource T W i muM h Z).hom) := by
  let S := (homParityShiftDatum (k := k)
    (C := homWeightSector T.obj W muP muM) (leftAdjParity D i (-nuP))).supernatural
  have hs := (S.whiskerLeft (homPre (k := k) (c := W muM) (T.F i h))).whiskerRight
    (homPre (k := k) (c := W muM) (T.E i h))
  have ha := isSupernatural_of_natTrans
    (homPreComp (k := k) (d := W muM) (T.E i h) (T.F i h)).hom
    (fun Z => inv_mem (associator (T.E i h) (T.F i h) Z)
      (TwoSupercategory.associator_hom_mem (R := k) _ _ _))
  have ht := hs.comp ha
  dsimp only [homPre, Functor.comp_obj] at ht ⊢
  simpa only [homWeightSector, add_zero, homContentPreInverseSource, Iso.trans_hom,
    Functor.mapIso_hom, homContentPreE, homContentPreF, homPre,
    homPreComp, NatIso.ofComponents, Iso.symm_hom] using ht

/-- Target shift removal has the same parity as the source, by the edge equation. -/
theorem homContentPreInverseTarget_supernatural :
    IsSupernatural k (leftAdjParity D i (-nuP))
      (F := homContentPreE T W i muM h₂ ⋙ homContentPreF T W i muM h₂)
      (G := homPre (k := k) (c := W muM) (T.F i h₂ ≫ T.E i h₂))
      (fun Z => (homContentPreInverseTarget T W i muM h₂ Z).hom) := by
  let S := (homParityShiftDatum (k := k)
    (C := homWeightSector T.obj W nuP muM) (leftAdjParity D i (-rhoP))).supernatural
  have hs := S.whiskerLeft
    (homPre (k := k) (c := W muM) (T.E i h₂) ⋙ homPre (k := k) (T.F i h₂))
  have ha := isSupernatural_of_natTrans
    (homPreComp (k := k) (d := W muM) (T.F i h₂) (T.E i h₂)).hom
    (fun Z => inv_mem (associator (T.F i h₂) (T.E i h₂) Z)
      (TwoSupercategory.associator_hom_mem (R := k) _ _ _))
  have ht := hs.comp ha
  rw [leftAdjParity_edge D i h₂]
  dsimp only [homPre, Functor.comp_obj] at ht ⊢
  simpa only [add_zero, homContentPreInverseTarget, Iso.trans_hom,
    homContentPreF, homContentPreE,
    homPreComp, NatIso.ofComponents, Iso.symm_hom] using ht

instance : (homContentPreE T W i muM h).Additive := by
  unfold homContentPreE
  infer_instance

instance : (homContentPreE T W i muM h).Linear k := by
  unfold homContentPreE
  infer_instance

instance : (homContentPreF T W i muM h).Additive := by
  unfold homContentPreF
  infer_instance

instance : (homContentPreF T W i muM h).Linear k := by
  unfold homContentPreF
  infer_instance

instance : IsSuperfunctor k (homContentPreF T W i muM h) := by
  unfold homContentPreF
  infer_instance

/-- Rescaling a supernatural family by an integral coefficient preserves its parity. -/
private theorem preSupernatural_zsmul {C C' : Type*} [Category C] [Category C']
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive C'] [Linear k C'] [Supercategory k C']
    {F G : C ⥤ C'} {p : ZMod 2} {x : ∀ Z, F.obj Z ⟶ G.obj Z}
    (hx : IsSupernatural k p x) (a : ℤ) :
    IsSupernatural k p (fun Z => a • x Z) where
  mem Z := zsmul_mem (hx.mem Z) a
  naturality := by
    intro Z Z' q f hf
    calc
      F.map f ≫ (a • x Z') = a • (F.map f ≫ x Z') :=
        Preadditive.comp_zsmul _ _ _
      _ = a • (sign k (p * q) • (x Z ≫ G.map f)) := by rw [hx.naturality hf]
      _ = sign k (p * q) • (a • (x Z ≫ G.map f)) := smul_comm _ _ _
      _ = sign k (p * q) • ((a • x Z) ≫ G.map f) := by
        rw [Preadditive.zsmul_comp]

/-- A homogeneous factor map, transported through both normalized pre-Hom
coordinates, has the original parity: the two shift signs cancel. -/
theorem homContentPre_coordinates_supernatural
    {q : ZMod 2} {x : T.F i h₂ ≫ T.E i h₂ ⟶ T.E i h ≫ T.F i h}
    (hx : x ∈ parity (R := k) _ _ q) (a : ℤ) :
    IsSupernatural k q
      (F := homContentPreE T W i muM h₂ ⋙ homContentPreF T W i muM h₂)
      (G := homContentPreF T W i muM h ⋙ homContentPreE T W i muM h)
      (fun Z => a • ((homContentPreInverseTarget T W i muM h₂ Z).hom ≫
        x ▷ Z ≫ (homContentPreInverseSource T W i muM h Z).inv)) := by
  have hs := homContentPreInverseSource_supernatural T W i muM h
  have ht := homContentPreInverseTarget_supernatural T W i muM h₂
  have hi := isSupernatural_iso_inv
    (F := homContentPreF T W i muM h ⋙ homContentPreE T W i muM h)
    (G := homPre (k := k) (c := W muM) (T.E i h ≫ T.F i h))
    (fun Z : homWeightSector T.obj W nuP muM =>
      homContentPreInverseSource T W i muM h Z) hs
  have hm := (homPreTransform (k := k) (c := W muM) x hx).isSupernatural q
  have hc := (ht.comp hm).comp hi
  rw [add_assoc, preParity_cancel_super] at hc
  simpa only [homPreTransform, ite_true, Category.assoc] using
    preSupernatural_zsmul hc a

/-- The prescribed normalized mate is signed-natural on odd Hom morphisms. -/
theorem homContentPreMate_supernatural :
    IsSupernatural k (D.parity i)
      (F := homContentPreF T W i muM h ⋙ homContentPreE T W i muM h)
      (G := homContentPreE T W i muM h₂ ⋙ homContentPreF T W i muM h₂)
      (homContentPreMate T W i muM h h₂) :=
  (rouquierMate (homContentSuperAdjunction T W i muM h)
    (homContentSuperAdjunction T W i muM h₂)
    (homContentCrossing T W i muM h h₂)).isSupernatural (D.parity i)

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- Every raw dot power is signed-natural on the entire Hom supercategory. -/
theorem homReservoirDot_power_supernatural (n : ℕ) :
    IsSupernatural k (n * D.parity i)
      (F := homContentPreE T W i muM h)
      (G := homContentPreE T W i muM h)
      (fun Z => homReservoirDot T W i muM h Z ^ n) := by
  have ht := (homPreTransform (k := k) (c := W muM)
    (rouquierPower (T.dot i h) n) (rouquierPower_mem (T.dot_mem i h) n)).isSupernatural
      (n * D.parity i)
  simpa only [homReservoirDot, whiskerRight_rouquierPower (k := k),
    homContentPreE, homPreTransform, ite_true] using ht

/-- Dotted normalized unit at every power, including odd powers. -/
theorem homReservoirCup_supernatural (n : ℕ) :
    IsSupernatural k (n * D.parity i)
      (F := 𝟭 (homWeightSector T.obj W muP muM))
      (G := homContentPreE T W i muM h ⋙ homContentPreF T W i muM h)
      (homReservoirCup T W i muM h n) := by
  have hc := isSupernatural_of_natTrans
    (homContentPreAdjunction T W T.leftAdjoints i muM h).unit
    (homContentPreAdjunction_unit_mem T W i muM h)
  have hd := (homReservoirDot_power_supernatural T W i muM h n).whiskerRight
    (homContentPreF T W i muM h)
  have ht := hc.comp hd
  rw [zero_add] at ht
  exact ht

/-- Dotted normalized counit at every power, including odd powers. -/
theorem homReservoirCap_supernatural (n : ℕ) :
    IsSupernatural k (n * D.parity i)
      (F := homContentPreF T W i muM h ⋙ homContentPreE T W i muM h)
      (G := 𝟭 (homWeightSector T.obj W nuP muM))
      (homReservoirCap T W i muM h n) := by
  have hd := (homReservoirDot_power_supernatural T W i muM h n).whiskerLeft
    (homContentPreF T W i muM h)
  have hc := isSupernatural_of_natTrans
    (homContentPreAdjunction T W T.leftAdjoints i muM h).counit
    (homContentPreAdjunction_counit_mem T W i muM h)
  have ht := hd.comp hc
  rw [add_zero] at ht
  exact ht

/-- Both principal inverse orientations retain gamma and odd signed naturality. -/
theorem homContentPreInvNeg_principal_supernatural (hh : 0 ≤ D.h i (-nuP)) :
    IsSupernatural k (D.parity i)
      (F := homContentPreE T W i muM h₂ ⋙ homContentPreF T W i muM h₂)
      (G := homContentPreF T W i muM h ⋙ homContentPreE T W i muM h)
      (fun Z => (homContentPreInvNeg T W i muM h h₂ hh Z).f') := by
  have ht := homContentPre_coordinates_supernatural T W i muM h h₂
    ((T.loc i h₂ h).leftWindowInvFrom hh).f'_mem
    (homPreGamma (D.parity i) (D.h i (-nuP)))
  simpa only [homContentPreInvNeg_principal, SuperRouquierLoc.leftWindowInvFrom] using ht

theorem homContentPreInvPos_principal_supernatural (hh : D.h i (-nuP) ≤ 0) :
    IsSupernatural k (D.parity i)
      (F := homContentPreE T W i muM h₂ ⋙ homContentPreF T W i muM h₂)
      (G := homContentPreF T W i muM h ⋙ homContentPreE T W i muM h)
      (fun Z => (homContentPreInvPos T W i muM h h₂ hh Z).f') := by
  have ht := homContentPre_coordinates_supernatural T W i muM h h₂
    ((T.loc i h₂ h).leftWindowInvTo hh).f'_mem
    (homPreGamma (D.parity i) (D.h i (-nuP)))
  simpa only [homContentPreInvPos_principal, SuperRouquierLoc.leftWindowInvTo] using ht

/-- Inverse cup row: the raw parity includes the left-adjunction parity. -/
theorem homContentPreInvNeg_row_supernatural (hh : 0 ≤ D.h i (-nuP)) (n : ℕ) :
    IsSupernatural k (n * D.parity i)
      (F := homContentPreE T W i muM h₂ ⋙ homContentPreF T W i muM h₂)
      (G := 𝟭 (homWeightSector T.obj W nuP muM))
      (fun Z => (homContentPreInvNeg T W i muM h h₂ hh Z).g' n) := by
  have hx := ((T.loc i h₂ h).leftWindowInvFrom hh).g'_mem n
  have hp : D.parity i * ((D.h i (-nuP) : ZMod 2) + 1) + n * D.parity i =
      leftAdjParity D i (-nuP) + n * D.parity i := rfl
  rw [hp] at hx
  have hm := (homPreTransform (k := k) (c := W muM)
    ((T.loc i h₂ h).leftWindowCupRowNat n) hx).isSupernatural
    (leftAdjParity D i (-nuP) + n * D.parity i)
  have ht := homContentPreInverseTarget_supernatural T W i muM h₂
  have hu := isSupernatural_of_natTrans
    (homPreId (k := k) (T.obj (-nuP)) (W muM)).hom
    (fun Z => TwoSupercategory.leftUnitor_hom_mem (R := k) Z)
  have hc := (ht.comp hm).comp hu
  rw [← add_assoc, zmod2_add_self, zero_add, add_zero] at hc
  simpa only [homContentPreInvNeg_row, homPreTransform, ite_true,
    homPreId, NatIso.ofComponents, Category.assoc] using
    preSupernatural_zsmul hc
      (koszulSign (leftAdjParity D i (-nuP)) (n * D.parity i))

/-- Inverse cap column, including the source-height beta normalization. -/
theorem homContentPreInvPos_column_supernatural (hh : D.h i (-nuP) ≤ 0) (n : ℕ) :
    IsSupernatural k (n * D.parity i)
      (F := 𝟭 (homWeightSector T.obj W nuP muM))
      (G := homContentPreF T W i muM h ⋙ homContentPreE T W i muM h)
      (fun Z => (homContentPreInvPos T W i muM h h₂ hh Z).g' n) := by
  have hx := ((T.loc i h₂ h).leftWindowInvTo hh).g'_mem n
  have hp : D.parity i * ((D.h i (-nuP) : ZMod 2) + 1) + n * D.parity i =
      leftAdjParity D i (-nuP) + n * D.parity i := rfl
  rw [hp] at hx
  have hm := (homPreTransform (k := k) (c := W muM)
    ((T.loc i h₂ h).leftWindowCapColumnNat n) hx).isSupernatural
    (leftAdjParity D i (-nuP) + n * D.parity i)
  have hu := isSupernatural_of_natTrans
    (homPreId (k := k) (T.obj (-nuP)) (W muM)).inv
    (fun Z => inv_mem (leftUnitor Z)
      (TwoSupercategory.leftUnitor_hom_mem (R := k) Z))
  have hs := homContentPreInverseSource_supernatural T W i muM h
  have hi := isSupernatural_iso_inv
    (F := homContentPreF T W i muM h ⋙ homContentPreE T W i muM h)
    (G := homPre (k := k) (c := W muM) (T.E i h ≫ T.F i h))
    (fun Z : homWeightSector T.obj W nuP muM =>
      homContentPreInverseSource T W i muM h Z) hs
  have hc := (hu.comp hm).comp hi
  rw [zero_add, add_assoc, preParity_cancel_super] at hc
  simpa only [homContentPreInvPos_column, homPreTransform, ite_true,
    homPreId, NatIso.ofComponents, Iso.symm_hom, Category.assoc] using
    preSupernatural_zsmul hc
      (homPreBeta (D.parity i) (leftAdjParity D i (-nuP)) (D.h i (-nuP)) n)

/-- The specified mate as a homogeneous transformation on the full Hom space. -/
def homContentPreSuperMate :
    homContentSuperF T W i muM h ≫ homContentSuperE T W i muM h ⟶
      homContentSuperE T W i muM h₂ ≫ homContentSuperF T W i muM h₂ :=
  (homContentPreMate_supernatural T W i muM h h₂).toSuperNatTrans

/-- The bundled mate is the actual cup–crossing–cap mate. -/
theorem homContentPreSuperMate_eq : homContentPreSuperMate T W i muM h h₂ =
    rouquierMate (homContentSuperAdjunction T W i muM h)
      (homContentSuperAdjunction T W i muM h₂)
      (homContentCrossing T W i muM h h₂) := by
  have hm := rouquierMate_homogeneous
    (homContentSuperAdjunction T W i muM h)
    (homContentSuperAdjunction T W i muM h₂)
    (homContentCrossing_mem T W i muM h h₂)
  apply Superfunctor.hom_ext
  intro q Z
  change (if q = D.parity i then _ else 0) = _
  by_cases hq : q = D.parity i
  · subst q; rw [ite_eq_left rfl]; rfl
  · rw [ite_eq_right hq]
    exact (Superfunctor.app_eq_zero_of_mem hm hq Z).symm

/-- Dotted normalized unit on the full Hom supercategory. -/
def homContentPreSuperCup (n : ℕ) :
    𝟙 (SCat.of k (homWeightSector T.obj W muP muM)) ⟶
      homContentSuperE T W i muM h ≫ homContentSuperF T W i muM h :=
  (homReservoirCup_supernatural T W i muM h n).toSuperNatTrans

/-- Dotted normalized counit on the full Hom supercategory. -/
def homContentPreSuperCap (n : ℕ) :
    homContentSuperF T W i muM h ≫ homContentSuperE T W i muM h ⟶
      𝟙 (SCat.of k (homWeightSector T.obj W nuP muM)) :=
  (homReservoirCap_supernatural T W i muM h n).toSuperNatTrans

/-- All five nonpositive-Hom-height augmented inverse identities. -/
def homContentPreSuperInvNeg (hh : 0 ≤ D.h i (-nuP)) :
    SuperSumInvFrom (k := k) (homContentPreSuperMate T W i muM h h₂)
      (homContentPreSuperCup T W i muM h₂)
      (D.parity i) (fun n => n * D.parity i) (D.h i (-nuP)).toNat :=
  SuperSumInvFrom.supernatural (homContentPreInvNeg T W i muM h h₂ hh)
    (homContentPreMate_supernatural T W i muM h h₂)
    (homReservoirCup_supernatural T W i muM h₂)
    (homContentPreInvNeg_principal_supernatural T W i muM h h₂ hh)
    (homContentPreInvNeg_row_supernatural T W i muM h h₂ hh)

/-- All five nonnegative-Hom-height augmented inverse identities. -/
def homContentPreSuperInvPos (hh : D.h i (-nuP) ≤ 0) :
    SuperSumInvTo (k := k) (homContentPreSuperMate T W i muM h h₂)
      (homContentPreSuperCap T W i muM h)
      (D.parity i) (fun n => n * D.parity i) (-D.h i (-nuP)).toNat :=
  SuperSumInvTo.supernatural (homContentPreInvPos T W i muM h h₂ hh)
    (homContentPreMate_supernatural T W i muM h h₂)
    (homReservoirCap_supernatural T W i muM h)
    (homContentPreInvPos_principal_supernatural T W i muM h h₂ hh)
    (homContentPreInvPos_column_supernatural T W i muM h h₂ hh)

/-- Both empty-window inverses agree as supernatural transformations. -/
theorem homContentPreSuperInv_zero (hh : D.h i (-nuP) = 0) :
    (homContentPreSuperInvPos T W i muM h h₂ (le_of_eq hh)).f' =
      (homContentPreSuperInvNeg T W i muM h h₂ (le_of_eq hh.symm)).f' := by
  apply Superfunctor.hom_ext
  intro q Z
  change (if q = D.parity i then _ else 0) = (if q = D.parity i then _ else 0)
  rw [homContentPreInv_zero T W i muM h h₂ hh Z]

end OddMath.SKM

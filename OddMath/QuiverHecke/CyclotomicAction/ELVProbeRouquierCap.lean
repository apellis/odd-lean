import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapUniqueness
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapPreDotSigns
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction
import OddMath.SKM.RouquierAdjacentLeftAdjunction

/-! # Comparing the inverse-defined Rouquier cap with the regular probe row

The existing left-adjunction route uses adjacent local Rouquier inverses,
not a separate Frobenius construction. At negative height the raw left cap
is an inverse row; its unit window forces its component at the regular
probe to be the specified native cap. The normalized counit additionally
retains the exact fixed scalar from `RouquierFTriangle`.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem power_total
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u+1} k}
    {F : A ⟶ B} (d : End F) (n : ℕ) (M : A) :
    (SKM.rouquierPower d n).total M = (show End (F.obj M) from d.total M) ^ n := by
  induction n with
  | zero => exact SuperNatTrans.id_total F.toFunctor M
  | succ n ih =>
    rw [SKM.rouquierPower, Superfunctor.comp_total, ih, pow_succ', End.mul_def]

private theorem whisker_total
    {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (η : F ⟶ G) (H : B ⟶ R) (M : A) :
    (η ▷ H).total M = H.map (η.total M) := by
  change H.map (η.app 0 M) + H.map (η.app 1 M) = H.map (η.app 0 M + η.app 1 M)
  exact (Functor.map_add H.toFunctor).symm

private theorem evenNat_total
    {k : Type u} [CommRing k] {C R : Type*} [Category C] [Category R]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R]
    (F G : C ⥤ R) [F.Additive] [F.Linear k] [G.Additive] [G.Linear k]
    (η : F ⟶ G) (hη : ∀ M, η.app M ∈ parity (R := k) _ _ 0) (M : C) :
    (SuperNatTrans.ofNatTrans η hη).total M = η.app M := by
  simp [SuperNatTrans.total, SuperNatTrans.ofNatTrans]

private theorem raw_component_window
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F : Superfunctor k (Superfunctor k C (SVec k)) (Superfunctor k C (SVec k))}
    (a : Superfunctor.id k (Superfunctor k C (SVec k)) ⟶ F)
    (b : F ⟶ Superfunctor.id k (Superfunctor k C (SVec k)))
    (q : Prop) [Decidable q]
    (h : a ≫ b = if q then 𝟙 (Superfunctor.id k (Superfunctor k C (SVec k))) else 0)
    (M : Superfunctor k C (SVec k)) :
    a.total M ≫ b.total M = if q then 𝟙 M else 0 := by
  have hh := congrArg (fun η : Superfunctor.id k (Superfunctor k C (SVec k)) ⟶
    Superfunctor.id k (Superfunctor k C (SVec k)) => η.total M) h
  rw [Superfunctor.comp_total] at hh
  by_cases hq : q
  · rw [ite_eq_left hq] at hh ⊢
    exact hh.trans (SuperNatTrans.id_total (𝟭 (Superfunctor k C (SVec k))) M)
  · rw [ite_eq_right hq] at hh ⊢
    simpa only [SuperNatTrans.total, Superfunctor.zero_app, zero_add] using hh

private theorem native_total_zsmul
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k (Superfunctor k C (SVec k)) (Superfunctor k C (SVec k))}
    (η : F ⟶ G) (z : ℤ) (M : Superfunctor k C (SVec k)) :
    (z • η).total M = z • η.total M := by
  change z • η.app 0 M + z • η.app 1 M = z • (η.app 0 M + η.app 1 M)
  exact (smul_add _ _ _).symm

private theorem negative_parity (p : ZMod 2) (P : ℕ) (hP : 0 < P) :
    p * (((-(P : ℤ)) : ZMod 2) + 1) = (P - 1) • p := by
  rw [Int.cast_natCast, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ P), Nat.cast_one]
  generalize (P : ZMod 2) = q
  fin_cases p <;> fin_cases q <;> decide

private theorem map_signed_cap {C R : Type*} [Category C] [Category R]
    [Preadditive C] [Preadditive R] (H : C ⥤ R) [H.Additive]
    {S M : C} {Z : R} (e : Z ≅ H.obj S) (f v : S ⟶ M) (q : ZMod 2)
    (hf : f = koszulSign q q • v) :
    koszulSign q q • (e.hom ≫ H.map f) = e.hom ≫ H.map v := by
  rw [hf, Functor.map_zsmul, Preadditive.comp_zsmul, smul_smul, koszulSign_mul_self, one_smul]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []

/-- The existing ordinary right adjunction on the chosen native probe edge. -/
def appendRightAdjunction (i : I) :
    SKM.SuperAdjunction (k := k) (inductionCell D Sc m i) (restrictionCell D Sc m i) :=
  ordinaryEvenSuperAdjunction (inductionCell D Sc m i) (restrictionCell D Sc m i)
    (adjunction (K i)) (adjunctionUnit_mem (K i)) (adjunctionCounit_mem (K i))

/-- Its unit and actual dot powers evaluate to the prescribed module
unit columns, before any local inverse is chosen. -/
theorem appendRightUnitPower_total (i : I) (a : ℕ) :
    ((appendRightAdjunction D Sc m i).unit ≫
      SKM.rouquierPower (inductionDotCell D Sc m i) a ▷ restrictionCell D Sc m i).total N =
      unitDotColumn (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N a := by
  rw [Superfunctor.comp_total, whisker_total, power_total, inductionDotCell_total]
  have hu : (appendRightAdjunction D Sc m i).unit.total N = (adjunction (K i)).unit.app N :=
    evenNat_total _ _ (adjunction (K i)).unit (adjunctionUnit_mem (K i)) N
  rw [hu]
  rfl

section Local
variable (i : I)
  {A : PiSCat.{u,u,u+1} k}
  {E₀ : A ⟶ modulePiCategory D Sc m} {F₀ : modulePiCategory D Sc m ⟶ A}
  (A₀ : SKM.SuperAdjunction (k := k) E₀ F₀) (x₀ : End E₀)
  (t : End (E₀ ≫ inductionCell D Sc m i))
  (L : SKM.SuperRouquierLoc A₀ (appendRightAdjunction D Sc m i)
    x₀ (inductionDotCell D Sc m i) t (D.parity i) (-((probeCutoff D m i : ℕ) : ℤ)))

include L in
/-- The raw inverse-defined local cap, on native module-functor endpoints
before any regular-probe component is substituted. -/
def localCapFamily :
    (show Superfunctor k (Superfunctor k (OldContentCategory D Sc cut []) (SVec k))
      (Superfunctor k (OldContentCategory D Sc cut []) (SVec k)) from
        ⟨induction (K i) ⋙ restriction (K i)⟩) ⟶
      Superfunctor.id k (Superfunctor k (OldContentCategory D Sc cut []) (SVec k)) := L.capL

include L in
private def localCupFamily (a : ℕ) :
    Superfunctor.id k (Superfunctor k (OldContentCategory D Sc cut []) (SVec k)) ⟶
      (show Superfunctor k (Superfunctor k (OldContentCategory D Sc cut []) (SVec k))
        (Superfunctor k (OldContentCategory D Sc cut []) (SVec k)) from
          ⟨induction (K i) ⋙ restriction (K i)⟩) := L.cupD a

/-- The existing raw local left cap has exactly the prescribed native
regular-probe component. The local Rouquier record supplies its inverse
window; no cap-compatibility or triangle premise is added. -/
theorem local_capL_total (hP : 0 < cut i) :
    (localCapFamily D Sc m i A₀ x₀ t L).total N = cap D Sc m i hP := by
  classical
  apply cap_eq_of_unitDot_window D Sc m i hP
  intro a ha
  have hh : -(cut i : ℤ) < 0 := by omega
  have ha' : a < (- (-(cut i : ℤ))).toNat := by simpa using ha
  have hraw : (localCupFamily D Sc m i A₀ x₀ t L a) ≫ (localCapFamily D Sc m i A₀ x₀ t L) =
      if a = (- (-(cut i : ℤ)) - 1).toNat then
        𝟙 (Superfunctor.id k (Superfunctor k (OldContentCategory D Sc cut []) (SVec k))) else 0 :=
    L.cupD_capL hh ha'
  have h := raw_component_window _ _ _ hraw N
  have hu : (localCupFamily D Sc m i A₀ x₀ t L a).total N =
      unitDotColumn (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N a :=
    appendRightUnitPower_total D Sc m i a
  rw [hu] at h
  have he : a = (- (-(cut i : ℤ)) - 1).toNat ↔ a + 1 = cut i := by omega
  simpa only [he] using h
section Adjacent
variable {Z : PiSCat.{u,u,u+1} k}
  {E₃ : raisedModulePiCategory D Sc m i ⟶ Z} {F₃ : Z ⟶ raisedModulePiCategory D Sc m i}
  (A₃ : SKM.SuperAdjunction (k := k) E₃ F₃) (x₃ : End E₃)
  (t' : End (inductionCell D Sc m i ≫ E₃))
  (U : SKM.SuperRouquierLoc (appendRightAdjunction D Sc m i) A₃
    (inductionDotCell D Sc m i) x₃ t' (D.parity i) (-((probeCutoff D m i : ℕ) : ℤ) + 2))
  (hP : 0 < probeCutoff D m i) (hsq : t ≫ t = 0) (hsq' : t' ≫ t' = 0)
  (hB : E₀ ◁ t' ≫ ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
      (associator E₀ (inductionCell D Sc m i) E₃).hom) ≫ E₀ ◁ t' =
    ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
      (associator E₀ (inductionCell D Sc m i) E₃).hom) ≫ E₀ ◁ t' ≫
      ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
        (associator E₀ (inductionCell D Sc m i) E₃).hom))

/-- The counit of the existing finite-local left-adjunction construction,
on native functor endpoints before evaluating the probe. -/
def localLeftCounitFamily :
    (show Superfunctor k (Superfunctor k (OldContentCategory D Sc cut []) (SVec k))
      (Superfunctor k (OldContentCategory D Sc cut []) (SVec k)) from
        ⟨induction (K i) ⋙ restriction (K i)⟩) ⟶
      Superfunctor.id k (Superfunctor k (OldContentCategory D Sc cut []) (SVec k)) :=
  (L.negativeLeftAdjunction U (by omega) hsq hsq' hB).counit

/-- The native normalized counit keeps `c(h)⁻¹=(-1)^σ` on the inverse row.
This is the actual chosen normalization, not a reallocation to the unit. -/
theorem localLeftCounit_total :
    (localLeftCounitFamily D Sc m i A₀ x₀ t L A₃ x₃ t' U hP hsq hsq' hB).total N =
      koszulSign ((cut i - 1) • D.parity i) ((cut i - 1) • D.parity i) • cap D Sc m i hP := by
  have he : localLeftCounitFamily D Sc m i A₀ x₀ t L A₃ x₃ t' U hP hsq hsq' hB =
      koszulSign (D.parity i * (((-(cut i : ℤ)) : ZMod 2) + 1))
        (D.parity i * (((-(cut i : ℤ)) : ZMod 2) + 1)) •
        localCapFamily D Sc m i A₀ x₀ t L := by
    apply Superfunctor.hom_ext
    intro q V
    dsimp only [localLeftCounitFamily, SKM.SuperRouquierLoc.negativeLeftAdjunction, localCapFamily]
    rw [Int.cast_neg]
  rw [he, native_total_zsmul, local_capL_total D Sc m i A₀ x₀ t L hP,
    negative_parity (D.parity i) (cut i) hP]

/-- The second diagonal Koszul factor in the prescribed pre-Hom counit
cancels the native normalization at negative height. -/
theorem localLeftCounit_preSign_total :
    koszulSign ((cut i - 1) • D.parity i) ((cut i - 1) • D.parity i) •
      (localLeftCounitFamily D Sc m i A₀ x₀ t L A₃ x₃ t' U hP hsq hsq' hB).total N =
      cap D Sc m i hP := by
  rw [localLeftCounit_total]
  exact koszulSign_smul_smul _ _ _

/-- On the chosen source-parity coordinates, the prescribed pre-Hom
counit component has its second diagonal Koszul factor. The fixed native
normalization cancels it, giving precisely the previously constructed cap
on this Hom carrier; the unit normalization is unchanged. -/
theorem localLeftCounit_preCap_eq (R : PiSCat.{u,u,u+1} k)
    (H : modulePiCategory D Sc m ⟶ R) :
    koszulSign ((cut i - 1) • D.parity i) ((cut i - 1) • D.parity i) •
      ((preSourceComponent D Sc m R i H).hom ≫ H.map
        ((localLeftCounitFamily D Sc m i A₀ x₀ t L A₃ x₃ t' U hP hsq hsq' hB).total N)) =
      shiftedPreCap D Sc m R i hP H := by
  have h := map_signed_cap (C := modulePiCategory D Sc m) (R := R) H.toFunctor
    (S := source D Sc m i) (M := N) (preSourceComponent D Sc m R i H)
    ((localLeftCounitFamily D Sc m i A₀ x₀ t L A₃ x₃ t' U hP hsq hsq' hB).total N)
    (cap D Sc m i hP) ((cut i - 1) • D.parity i)
    (localLeftCounit_total D Sc m i A₀ x₀ t L A₃ x₃ t' U hP hsq hsq' hB)
  exact h.trans (shiftedPreCap_eq D Sc m R i hP H).symm
end Adjacent

end Local

end OddMath.QuiverHecke.ELVOld.ProbeVacuumCap

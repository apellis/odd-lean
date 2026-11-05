import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightPreDot
import Mathlib.RingTheory.Nilpotent.Basic
import OddMath.SKM.RouquierHomPreNegativePowers
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvenVacuumPolynomial

/-! # The actual negative pre-cap at the regular probe

SwappedActionAssembly F2 and SwappedHomInversion §3 (4): evaluate the
chosen raw pre-dot inverse powers before the chosen normalized counit.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open CyclotomicAction
universe u
local instance negativeCapHomPi {k : Type u} [CommRing k] (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

private def totalEvaluation {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A] (N : C) :
    Superfunctor k C A ⥤ A where
  obj F := F.obj N
  map f := f.total N
  map_id F := SuperNatTrans.id_total F.toFunctor N
  map_comp f g := Superfunctor.comp_total f g N

private theorem total_pow {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F : Superfunctor k C A} (f : End F) (n : ℕ) (N : C) :
    (f ^ n).total N = ((totalEvaluation N).mapEnd F f) ^ n :=
  map_pow ((totalEvaluation N).mapEnd F) f n

private theorem inverse_power_square {C : Type*} [Category C] [Preadditive C]
    {A B : C} (a : A ≅ A) (e : A ≅ B) (xi : End A) (hxi : xi = a.inv)
    (y : End B) (hy : IsUnit y) (h : a.hom ≫ e.hom = e.hom ≫ y) (n : ℕ) :
    (xi ^ n) ≫ e.hom = e.hom ≫ Ring.inverse y ^ n := by
  have hi : xi ≫ e.hom = e.hom ≫ Ring.inverse (M₀ := End B) y := by
    obtain ⟨v, rfl⟩ := hy
    let b : B ≅ B := {
      hom := (v : End B)
      inv := ((v⁻¹ : (End B)ˣ) : End B)
      hom_inv_id := v.inv_val
      inv_hom_id := v.val_inv }
    have hh := congrArg (fun f => a.inv ≫ f ≫ b.inv) h
    rw [hxi, Ring.inverse_unit]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc,
      show (v : End B) = b.hom from rfl, Iso.hom_inv_id, Category.comp_id] using hh.symm
  induction n with
  | zero => simp only [pow_zero, End.one_def, Category.id_comp, Category.comp_id]
  | succ n ih =>
    rw [pow_succ', pow_succ', End.mul_def, End.mul_def, Category.assoc,
      hi, ← Category.assoc, ih, Category.assoc]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ) (Λ : X)
  (hc : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)
  (W : X → PiSCat.{u,u,u+1} k) (muM : X) (i : I) {muP : X}
  (h : -Λ + D.α i = -muP) (H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ W muM)
local notation "T" => probeOldRouquierFamily D Sc m Λ hc
local notation "N₀" => regularProbe D Sc m Λ
local notation "Z" => preCapInput D Sc m Λ hc W muM H
local instance rawProbeDotIso : IsIso ((T).dot i h) :=
  (isUnit_iff_isIso _).mp (probeOldRouquierFamily_dot_isUnit D Sc m Λ hc i h)

private def rawPreDotAut :
    Aut ((SKM.homContentPreE T W i muM h).obj ((SKM.homContentPreF T W i muM h).obj Z)) where
  hom := SKM.homReservoirDot T W i muM h ((SKM.homContentPreF T W i muM h).obj Z)
  inv := SKM.homPreDotInverse T W i muM h ((SKM.homContentPreF T W i muM h).obj Z)
  hom_inv_id := SKM.homPreDot_dotInverse T W i muM h _
  inv_hom_id := SKM.homPreDotInverse_dot T W i muM h _

private theorem shiftedDot_isUnit (hi : D.parity i = 1) :
    IsUnit (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H) := by
  let x := ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H
  have hn : IsNilpotent (x ^ 2 + 1) :=
    ⟨m i, ProbeVacuumCap.shiftedPreDot_odd_polynomial D Sc m (W muM) i hi H⟩
  have hu : IsUnit (x ^ 2) := by simpa only [add_sub_cancel_right] using hn.isUnit_sub_one
  exact (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp hu

/-- All inverse powers are those of the actual whole-weight raw dot.
The target is the Ring inverse of the native shifted raw pre-dot. -/
theorem vacuumPreInverseDot_source (hP : 0 < probeCutoff D m i)
    (hi : D.parity i = 1) (n : ℕ) :
    ((SKM.homPreDotInverse T W i muM h ((SKM.homContentPreF T W i muM h).obj Z)) ^ n).total N₀ ≫
      (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H) ^ n := by
  let a := (totalEvaluation N₀).mapIso (rawPreDotAut D Sc m Λ hc W muM i h H)
  let xi := (totalEvaluation N₀).mapEnd _
    (SKM.homPreDotInverse T W i muM h ((SKM.homContentPreF T W i muM h).obj Z))
  have hh := inverse_power_square a (vacuumPreSourceIso D Sc m Λ hc W muM i h H)
    xi rfl (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H)
    (shiftedDot_isUnit D Sc m W muM i H hi)
    (vacuumPreDot_source D Sc m Λ hc W muM i h H hP) n
  rw [total_pow]
  exact hh

/-- Every actual normalized negative pre-cap has the native inverse-dot
and cap coordinates. No moment or cap compatibility hypothesis is used. -/
theorem vacuumPreNegativeCap_eq (hP : 0 < probeCutoff D m i)
    (hi : D.parity i = 1) (n : ℕ) :
    (SKM.homPreNegativeCap T W i muM h n Z).total N₀ ≫
      H.map (eqToHom (emptyProbe_regular D Sc m Λ)) =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      (Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D Sc m (W muM) i hP H := by
  rw [SKM.homPreNegativeCap, Superfunctor.comp_total, Category.assoc,
    vacuumPreCounit_eq D Sc m Λ hc W muM i h H hP,
    ← Category.assoc, vacuumPreInverseDot_source D Sc m Λ hc W muM i h H hP hi n,
    Category.assoc]

/-- Even colour: all inverse powers are those of the actual whole-weight raw dot. -/
theorem vacuumPreInverseDot_source_even (hP : 0 < probeCutoff D m i)
    (hi : D.parity i = 0) (n : ℕ) :
    ((SKM.homPreDotInverse T W i muM h ((SKM.homContentPreF T W i muM h).obj Z)) ^ n).total N₀ ≫
      (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H) ^ n := by
  let a := (totalEvaluation N₀).mapIso (rawPreDotAut D Sc m Λ hc W muM i h H)
  let xi := (totalEvaluation N₀).mapEnd _
    (SKM.homPreDotInverse T W i muM h ((SKM.homContentPreF T W i muM h).obj Z))
  have hh := inverse_power_square a (vacuumPreSourceIso D Sc m Λ hc W muM i h H)
    xi rfl (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H)
    (ProbeVacuumCap.shiftedPreDot_even_isUnit D Sc m (W muM) i hi H)
    (vacuumPreDot_source D Sc m Λ hc W muM i h H hP) n
  rw [total_pow]
  exact hh

/-- Even colour: every actual normalized negative pre-cap has the native
inverse-dot and cap coordinates. No moment or cap compatibility hypothesis is used. -/
theorem vacuumPreNegativeCap_even (hP : 0 < probeCutoff D m i)
    (hi : D.parity i = 0) (n : ℕ) :
    (SKM.homPreNegativeCap T W i muM h n Z).total N₀ ≫
      H.map (eqToHom (emptyProbe_regular D Sc m Λ)) =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      (Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D Sc m (W muM) i hP H := by
  rw [SKM.homPreNegativeCap, Superfunctor.comp_total, Category.assoc,
    vacuumPreCounit_eq D Sc m Λ hc W muM i h H hP,
    ← Category.assoc, vacuumPreInverseDot_source_even D Sc m Λ hc W muM i h H hP hi n,
    Category.assoc]

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum

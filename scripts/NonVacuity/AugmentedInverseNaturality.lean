import OddMath.SKM.AugmentedInverseNaturality
import OddMath.Algebra.FiniteSuperspace
import OddMath.Algebra.HomogeneousSuperfunctorIso
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.SKM
namespace AugmentedInverseNaturalityConsumer
private def E : Superfunctor ℚ (SVec ℚ) (SVec ℚ) := ⟨𝟭 _⟩
private def P : Superfunctor ℚ (SVec ℚ) (SVec ℚ) := ⟨PiSupercategory.pi (R := ℚ)⟩
private def ZV : SVec ℚ := FiniteSuperspace.product (fun _ : Fin 0 => SVec.unit)
private instance : Subsingleton ZV.carrier where
  allEq x y := by
    funext i
    exact Fin.elim0 i
private def zeroFunctor : SVec ℚ ⥤ SVec ℚ where
  obj _ := ZV
  map _ := 0
  map_id _ := by apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _
  map_comp _ _ := by simp
private instance : zeroFunctor.Additive where
  map_add := by intros; simp [zeroFunctor]
private instance : zeroFunctor.Linear ℚ where
  map_smul := by intros; simp [zeroFunctor]
private instance : IsSuperfunctor ℚ zeroFunctor where
  map_mem _ := Submodule.zero_mem _
private def Z : Superfunctor ℚ (SVec ℚ) (SVec ℚ) := ⟨zeroFunctor⟩
private instance (V : SVec ℚ) : Subsingleton (Z.obj V).carrier := by
  change Subsingleton ZV.carrier
  infer_instance
private def f (V : SVec ℚ) : P.obj V ⟶ E.obj V := (PiSupercategory.ζ (R := ℚ) V).hom
private def fi (V : SVec ℚ) : E.obj V ⟶ P.obj V := (PiSupercategory.ζ (R := ℚ) V).inv
private theorem hf : IsSupernatural ℚ 1 f := PiSupercategory.ζ_isSupernatural (R := ℚ)
private theorem hfi : IsSupernatural ℚ 1 fi :=
  HomogeneousSuperfunctorIso.inverseSupernatural (k := ℚ) (F := P) (G := E)
    (fun V => PiSupercategory.ζ (R := ℚ) V) hf
private theorem zero_natural (L T : Superfunctor ℚ (SVec ℚ) (SVec ℚ)) (p : ZMod 2) :
    IsSupernatural ℚ p (F := L.toFunctor) (G := T.toFunctor) (fun _ => 0) where
  mem _ := Submodule.zero_mem _
  naturality _ := by simp

private def emptyFrom (V : SVec ℚ) :
    SuperSumInvFrom (k := ℚ) (f V) (fun _ => (0 : V ⟶ V)) 1 (fun n => n • (1 : ZMod 2)) 0 where
  f' := fi V
  g' _ := 0
  f_mem := PiSupercategory.ζ_hom_mem V
  g_mem _ := Submodule.zero_mem _
  f'_mem := PiSupercategory.ζ_inv_mem V
  g'_mem _ := Submodule.zero_mem _
  total := by simp only [Finset.range_zero, Finset.sum_empty, add_zero, f, fi, Iso.inv_hom_id]
  ff := (PiSupercategory.ζ (R := ℚ) V).hom_inv_id
  fg m hm := (Nat.not_lt_zero m hm).elim
  gf m hm := (Nat.not_lt_zero m hm).elim
  gg m l hm _ := (Nat.not_lt_zero m hm).elim
private def emptyTo (V : SVec ℚ) :
    SuperSumInvTo (k := ℚ) (fi V) (fun _ => (0 : V ⟶ V)) 1 (fun n => n • (1 : ZMod 2)) 0 where
  f' := f V
  g' _ := 0
  f_mem := PiSupercategory.ζ_inv_mem V
  g_mem _ := Submodule.zero_mem _
  f'_mem := PiSupercategory.ζ_hom_mem V
  g'_mem _ := Submodule.zero_mem _
  total := by simp only [Finset.range_zero, Finset.sum_empty, add_zero, f, fi, Iso.inv_hom_id]
  ff := (PiSupercategory.ζ (R := ℚ) V).hom_inv_id
  fg m hm := (Nat.not_lt_zero m hm).elim
  gf m hm := (Nat.not_lt_zero m hm).elim
  gg m l hm _ := (Nat.not_lt_zero m hm).elim

private def g (m : ℕ) (V : SVec ℚ) : P.obj V ⟶ E.obj V := if m = 0 then f V else 0
private def gi (m : ℕ) (V : SVec ℚ) : E.obj V ⟶ P.obj V := if m = 0 then fi V else 0
private theorem hg (m : ℕ) : IsSupernatural ℚ 1 (g m) := by
  unfold g
  by_cases hm : m = 0
  · simpa only [ite_eq_left hm] using hf
  · simpa only [ite_eq_right hm] using zero_natural P E 1
private theorem hgi (m : ℕ) : IsSupernatural ℚ 1 (gi m) := by
  unfold gi
  by_cases hm : m = 0
  · simpa only [ite_eq_left hm] using hfi
  · simpa only [ite_eq_right hm] using zero_natural E P 1
private def oneFrom (V : SVec ℚ) :
    SuperSumInvFrom (k := ℚ) (0 : Z.obj V ⟶ E.obj V) (fun m => g m V) 1 (fun _ => 1) 1 where
  f' := 0
  g' _ := fi V
  f_mem := Submodule.zero_mem _
  g_mem m := (hg m).mem V
  f'_mem := Submodule.zero_mem _
  g'_mem _ := PiSupercategory.ζ_inv_mem V
  total := by simp [g, f, fi]
  ff := by apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _
  fg _ _ := by simp
  gf _ _ := by simp
  gg m l hm hl := by
    have hm0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hm)
    have hl0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hl)
    subst m
    subst l
    simp only [g, f, fi, ite_true, Iso.hom_inv_id]
private def oneTo (V : SVec ℚ) :
    SuperSumInvTo (k := ℚ) (0 : E.obj V ⟶ Z.obj V) (fun m => gi m V) 1 (fun _ => 1) 1 where
  f' := 0
  g' _ := f V
  f_mem := Submodule.zero_mem _
  g_mem m := (hgi m).mem V
  f'_mem := Submodule.zero_mem _
  g'_mem _ := PiSupercategory.ζ_hom_mem V
  total := by simp [gi, f, fi]
  ff := by apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _
  fg _ _ := by simp
  gf _ _ := by simp
  gg m l hm hl := by
    have hm0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hm)
    have hl0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hl)
    subst m
    subst l
    simp only [gi, f, fi, ite_true, Iso.hom_inv_id]

private theorem identity_natural :
    IsSupernatural ℚ 0 (F := E.toFunctor) (G := E.toFunctor) (fun V => 𝟙 V) where
  mem V := id_mem V
  naturality := by
    intro X Y r h _
    change h ≫ 𝟙 Y = sign ℚ (0 * r) • ((𝟙 X) ≫ h)
    simp
private def evenFrom (V : SVec ℚ) :
    SuperSumInvFrom (k := ℚ) (𝟙 V) (fun _ => (0 : V ⟶ V)) 0 (fun _ => 0) 0 where
  f' := 𝟙 V
  g' _ := 0
  f_mem := id_mem V
  g_mem _ := Submodule.zero_mem _
  f'_mem := id_mem V
  g'_mem _ := Submodule.zero_mem _
  total := by simp
  ff := Category.id_comp _
  fg m hm := (Nat.not_lt_zero m hm).elim
  gf m hm := (Nat.not_lt_zero m hm).elim
  gg m l hm _ := (Nat.not_lt_zero m hm).elim
example := SuperSumInvFrom.ofSupernaturalComponents (F := E) (G := E) (H := E) evenFrom identity_natural (fun _ => zero_natural E E 0)

/-- Empty windows retain nonzero-degree principal inverses and their whole families. -/
example := SuperSumInvFrom.ofSupernaturalComponents emptyFrom hf (fun n => zero_natural E E (n • 1))
example := SuperSumInvTo.ofSupernaturalComponents emptyTo hfi (fun n => zero_natural E E (n • 1))
/-- Nonempty windows retain the odd auxiliary inverse and zero extension. -/
example := SuperSumInvFrom.ofSupernaturalComponents oneFrom (zero_natural Z E 1) hg
example := SuperSumInvTo.ofSupernaturalComponents oneTo (zero_natural E Z 1) hgi
example := ((SuperSumInvFrom.ofSupernaturalComponents oneFrom (zero_natural Z E 1) hg)).total
example := ((SuperSumInvTo.ofSupernaturalComponents oneTo (zero_natural E Z 1) hgi)).gg 0 0 (by decide) (by decide)
/-- The derived naturality sees a concrete odd input arrow on the one-dimensional superspace. -/
example := (SuperSumInvFrom.principal_supernatural emptyFrom hf
  (fun n => zero_natural E E (n • 1))).naturality (PiSupercategory.ζ_hom_mem (R := ℚ) SVec.unit)
example := (SuperSumInvTo.principal_supernatural emptyTo hfi
  (fun n => zero_natural E E (n • 1))).naturality (PiSupercategory.ζ_hom_mem (R := ℚ) SVec.unit)
example := (SuperSumInvFrom.row_supernatural oneFrom (zero_natural Z E 1) hg 0).naturality
  (PiSupercategory.ζ_hom_mem (R := ℚ) SVec.unit)
example := (SuperSumInvTo.column_supernatural oneTo (zero_natural E Z 1) hgi 0).naturality
  (PiSupercategory.ζ_hom_mem (R := ℚ) SVec.unit)
example := (SuperSumInvFrom.row_supernatural oneFrom (zero_natural Z E 1) hg 7).naturality
  (PiSupercategory.ζ_hom_mem (R := ℚ) SVec.unit)
example : ((oneFrom SVec.unit).zeroExtend.g' 0) (1 : ℚ) =
    (PiSupercategory.ζ (R := ℚ) SVec.unit).inv (1 : ℚ) := by
  rfl
/-- The chosen finite extension leaves a nonzero original outside row unconstrained. -/
example : (oneFrom SVec.unit).g' 7 (1 : ℚ) =
    (PiSupercategory.ζ (R := ℚ) SVec.unit).inv (1 : ℚ) := rfl
example : ((oneFrom SVec.unit).zeroExtend.g' 7) (1 : ℚ) = 0 := rfl
/-- The finite odd inverse row acts nontrivially on the one-dimensional superspace. -/
example : ((oneFrom (SVec.unit (k := ℚ))).zeroExtend.g' 0) (1 : ℚ) ≠ 0 := by
  change (PiSupercategory.ζ (R := ℚ) (SVec.unit (k := ℚ))).inv (1 : ℚ) ≠ 0
  intro h
  have he : (PiSupercategory.ζ (R := ℚ) (SVec.unit (k := ℚ))).hom
      ((PiSupercategory.ζ (R := ℚ) (SVec.unit (k := ℚ))).inv (1 : ℚ)) = (1 : ℚ) := by
    have hi := (PiSupercategory.ζ (R := ℚ) (SVec.unit (k := ℚ))).inv_hom_id
    exact congrArg (fun f => f (1 : ℚ)) hi
  rw [h] at he
  have hz := (SVec.toLinearMap (PiSupercategory.ζ (R := ℚ) (SVec.unit (k := ℚ))).hom).map_zero
  exact zero_ne_one (hz.symm.trans he)
end AugmentedInverseNaturalityConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.AugmentedInverseNaturality
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

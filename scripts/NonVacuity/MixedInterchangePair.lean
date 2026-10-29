import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.InterchangePair
import StringDiagrams.Super.DrinfeldCenterPiCounterexample

/-! Mixed interchange on the parity envelope: a nonzero odd map with unequal
outer shifts, and mixed-colour generator data with a nonzero crossing. -/
noncomputable section
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
namespace NonVacuity.MixedInterchangePair
private abbrev B := TwoEnvelope ℤ (UnitTwo ℤ)
private def o : B := ⟨UnitTwo.pt⟩
private def e (p : ZMod 2) : o ⟶ o := ⟨p, ⟨⟩⟩
private def η : e 0 ≫ e 0 ⟶ e 1 ≫ e 0 := Envelope.ofHom (1 : ℤ)
private theorem η_odd : η ∈ parity (R := ℤ) _ _ 1 := by
  rw [Envelope.mem_parity_iff]
  change (1 : ℤ) ∈ trivialGrading ℤ (0 : ZMod 2)
  simp

-- Unequal outer shifts and a nonzero odd map: the sign cannot be discarded.
example := homMixedInterchange_pair_cross (k := ℤ)
  (e 0) (e 0) (e 1) (e 0) (e 0) (e 0) 1 0 1 0 η_odd

example : η ≠ 0 := by
  intro h
  have h' := congrArg Envelope.toHom h
  change (1 : ℤ) = 0 at h'
  norm_num at h'

example : koszulSign (1 : ZMod 2) 1 * koszulSign (0 : ZMod 2) 1 = (-1 : ℤ) := by decide

private def datum : Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else 0
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun i => if i then 1 else 0
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else 0)
    split <;> simp

-- Generator data, not a factor action: the triangle uses only the crossing parity.
private def generators : RouquierData (k := ℤ) (B := B) datum where
  obj := fun _ => o
  E := fun _ {_ _} _ => e 0
  dot := fun _ {_ _} _ => 0
  dot_mem := fun _ {_ _} _ => Submodule.zero_mem _
  cross := fun i j {_ _ _ _} _ _ _ _ =>
    if datum.parity i * datum.parity j = 0 then 𝟙 _ else 0
  cross_mem := by
    intro i j a b c d h₁ h₂ h₃ h₄
    split_ifs with h
    · rw [h]; exact Supercategory.id_mem _
    · exact Submodule.zero_mem _

example := generators.cross_mixedInterchange_pair false true true (Finsupp.single true 1)
  (a₀ := 0) rfl rfl rfl (by simp [add_comm]) (e 0) (e 0)

example : generators.cross false true (a := 0) rfl rfl rfl (by simp [add_comm]) ≠ 0 := by
  intro h
  have h' := congrArg Envelope.toHom h
  change (1 : ℤ) = 0 at h'
  norm_num at h'

#print axioms OddMath.SKM.homMixedInterchange_pair_cross
#print axioms OddMath.SKM.RouquierData.cross_mixedInterchange_pair
end NonVacuity.MixedInterchangePair

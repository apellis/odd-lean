import OddMath.QuiverHecke.SwappedAssembly.ReservoirWordFunctor
import OddMath.QuiverHecke.CyclotomicAction.Global
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightModules
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierData
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordEvaluation

/-! # Chosen values of the reversed reservoir word

SwappedActionAssembly §6 and SwappedVacuumCoordinates §2: keep the exact
formal-content weight when comparing the surviving reservoir path with
the append-defined chosen E-word value. The word is reversed, while the
original weight group and all strand labels are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ReservoirWordValue
open SwappedAssembly CyclotomicAction
universe u
variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Λ : X)

omit [AddCommGroup X] in
private theorem path_content {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0, c) (0, 0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    c = SPath.wordContent l := by
  induction l generalizing c with
  | nil => cases p; rfl
  | cons a l ih =>
    cases p with
    | cons a side s hv p =>
      have ha := hl a List.mem_cons_self
      have ht : ∀ b ∈ l, b.l.1 = true := fun b hb => hl b (List.mem_cons_of_mem _ hb)
      rcases a with ⟨⟨b, i⟩, r⟩
      cases b with
      | false => cases ha
      | true =>
        have hs := SPath.side_eq_false_of_upward_probe_zero i side p ht rfl
        subst side
        change c = Finsupp.single i 1 + SPath.wordContent l
        rw [← ih p ht]
        have hle : Finsupp.single i 1 ≤ c := by
          rw [Finsupp.single_le_iff]
          exact hv
        simpa only [add_comm] using (tsub_add_cancel_of_le hle).symm

private theorem reversed_word_weight (l : List (SKM.Col I X)) :
    ReservoirWord.weight D Λ (SPath.wordContent l) =
      blockWeight D Λ ((l.map (fun a => a.l.2)).reverse : Multiset I) := by
  induction l with
  | nil => simp [ReservoirWord.weight, SPath.wordContent]
  | cons a l ih =>
    have hs : blockWeight D Λ (((a :: l).map (fun a => a.l.2)).reverse : Multiset I) =
        blockWeight D Λ ((l.map (fun a => a.l.2)).reverse : Multiset I) + D.α a.l.2 := by
      simpa only [List.map_cons, List.reverse_cons, ← Multiset.coe_add,
        Multiset.coe_singleton, add_comm] using
          (blockWeight_cons D Λ a.l.2 ((l.map (fun a => a.l.2)).reverse : Multiset I))
    rw [hs, ← ih]
    simp only [ReservoirWord.weight, SPath.wordContent, map_add, contentWeight,
      Finsupp.weight_single, one_nsmul]
    abel

private theorem path_weight (l : List (SKM.Col I X)) :
    ReservoirWord.weight D Λ (SPath.wordContent l + 0) =
      blockWeight D Λ ((l.map (fun a => a.l.2)).reverse : Multiset I) := by
  simpa only [add_zero] using reversed_word_weight D Λ l

section Modules
variable {k : Type u} [CommRing k] (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem induction_obj_heq (i : I) {x y x' y' : X}
    (hx : x = x') (hy : y = y') (h : x + D.α i = y) (h' : x' + D.α i = y')
    {M : ELVWeightProduct D Sc cutoff N Λ x} {M' : ELVWeightProduct D Sc cutoff N Λ x'}
    (hM : HEq M M') :
    HEq ((elvE D Sc cutoff N i Λ h).obj M) ((elvE D Sc cutoff N i Λ h').obj M') := by
  cases hx
  cases hy
  cases hM
  rfl

end Modules

section ChosenValue
variable {k : Type u} [CommRing k] [Fintype I]
  (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
local notation "N" => PowerWordContent.powerBound D cutoff L

/-- The actual regular-power empty-word family, at its formal-content weight. -/
def initialValue : ELVWeightProduct D Sc cutoff N Λ (ReservoirWord.weight D Λ 0) :=
  PowerWordWeight.wordFamily D Sc cutoff L Λ (ReservoirWord.weight D Λ 0) []

/-- Literal evaluation of the native reservoir word on its specified
regular-power vacuum, before the original-weight endpoint reindexing. -/
def pathValue (l : List (SKM.Col I X)) (hl : ∀ a ∈ l, a.l.1 = true) :
    ELVWeightProduct D Sc cutoff N Λ (ReservoirWord.weight D Λ (SPath.wordContent l + 0)) :=
  (ReservoirWord.word (elvRouquierData D Sc cutoff N Λ) Λ
    (SPath.reservoirPath l hl 0) hl).obj (initialValue D Λ Sc cutoff L)

/-- The same native value at the proved original weight of the reversed word. -/
def pathValueAt (l : List (SKM.Col I X)) (hl : ∀ a ∈ l, a.l.1 = true) :
    ELVWeightProduct D Sc cutoff N Λ
      (PowerWordWeight.wordWeight D Λ ((l.map (fun a => a.l.2)).reverse)) :=
  cast (congrArg (ELVWeightProduct D Sc cutoff N Λ) (path_weight D Λ l))
    (pathValue D Λ Sc cutoff L l hl)

private theorem initialValue_heq : HEq (initialValue D Λ Sc cutoff L)
    (PowerWordEvaluation.value D Sc cutoff L Λ []) := by
  rw [PowerWordEvaluation.value_nil]
  have hw : ReservoirWord.weight D Λ 0 = PowerWordWeight.wordWeight D Λ [] := by
    simp [ReservoirWord.weight, PowerWordWeight.wordWeight]
  have transport : ∀ {x y : X}, x = y → HEq
      (PowerWordWeight.wordFamily D Sc cutoff L Λ x [])
      (PowerWordWeight.wordFamily D Sc cutoff L Λ y []) := by
    intro x y h
    cases h
    rfl
  exact transport hw

private theorem value_word_heq {ν τ : List I} (h : ν = τ) :
    HEq (PowerWordEvaluation.value D Sc cutoff L Λ ν)
      (PowerWordEvaluation.value D Sc cutoff L Λ τ) := by
  cases h
  rfl

private theorem word_value_heq {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0, c) (0, 0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    HEq ((ReservoirWord.word (elvRouquierData D Sc cutoff N Λ) Λ p hl).obj
      (initialValue D Λ Sc cutoff L))
      (PowerWordEvaluation.value D Sc cutoff L Λ ((l.map (fun a => a.l.2)).reverse)) := by
  induction l generalizing c with
  | nil =>
    cases p
    rw [ReservoirWord.word_nil]
    change HEq (initialValue D Λ Sc cutoff L) (PowerWordEvaluation.value D Sc cutoff L Λ [])
    exact initialValue_heq D Λ Sc cutoff L
  | cons a l ih =>
    cases p with
    | cons a side s hv p =>
      have ha := hl a List.mem_cons_self
      have ht : ∀ b ∈ l, b.l.1 = true := fun b hb => hl b (List.mem_cons_of_mem _ hb)
      rcases a with ⟨⟨b, i⟩, r⟩
      cases b with
      | false => cases ha
      | true =>
        have hs := SPath.side_eq_false_of_upward_probe_zero i side p ht rfl
        subst side
        change SPath l (0, c - Finsupp.single i 1) (0, 0) at p
        have hci : 1 ≤ c i := hv
        have hp := ih p ht
        have hx : ReservoirWord.weight D Λ (c - Finsupp.single i 1) =
            PowerWordWeight.wordWeight D Λ ((l.map (fun a => a.l.2)).reverse) :=
          (congrArg (ReservoirWord.weight D Λ) (path_content p ht)).trans
            (reversed_word_weight D Λ l)
        have hy : ReservoirWord.weight D Λ c = PowerWordWeight.wordWeight D Λ
            (((l.map (fun a => a.l.2)).reverse) ++ [i]) := by
          have hc := path_content (SPath.cons ⟨(true, i), r⟩ false (0, c) hci p) hl
          simpa only [List.map_cons, List.reverse_cons] using
            (congrArg (ReservoirWord.weight D Λ) hc).trans
              (reversed_word_weight D Λ (⟨(true, i), r⟩ :: l))
        have hh : ReservoirWord.weight D Λ (c - Finsupp.single i 1) + D.α i =
            ReservoirWord.weight D Λ c := by
          simp only [ReservoirWord.weight]
          rw [add_assoc, contentWeight_sub_single hci]
        erw [ReservoirWord.word_cons (elvRouquierData D Sc cutoff N Λ) Λ i r hci p ht]
        change HEq ((elvE D Sc cutoff N i Λ hh).obj
          ((ReservoirWord.word (elvRouquierData D Sc cutoff N Λ) Λ p ht).obj
            (initialValue D Λ Sc cutoff L))) _
        have hwords : ((l.map (fun a => a.l.2)).reverse) ++ [i] =
            (((⟨(true, i), r⟩ :: l).map (fun a => a.l.2)).reverse) := by
          rw [List.map_cons, List.reverse_cons]
        exact (induction_obj_heq D Λ Sc cutoff N i hx hy hh
          (PowerWordWeight.wordWeight_append D Λ ((l.map (fun a => a.l.2)).reverse) i) hp).trans
            ((heq_of_eq (PowerWordEvaluation.value_append D Sc cutoff L Λ
              ((l.map (fun a => a.l.2)).reverse) i).symm).trans
                (value_word_heq D Λ Sc cutoff L hwords))

/-- The actual native reservoir path, evaluated on its actual empty-word
family, is the chosen E-word value with reversed colours. No initial
vacuum-identification or factor-existence premise is assumed. -/
theorem reservoirPath_value_heq (l : List (SKM.Col I X)) (hl : ∀ a ∈ l, a.l.1 = true) :
    HEq ((ReservoirWord.word (elvRouquierData D Sc cutoff N Λ) Λ
      (SPath.reservoirPath l hl 0) hl).obj (initialValue D Λ Sc cutoff L))
      (PowerWordEvaluation.value D Sc cutoff L Λ ((l.map (fun a => a.l.2)).reverse)) :=
  word_value_heq D Λ Sc cutoff L (SPath.reservoirPath l hl 0) hl

private theorem pathValueAt_eq (l : List (SKM.Col I X)) (hl : ∀ a ∈ l, a.l.1 = true) :
    pathValueAt D Λ Sc cutoff L l hl =
      PowerWordEvaluation.value D Sc cutoff L Λ ((l.map (fun a => a.l.2)).reverse) := by
  apply eq_of_heq
  exact (cast_heq (congrArg (ELVWeightProduct D Sc cutoff N Λ) (path_weight D Λ l))
    (pathValue D Λ Sc cutoff L l hl)).trans (reservoirPath_value_heq D Λ Sc cutoff L l hl)

/-- The native path value has the very same selected full word chart,
after its proved original-weight transport. No gauge is chosen. -/
def pathChart (l : List (SKM.Col I X)) (hl : ∀ a ∈ l, a.l.1 = true) :
    pathValueAt D Λ Sc cutoff L l hl ≅ PowerWordWeight.wordFamily D Sc cutoff L Λ
      (PowerWordWeight.wordWeight D Λ ((l.map (fun a => a.l.2)).reverse))
      ((l.map (fun a => a.l.2)).reverse) :=
  eqToIso (pathValueAt_eq D Λ Sc cutoff L l hl) ≪≫
    PowerWordEvaluation.chart D Sc cutoff L Λ ((l.map (fun a => a.l.2)).reverse)

/-- The path chart is even on the whole weight product. -/
theorem pathChart_hom_mem (l : List (SKM.Col I X)) (hl : ∀ a ∈ l, a.l.1 = true) :
    (pathChart D Λ Sc cutoff L l hl).hom ∈ Supercategory.parity (R := k) _ _ 0 := by
  change eqToHom (pathValueAt_eq D Λ Sc cutoff L l hl) ≫
    (PowerWordEvaluation.chart D Sc cutoff L Λ ((l.map (fun a => a.l.2)).reverse)).hom ∈ _
  simpa only [zero_add] using comp_mem
    (eqToHom_mem_parity_zero (pathValueAt_eq D Λ Sc cutoff L l hl))
    (PowerWordEvaluation.chart_even D Sc cutoff L Λ ((l.map (fun a => a.l.2)).reverse))

end ChosenValue

end OddMath.QuiverHecke.ELVOld.ReservoirWordValue

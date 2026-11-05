import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumWords

/-! # Tensor-vacuum Homs along the given reservoir words

SwappedVacuumCoordinates §§2–6: identify the entire selected tensor Hom
postcomposed by the actual reservoir path word with the chosen append
word Hom. The original weight equality is proved, and labels are reversed.
This is a comparison of whole functors, not only their regular-probe value.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.TensorReservoirWords
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (cutoff : I → ℕ) (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "W" => elvRouquierData D Sc cutoff N ΛR
local notation "R₀" => WeightTensorVacuum.regularProbe D Sc m ΛP

private def atWeight {x y : X} (h : x = y)
    (F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x) :
    probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR y := h ▸ F

private theorem atWeight_heq {x y : X} (h : x = y)
    (F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x) :
    HEq (atWeight D Sc m cutoff L ΛP ΛR h F) F := by
  subst y
  rfl

omit [Fintype I] in
private theorem initial_weight : ReservoirWord.weight D ΛR 0 = PowerWordWeight.wordWeight D ΛR [] := by
  simp [ReservoirWord.weight, PowerWordWeight.wordWeight]

omit [Fintype I] in
private theorem edge (i : I) (c : I →₀ ℕ) (hc : 1 ≤ c i) :
    ReservoirWord.weight D ΛR (c - Finsupp.single i 1) + D.α i = ReservoirWord.weight D ΛR c := by
  simp only [ReservoirWord.weight]
  rw [add_assoc, contentWeight_sub_single hc]

private theorem postE_heq (i : I) {x y x' y' : X} (hx : x = x') (hy : y = y')
    (h : x + D.α i = y) (h' : x' + D.α i = y')
    {F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x}
    {F' : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x'}
    (hF : HEq F F') : HEq (F ≫ (W).E i h) (F' ≫ (W).E i h') := by
  cases hx
  cases hy
  cases hF
  rfl

private theorem wordHom_word_heq {ν τ : List I} (h : ν = τ) :
    HEq (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν)
      (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR τ) := by
  subst τ
  rfl

/-- Postcompose the actual selected tensor-vacuum Hom by the given
reservoir path word, retaining its original formal-content weight. -/
def pathHom {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
      elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR c) :=
  WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L ≫ ReservoirWord.word (W) ΛR p hl

private theorem comparison {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    ReservoirWord.weight D ΛR c = PowerWordWeight.wordWeight D ΛR ((l.map (fun a => a.l.2)).reverse) ∧
    HEq (pathHom D Sc m cutoff L ΛP ΛR p hl)
      (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ((l.map (fun a => a.l.2)).reverse)) := by
  induction l generalizing c with
  | nil =>
    cases p
    refine ⟨initial_weight D ΛR, ?_⟩
    change HEq (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L ≫
      ReservoirWord.word (W) ΛR (SPath.nil (0,0)) hl)
      (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR [])
    rw [ReservoirWord.word_nil]
    apply (heq_of_eq (show WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L ≫
      (𝟙 (elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR 0))) =
        WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L from rfl)).trans
    unfold TensorVacuumWords.wordHom
    simp only [List.reverseRecOn_nil]
    change HEq (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L)
      (atWeight D Sc m cutoff L ΛP ΛR (initial_weight D ΛR)
        (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L))
    exact (atWeight_heq D Sc m cutoff L ΛP ΛR (initial_weight D ΛR) _).symm
  | cons a l ih =>
    cases p with
    | cons a side s hv p =>
      have ha := hl a List.mem_cons_self
      have ht : ∀ b ∈ l, b.l.1 = true := fun b hb => hl b (List.mem_cons_of_mem _ hb)
      rcases a with ⟨⟨b,i⟩,r⟩
      cases b with
      | false => cases ha
      | true =>
        have hs := SPath.side_eq_false_of_upward_probe_zero i side p ht rfl
        subst side
        change SPath l (0,c - Finsupp.single i 1) (0,0) at p
        have hp := ih p ht
        have hci : 1 ≤ c i := hv
        have hy : ReservoirWord.weight D ΛR c = PowerWordWeight.wordWeight D ΛR
            (((l.map (fun a => a.l.2)).reverse) ++ [i]) :=
          (edge D ΛR i c hci).symm.trans ((congrArg (fun x => x + D.α i) hp.1).trans
            (PowerWordWeight.wordWeight_append D ΛR ((l.map (fun a => a.l.2)).reverse) i))
        refine ⟨by simpa only [List.map_cons, List.reverse_cons] using hy, ?_⟩
        have hc : pathHom D Sc m cutoff L ΛP ΛR
            (SPath.cons ⟨(true,i),r⟩ false (0,c) hci p) hl =
            pathHom D Sc m cutoff L ΛP ΛR p ht ≫ (W).E i (edge D ΛR i c hci) :=
          congrArg (fun (F : elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR 0) ⟶
              elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR c)) =>
            WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L ≫ F)
              (ReservoirWord.word_cons (W) ΛR i r hci p ht)
        have hwords : ((l.map (fun a => a.l.2)).reverse) ++ [i] =
            (((⟨(true,i),r⟩ :: l).map (fun a => a.l.2)).reverse) := by
          rw [List.map_cons, List.reverse_cons]
        have hpost := postE_heq D Sc m cutoff L ΛP ΛR i hp.1 hy (edge D ΛR i c hci)
          (PowerWordWeight.wordWeight_append D ΛR ((l.map (fun a => a.l.2)).reverse) i) hp.2
        have happ := heq_of_eq (TensorVacuumWords.wordHom_append D Sc m cutoff L ΛP ΛR
          ((l.map (fun a => a.l.2)).reverse) i).symm
        have hlist := wordHom_word_heq D Sc m cutoff L ΛP ΛR hwords
        exact (heq_of_eq hc).trans (hpost.trans (happ.trans hlist))

omit [Fintype I] in
/-- The actual endpoint weight is the unchanged original weight of the
reversed labelled colour word. -/
theorem path_weight {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    ReservoirWord.weight D ΛR c = PowerWordWeight.wordWeight D ΛR ((l.map (fun a => a.l.2)).reverse) := by
  induction l generalizing c with
  | nil => cases p; exact initial_weight D ΛR
  | cons a l ih =>
    cases p with
    | cons a side s hv p =>
      have ha := hl a List.mem_cons_self
      have ht : ∀ b ∈ l, b.l.1 = true := fun b hb => hl b (List.mem_cons_of_mem _ hb)
      rcases a with ⟨⟨b,i⟩,r⟩
      cases b with
      | false => cases ha
      | true =>
        have hs := SPath.side_eq_false_of_upward_probe_zero i side p ht rfl
        subst side
        have hy := (edge D ΛR i c hv).symm.trans ((congrArg (fun x => x + D.α i) (ih p ht)).trans
          (PowerWordWeight.wordWeight_append D ΛR ((l.map (fun a => a.l.2)).reverse) i))
        simpa only [List.map_cons, List.reverse_cons] using hy

/-- The entire postcomposed tensor Hom is the chosen reversed append Hom,
with only its proved original-weight endpoint presentation changed. -/
theorem pathHom_heq {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    HEq (pathHom D Sc m cutoff L ΛP ΛR p hl)
      (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ((l.map (fun a => a.l.2)).reverse)) :=
  (comparison D Sc m cutoff L ΛP ΛR p hl).2

/-- The literal reservoir postcomposition at the proved reversed-word weight. -/
def pathHomAt {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR
      (PowerWordWeight.wordWeight D ΛR ((l.map (fun a => a.l.2)).reverse)) :=
  atWeight D Sc m cutoff L ΛP ΛR (path_weight D ΛR p hl)
    (pathHom D Sc m cutoff L ΛP ΛR p hl)

/-- Equality of whole chosen functors, not an agreement only on a probe
vector or on the coefficient vacuum. -/
theorem pathHomAt_eq_wordHom {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    pathHomAt D Sc m cutoff L ΛP ΛR p hl =
      TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ((l.map (fun a => a.l.2)).reverse) :=
  eq_of_heq ((atWeight_heq D Sc m cutoff L ΛP ΛR _ _).trans
    (pathHom_heq D Sc m cutoff L ΛP ΛR p hl))

/-- The path-Hom value uses precisely the existing chosen word chart on
every actual regular-probe vector and full original-weight component. -/
def valueChart {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    (pathHomAt D Sc m cutoff L ΛP ΛR p hl).obj R₀ ≅
      PowerWordWeight.wordFamily D Sc cutoff L ΛR
        (PowerWordWeight.wordWeight D ΛR ((l.map (fun a => a.l.2)).reverse))
        ((l.map (fun a => a.l.2)).reverse) :=
  eqToIso (congrArg (fun F => F.obj R₀) (pathHomAt_eq_wordHom D Sc m cutoff L ΛP ΛR p hl)) ≪≫
    TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR ((l.map (fun a => a.l.2)).reverse)

end OddMath.QuiverHecke.ELVOld.TensorReservoirWords

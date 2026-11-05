import OddMath.QuiverHecke.CyclotomicAction.ELVTensorHomContexts

/-! # Actual reservoir words as the chosen E contexts

SwappedVacuumCoordinates §§2–6: compare the unchanged reservoir word
at arbitrary intermediate formal content with the prescribed context
functor, using the proved original-weight endpoint and reversed labels.
No support or boundary vanishing property of arbitrary Hom objects is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ReservoirContexts
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (cutoff : I → ℕ) (L : I × ℕ → ℕ) (Λ : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "W" => elvRouquierData D Sc cutoff N Λ

omit [Fintype I] in
private theorem context_weight_append (x : X) (η : List I) (i : I) :
    PowerWordWeightContexts.contextWeight D x (η ++ [i]) =
      PowerWordWeightContexts.contextWeight D x η + D.α i := by
  induction η generalizing x with
  | nil => rfl
  | cons j η ih => exact ih (x + D.α j)

omit [Fintype I] in
private theorem edge (i : I) (c : I →₀ ℕ) (hc : 1 ≤ c i) :
    ReservoirWord.weight D Λ (c - Finsupp.single i 1) + D.α i = ReservoirWord.weight D Λ c := by
  simp only [ReservoirWord.weight]
  rw [add_assoc, contentWeight_sub_single hc]

private theorem pre_heq {x₀ x y y' : X} (hy : y = y')
    {F : elvWeightSpace D Sc cutoff N Λ x ⟶ elvWeightSpace D Sc cutoff N Λ y}
    {F' : elvWeightSpace D Sc cutoff N Λ x ⟶ elvWeightSpace D Sc cutoff N Λ y'}
    (K : elvWeightSpace D Sc cutoff N Λ x₀ ⟶ elvWeightSpace D Sc cutoff N Λ x)
    (hF : HEq F F') : HEq (K ≫ F) (K ≫ F') := by
  cases hy
  cases hF
  rfl

private theorem postE_heq (i : I) {x₀ x y x' y' : X} (hx : x = x') (hy : y = y')
    (h : x + D.α i = y) (h' : x' + D.α i = y')
    {F : elvWeightSpace D Sc cutoff N Λ x₀ ⟶ elvWeightSpace D Sc cutoff N Λ x}
    {F' : elvWeightSpace D Sc cutoff N Λ x₀ ⟶ elvWeightSpace D Sc cutoff N Λ x'}
    (hF : HEq F F') : HEq (F ≫ (W).E i h) (F' ≫ (W).E i h') := by
  cases hx
  cases hy
  cases hF
  rfl

private theorem context_append_heq (x : X) (η : List I) (i : I) :
    HEq (TensorHomContexts.context D Sc cutoff L Λ x (η ++ [i]))
      (TensorHomContexts.context D Sc cutoff L Λ x η ≫
        (W).E i (rfl : PowerWordWeightContexts.contextWeight D x η + D.α i =
          PowerWordWeightContexts.contextWeight D x η + D.α i)) := by
  induction η generalizing x with
  | nil => rfl
  | cons j η ih =>
    exact pre_heq D Sc cutoff L Λ (context_weight_append D (x + D.α j) η i)
      ((W).E j (rfl : x + D.α j = x + D.α j)) (ih (x + D.α j))

private theorem context_word_heq (x : X) {η θ : List I} (h : η = θ) :
    HEq (TensorHomContexts.context D Sc cutoff L Λ x η)
      (TensorHomContexts.context D Sc cutoff L Λ x θ) := by
  subst θ
  rfl

omit [Fintype I] in
/-- The endpoint weight follows the actual reversed colour context,
including a nonzero intermediate formal starting content. -/
theorem word_weight {l : List (SKM.Col I X)} {c d : I →₀ ℕ}
    (p : SPath l (0,c) (0,d)) (hl : ∀ a ∈ l, a.l.1 = true) :
    ReservoirWord.weight D Λ c = PowerWordWeightContexts.contextWeight D
      (ReservoirWord.weight D Λ d) ((l.map (fun a => a.l.2)).reverse) := by
  induction l generalizing c with
  | nil => cases p; rfl
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
        have hy := (edge D Λ i c hv).symm.trans ((congrArg (fun x => x + D.α i) (ih p ht)).trans
          (context_weight_append D (ReservoirWord.weight D Λ d) ((l.map (fun a => a.l.2)).reverse) i).symm)
        simpa only [List.map_cons, List.reverse_cons] using hy

/-- The whole given reservoir word and the chosen E-context functor
agree after changing only their proved original-weight endpoint. -/
theorem word_heq {l : List (SKM.Col I X)} {c d : I →₀ ℕ}
    (p : SPath l (0,c) (0,d)) (hl : ∀ a ∈ l, a.l.1 = true) :
    HEq (ReservoirWord.word (W) Λ p hl)
      (TensorHomContexts.context D Sc cutoff L Λ (ReservoirWord.weight D Λ d)
        ((l.map (fun a => a.l.2)).reverse)) := by
  induction l generalizing c with
  | nil => cases p; rw [ReservoirWord.word_nil]; rfl
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
        change SPath l (0,c - Finsupp.single i 1) (0,d) at p
        have hci : 1 ≤ c i := hv
        have hx := word_weight D Λ p ht
        have hy := (edge D Λ i c hci).symm.trans (congrArg (fun x => x + D.α i) hx)
        have hpost := postE_heq D Sc cutoff L Λ i hx hy (edge D Λ i c hci) rfl (ih p ht)
        have happ := context_append_heq D Sc cutoff L Λ (ReservoirWord.weight D Λ d)
          ((l.map (fun a => a.l.2)).reverse) i
        have hwords : ((l.map (fun a => a.l.2)).reverse) ++ [i] =
            (((⟨(true,i),r⟩ :: l).map (fun a => a.l.2)).reverse) := by
          rw [List.map_cons, List.reverse_cons]
        have hlist := context_word_heq D Sc cutoff L Λ (ReservoirWord.weight D Λ d) hwords
        exact (heq_of_eq (ReservoirWord.word_cons (W) Λ i r hci p ht)).trans
          (hpost.trans (happ.symm.trans hlist))

private def atWeight {x y y' : X} (h : y = y')
    (F : elvWeightSpace D Sc cutoff N Λ x ⟶ elvWeightSpace D Sc cutoff N Λ y) :
    elvWeightSpace D Sc cutoff N Λ x ⟶ elvWeightSpace D Sc cutoff N Λ y' := h ▸ F

private theorem atWeight_heq {x y y' : X} (h : y = y')
    (F : elvWeightSpace D Sc cutoff N Λ x ⟶ elvWeightSpace D Sc cutoff N Λ y) :
    HEq (atWeight D Sc cutoff L Λ h F) F := by cases h; rfl

/-- The actual outer reservoir word at its proved context endpoint. -/
def wordAt {l : List (SKM.Col I X)} {c d : I →₀ ℕ}
    (p : SPath l (0,c) (0,d)) (hl : ∀ a ∈ l, a.l.1 = true) :
    elvWeightSpace D Sc cutoff N Λ (ReservoirWord.weight D Λ d) ⟶
      elvWeightSpace D Sc cutoff N Λ (PowerWordWeightContexts.contextWeight D
        (ReservoirWord.weight D Λ d) ((l.map (fun a => a.l.2)).reverse)) :=
  atWeight D Sc cutoff L Λ (word_weight D Λ p hl) (ReservoirWord.word (W) Λ p hl)

end OddMath.QuiverHecke.ELVOld.ReservoirContexts

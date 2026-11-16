import OddMath.QuiverHecke.SwappedAssembly.ReservoirPaths
import OddMath.SKM.RouquierHomContentCoherence

/-! # The native reservoir word beneath a vacuum path

SwappedActionAssembly §6 and SwappedVacuumCoordinates §2: remove the
content-parity shifts at probe content zero and identify the entire path
functor with postcomposition by its reservoir induction word. A labelled
word is read from right to left: its tail induction precedes its head.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ReservoirWord

/-- Original reservoir weight at the specified formal content. -/
def weight (D : Datum I X) (Λ : X) (c : I →₀ ℕ) : X := -Λ + contentWeight D c

private theorem height (Λ : X) (i : I) (c : I →₀ ℕ) (hc : 1 ≤ c i) :
    weight D Λ (c - Finsupp.single i 1) + D.α i = weight D Λ c := by
  simp only [weight]
  rw [add_assoc, contentWeight_sub_single hc]

variable (W : RouquierData (k := k) (B := B) D) (Λ : X)

/-- The reservoir induction word of an upward vacuum path. It uses only
the prescribed upward generator data, independently of any probe factor. -/
def word {l : List (Col I X)} {c d : I →₀ ℕ}
    (p : SPath l (0, c) (0, d)) (hl : ∀ a ∈ l, a.l.1 = true) :
    W.obj (weight D Λ d) ⟶ W.obj (weight D Λ c) := by
  cases l with
  | nil => cases p; exact 𝟙 _
  | cons a l =>
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
        exact word p ht ≫ W.E i (height Λ i c hv)
termination_by l.length

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- The empty reservoir induction word is the identity. -/
theorem word_nil (d : I →₀ ℕ) :
    word W Λ (.nil (0, d)) (by simp) = 𝟙 _ := by
  rw [word]
  rfl

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- The tail induction is followed by the first letter's induction. -/
theorem word_cons (i : I) (r : X) {l : List (Col I X)}
    {c d : I →₀ ℕ} (hc : 1 ≤ c i) (p : SPath l (0, c - Finsupp.single i 1) (0, d))
    (hl : ∀ a ∈ l, a.l.1 = true) :
    word W Λ (.cons ⟨(true, i), r⟩ false (0, c) hc p)
      (by simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨True.intro, hl⟩) =
        word W Λ p hl ≫ W.E i (height Λ i c hc) := by
  rw [word]
  rfl

end ReservoirWord

namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

/-- The full path functor is unshifted postcomposition by its actual
reservoir word, rather than only an agreement on a cyclic vector. -/
private def reservoirWordComparison {l : List (Col I X)} {c d : I →₀ ℕ}
    (p : SPath l (0, c) (0, d)) (hl : ∀ a ∈ l, a.l.1 = true) :
    { e : P.pathFunctor p ≅ homPost (k := k) (a := P.T.obj (-P.muP (0, d)))
      (ReservoirWord.word P.W.toRouquierData P.ΛR p hl) //
        ∀ Z, e.hom.app Z ∈ parity (R := k) _ _ 0 } := by
  induction l generalizing c with
  | nil =>
    cases p
    rw [ReservoirWord.word_nil]
    refine ⟨(homPostId (k := k) (P.T.obj (-P.muP (0, d)))
      (P.W.obj (P.muM (0, d)))).symm, ?_⟩
    intro Z
    exact inv_mem (rightUnitor Z) (TwoSupercategory.rightUnitor_hom_mem (R := k) Z)
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
        let E := P.W.E i (ReservoirWord.height P.ΛR i c hv)
        have hp := ih p ht
        rw [pathFunctor_cons]
        have hstep : P.step (true, i) false (0, c) hv = homPost (k := k) E := by
          simp only [step, homContentPostE, homContentShift, contentParity, map_zero,
            mul_zero, homParityShift_zero, Functor.comp_id]
          rfl
        rw [hstep]
        rw [ReservoirWord.word_cons P.W.toRouquierData P.ΛR i r hv p ht]
        refine ⟨Functor.isoWhiskerRight hp.1 (homPost (k := k) E) ≪≫
          homPostComp (ReservoirWord.word P.W.toRouquierData P.ΛR p ht) E, ?_⟩
        intro Z
        change (hp.1.hom.app Z) ▷ E ≫
          (associator Z (ReservoirWord.word P.W.toRouquierData P.ΛR p ht) E).hom ∈
            parity (R := k) ((P.pathFunctor p).obj Z ≫ E)
              (Z ≫ ReservoirWord.word P.W.toRouquierData P.ΛR p ht ≫ E) 0
        simpa only [zero_add] using comp_mem
          (TwoSupercategory.whiskerRight_mem E (hp.2 Z))
          (TwoSupercategory.associator_hom_mem (R := k) Z
            (ReservoirWord.word P.W.toRouquierData P.ΛR p ht) E)

/-- The whole vacuum-path functor is postcomposition by the native
reservoir word, with every content-parity shift removed. -/
def reservoirWordFunctorIso {l : List (Col I X)} {c d : I →₀ ℕ}
    (p : SPath l (0, c) (0, d)) (hl : ∀ a ∈ l, a.l.1 = true) :
    P.pathFunctor p ≅ homPost (k := k) (a := P.T.obj (-P.muP (0, d)))
      (ReservoirWord.word P.W.toRouquierData P.ΛR p hl) :=
  (P.reservoirWordComparison p hl).1

private theorem mpr_heq_iff {α β γ : Sort w} (h : α = β) (b : β) (c : γ) :
    HEq (h.mpr b) c ↔ HEq b c := by
  cases h
  rfl

private theorem evenIso_app_heq {C : Type*} [Category* C]
    {D₀ : Type*} [Category* D₀] [Preadditive D₀] [Linear k D₀] [Supercategory k D₀]
    {F F' G G' : C ⥤ D₀} (hF : F = F') (hG : G = G')
    (e : { e : F ≅ G // ∀ Z, e.hom.app Z ∈ parity (R := k) _ _ 0 })
    (e' : { e : F' ≅ G' // ∀ Z, e.hom.app Z ∈ parity (R := k) _ _ 0 })
    (he : HEq e e') (Z : C) : HEq (e.1.hom.app Z) (e'.1.hom.app Z) := by
  cases hF
  cases hG
  cases eq_of_heq he
  rfl

/-- The empty comparison is the inverse right unitor, with only its
prescribed equality transports suppressed. -/
theorem reservoirWordFunctorIso_nil_hom_heq (d : I →₀ ℕ) (Z : P.H (0,d)) :
    HEq ((P.reservoirWordFunctorIso (.nil (0,d)) (by simp)).hom.app Z)
      (rightUnitor Z).inv := by
  let e := (homPostId (k := k) (P.T.obj (-P.muP (0,d)))
    (P.W.obj (P.muM (0,d)))).symm
  have hm : ∀ Z, e.hom.app Z ∈ parity (R := k) _ _ 0 := fun Z =>
    inv_mem (rightUnitor Z) (TwoSupercategory.rightUnitor_hom_mem (R := k) Z)
  have he : HEq (P.reservoirWordComparison (.nil (0,d)) (by simp))
      (⟨e,hm⟩ : { f : (𝟭 (P.H (0,d))) ≅ homPost (k := k)
        (a := P.T.obj (-P.muP (0,d))) (𝟙 (P.W.obj (P.muM (0,d)))) //
          ∀ Z, f.hom.app Z ∈ parity (R := k) _ _ 0 }) := by
    unfold reservoirWordComparison
    dsimp only
    simp only [Prod.mk.noConfusion, Prod.noConfusion, id, mpr_heq_iff]
    rfl
  exact evenIso_app_heq rfl
    (congrArg (homPost (k := k) (a := P.T.obj (-P.muP (0,d))))
      (ReservoirWord.word_nil P.W.toRouquierData P.ΛR d))
    (P.reservoirWordComparison (.nil (0,d)) (by simp)) ⟨e,hm⟩ he Z

/-- The first upward letter appends the factor comparison and its
associator, with only the prescribed equality transports suppressed. -/
theorem reservoirWordFunctorIso_cons_hom_heq (i : I) (r : X)
    {l : List (Col I X)} {c d : I →₀ ℕ} (hc : 1 ≤ c i)
    (p : SPath l (0,c - Finsupp.single i 1) (0,d)) (hl : ∀ a ∈ l, a.l.1 = true)
    (Z : P.H (0,d)) :
    let E := P.W.E i (ReservoirWord.height P.ΛR i c hc)
    HEq ((P.reservoirWordFunctorIso
      (.cons ⟨(true,i),r⟩ false (0,c) hc p)
      (by simp only [List.mem_cons,forall_eq_or_imp]; exact ⟨True.intro,hl⟩)).hom.app Z)
      (((P.reservoirWordFunctorIso p hl).hom.app Z) ▷ E ≫
        (associator Z (ReservoirWord.word P.W.toRouquierData P.ΛR p hl) E).hom) := by
  dsimp only
  let E := P.W.E i (ReservoirWord.height P.ΛR i c hc)
  let e := Functor.isoWhiskerRight (P.reservoirWordComparison p hl).1 (homPost (k := k) E) ≪≫
    homPostComp (ReservoirWord.word P.W.toRouquierData P.ΛR p hl) E
  have hm : ∀ Z, e.hom.app Z ∈ parity (R := k) _ _ 0 := by
    intro Z
    change ((P.reservoirWordComparison p hl).1.hom.app Z) ▷ E ≫
      (associator Z (ReservoirWord.word P.W.toRouquierData P.ΛR p hl) E).hom ∈ parity (R := k) _ _ 0
    simpa only [zero_add] using comp_mem
      (TwoSupercategory.whiskerRight_mem E ((P.reservoirWordComparison p hl).2 Z))
      (TwoSupercategory.associator_hom_mem (R := k) Z
        (ReservoirWord.word P.W.toRouquierData P.ΛR p hl) E)
  have hF : P.pathFunctor (.cons ⟨(true,i),r⟩ false (0,c) hc p) =
      P.pathFunctor p ⋙ homPost (k := k) E := by
    rw [pathFunctor_cons]
    congr 1
  have hG := congrArg (homPost (k := k) (a := P.T.obj (-P.muP (0,d))))
    (ReservoirWord.word_cons P.W.toRouquierData P.ΛR i r hc p hl)
  have he : HEq (P.reservoirWordComparison (.cons ⟨(true,i),r⟩ false (0,c) hc p)
      (by simp only [List.mem_cons,forall_eq_or_imp]; exact ⟨True.intro,hl⟩))
      (⟨e,hm⟩ : { f : (P.pathFunctor p ⋙ homPost (k := k) E) ≅
        homPost (k := k) (a := P.T.obj (-P.muP (0,d)))
          (ReservoirWord.word P.W.toRouquierData P.ΛR p hl ≫ E) //
            ∀ Z, f.hom.app Z ∈ parity (R := k) _ _ 0 }) := by
    unfold reservoirWordComparison
    dsimp only
    simp only [Prod.mk.noConfusion, Prod.noConfusion, List.cons.noConfusion,
      List.noConfusion, id, mpr_heq_iff]
    rfl
  exact evenIso_app_heq hF hG
    (P.reservoirWordComparison (.cons ⟨(true,i),r⟩ false (0,c) hc p)
      (by simp only [List.mem_cons,forall_eq_or_imp]; exact ⟨True.intro,hl⟩)) ⟨e,hm⟩ he Z

/-- The comparison is even, so transporting odd dot and crossing entries
through it introduces no new Koszul factor. -/
theorem reservoirWordFunctorIso_hom_mem {l : List (Col I X)} {c d : I →₀ ℕ}
    (p : SPath l (0, c) (0, d)) (hl : ∀ a ∈ l, a.l.1 = true)
    (Z : P.H (0, d)) :
    (P.reservoirWordFunctorIso p hl).hom.app Z ∈ parity (R := k) _ _ 0 :=
  (P.reservoirWordComparison p hl).2 Z

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly


/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanCapsElim
import OddMath.SKM.SpanCapBlock

/-!
# The cap push

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1, whose proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11. As in the proof of KL III Proposition
3.11, the cap block `capBlk S l d` on top of a move diagram is pushed down one move at a time
(`PushGoal`, `OddMath.SKM.SpanCapsElim`), using the local relations of
`OddMath.SKM.SpanCapBlock`. A dot of odd colour moving around the leftward cap `ε'` produces twice
the odd bubble in a middle region ((4.3)); the bubble is moved to the rightmost region by
`BubbleSlideOut`.

## Main results

* `posDot`, `posPair`: the positions of a move relative to the block.
* `push_dot`: the cap push through a dot.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} {cs : CScalars Sc}

/-! ## Positions of a move relative to the block -/

theorem split1 {α : Type*} {x y : α} : ∀ {u v L₁ L₂ : List α}, u ++ [x] ++ v = L₁ ++ [y] ++ L₂ →
    (∃ R, L₁ = u ++ [x] ++ R ∧ v = R ++ [y] ++ L₂) ∨ (u = L₁ ∧ x = y ∧ v = L₂) ∨
      (∃ R, u = L₁ ++ [y] ++ R ∧ L₂ = R ++ [x] ++ v)
  | [], v, [], L₂, h => by simp at h; exact Or.inr (Or.inl ⟨rfl, h.1, h.2⟩)
  | [], v, b :: L₁, L₂, h => by
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨L₁, by simp, by simp⟩
  | a :: u, v, [], L₂, h => by
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr (Or.inr ⟨u, by simp, by simp⟩)
  | a :: u, v, b :: L₁, L₂, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rcases split1 (by simpa using h) with ⟨R, h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩ | ⟨R, h₁, h₂⟩
    · exact Or.inl ⟨R, by simp [h₁], h₂⟩
    · exact Or.inr (Or.inl ⟨by simp [h₁], h₂, h₃⟩)
    · exact Or.inr (Or.inr ⟨R, by simp [h₁], h₂⟩)

/-- The position of a strand `x` relative to the block `P A S B Q`. -/
theorem posDot {α : Type*} {u v P S Q : List α} {x A B : α}
    (h : u ++ [x] ++ v = P ++ [A] ++ S ++ [B] ++ Q) :
    (∃ R, P = u ++ [x] ++ R ∧ v = R ++ [A] ++ S ++ [B] ++ Q) ∨
      (u = P ∧ x = A ∧ v = S ++ [B] ++ Q) ∨
      (∃ S₁ S₂, S = S₁ ++ [x] ++ S₂ ∧ u = P ++ [A] ++ S₁ ∧ v = S₂ ++ [B] ++ Q) ∨
      (u = P ++ [A] ++ S ∧ x = B ∧ v = Q) ∨
      (∃ R, Q = R ++ [x] ++ v ∧ u = P ++ [A] ++ S ++ [B] ++ R) := by
  rcases split1 (L₁ := P) (L₂ := S ++ [B] ++ Q) (by simpa using h) with
    ⟨R, h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩ | ⟨R, h₁, h₂⟩
  · exact Or.inl ⟨R, h₁, by simpa using h₂⟩
  · exact Or.inr (Or.inl ⟨h₁, h₂, h₃⟩)
  · rcases split1 (u := R) (v := v) (L₁ := S) (L₂ := Q) (by simpa using h₂.symm) with
      ⟨R', h₃, h₄⟩ | ⟨h₃, h₄, h₅⟩ | ⟨R', h₃, h₄⟩
    · exact Or.inr (Or.inr (Or.inl ⟨R, R', h₃, by simpa using h₁, by simpa using h₄⟩))
    · subst h₃; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by simpa using h₁, h₄, h₅⟩)))
    · subst h₃
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨R', h₄, by simpa using h₁⟩)))

/-- The position of two adjacent strands `y z` relative to the block `P A S B Q`. -/
theorem posPair {α : Type*} {u v P S Q : List α} {y z A B : α}
    (h : u ++ [y, z] ++ v = P ++ [A] ++ S ++ [B] ++ Q) :
    (∃ R, P = u ++ [y, z] ++ R ∧ v = R ++ [A] ++ S ++ [B] ++ Q) ∨
      (P = u ++ [y] ∧ z = A ∧ v = S ++ [B] ++ Q) ∨
      (u = P ∧ y = A ∧ ∃ S', S = z :: S' ∧ v = S' ++ [B] ++ Q) ∨
      (u = P ∧ y = A ∧ S = [] ∧ z = B ∧ v = Q) ∨
      (∃ S₁ S₂, S = S₁ ++ [y, z] ++ S₂ ∧ u = P ++ [A] ++ S₁ ∧ v = S₂ ++ [B] ++ Q) ∨
      (∃ S', S = S' ++ [y] ∧ z = B ∧ u = P ++ [A] ++ S' ∧ v = Q) ∨
      (u = P ++ [A] ++ S ∧ y = B ∧ Q = z :: v) ∨
      (∃ R, Q = R ++ [y, z] ++ v ∧ u = P ++ [A] ++ S ++ [B] ++ R) := by
  rcases posDot (u := u) (x := y) (v := z :: v) (by simpa using h) with
    ⟨R, h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩ | ⟨S₁, S₂, h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨R, h₁, h₂⟩
  · rcases R with _ | ⟨r, R⟩
    · simp at h₂
      exact Or.inr (Or.inl ⟨by simpa using h₁, h₂.1, by simpa using h₂.2⟩)
    · simp at h₂
      exact Or.inl ⟨R, by simp [h₁, h₂.1], by simpa using h₂.2⟩
  · rcases S with _ | ⟨s, S⟩
    · simp at h₃
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h₁, h₂, rfl, h₃.1, h₃.2⟩)))
    · simp at h₃
      exact Or.inr (Or.inr (Or.inl ⟨h₁, h₂, S, by simp [h₃.1], by simpa using h₃.2⟩))
  · rcases S₂ with _ | ⟨s, S₂⟩
    · simp at h₃
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨S₁, by simpa using h₁, h₃.1, h₂,
        h₃.2⟩)))))
    · simp at h₃
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨S₁, S₂, by simp [h₁, h₃.1], h₂,
        by simpa using h₃.2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h₁, h₂, h₃.symm⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨R, by simp [h₁], h₂⟩))))))

/-! ## Concluding a step of the cap push -/

section Push

variable {μ : X} {w₀ : List (Letter I)}

theorem capT_of_xeq {T : List (Letter I)} {c c' t : ℕ} (hF : LowHyp cs μ w₀ c) {L L'}
    (E : XEq cs μ w₀ T c' L L') (hc : c' < c) (ht : c' ≤ t)
    (h : xev cs μ w₀ T L' ∈ CapTarget D Sc cs μ w₀ T t) :
    xev cs μ w₀ T L ∈ CapTarget D Sc cs μ w₀ T t := by
  obtain ⟨p, hp⟩ := E
  exact capT_of_sub hF hc ht hp (Submodule.smul_mem _ _ h)

/-- The block of the induction hypothesis followed by moves lies in `CapTarget`. -/
theorem push_tail {c t : ℕ} {ms : List (Mv I)} (hIH : PushHyp cs μ w₀ c ms)
    {T P S Q : List (Letter I)} {l : Letter I} {d : ℕ} {L : List (XLayer I)}
    (hms : MvChain w₀ ms (P ++ [flipL l] ++ S ++ [l] ++ Q)) (ns : List (Mv I))
    (hns : MvChain (P ++ S ++ Q) ns T)
    (hL : L = mvLay ms ++ (capBlk S l d).map (xwhL P Q) ++ mvLay ns)
    (hc : xcnt (mvLay ms) + S.length ≤ c)
    (ht : xcnt (mvLay ms) + S.length + xcnt (mvLay ns) ≤ t) :
    xev cs μ w₀ T L ∈ CapTarget D Sc cs μ w₀ T t := by
  subst hL
  have hB : XChain (P ++ [flipL l] ++ S ++ [l] ++ Q) ((capBlk S l d).map (xwhL P Q))
      (P ++ S ++ Q) := by
    simpa using (xChain_capBlk S l d).whisk P Q
  rw [xev_append cs _ (hms.xChain.append hB)]
  exact capTarget_mono cs ht (capTarget_comp_mvs cs (hIH P S Q l d hms hc) hns)

/-- A product of bubbles placed in a middle region, after an element of `CapTarget`. -/
theorem capTarget_comp_bubble_mid (hS : BubbleSlideOut D Sc cs) {P R T : List (Letter I)}
    (e : P ++ [] ++ R = T) {c : ℕ} {f} (hf : f ∈ CapTarget D Sc cs μ w₀ T c)
    {β : (pres D Sc).obj (ob D (wt D μ R) []) ⟶ (pres D Sc).obj (ob D (wt D μ R) [])}
    (hβ : IsBubbleProd cs (wt D μ R) β) :
    f ≫ wordCast μ e e (plcL D Sc μ P R [] [] β) ∈ CapTarget D Sc cs μ w₀ T c := by
  subst e
  exact capTarget_comp_bubble hS hf hβ

end Push

/-! ## A local relation with a bubble term, in context -/

theorem xev_bub_ctx (μ : X) {s₀ : List (Letter I)} (pre : List (XLayer I))
    (u v : List (Letter I)) {s : List (Letter I)} {A B C : List (XLayer I)}
    {β : (pres D Sc).obj (ob D (wt D μ v) []) ⟶ (pres D Sc).obj (ob D (wt D μ v) [])}
    {p : ZMod 2} {r : k}
    (E : xev cs (wt D μ v) s [] A =
      zsign k p • xev cs (wt D μ v) s [] B + r • (xev cs (wt D μ v) s [] C ≫ β))
    (hpre : XChain s₀ pre (u ++ s ++ v)) (hA : XChain s A []) (hB : XChain s B [])
    (hC : XChain s C []) {T : List (Letter I)} (e : u ++ [] ++ v = T) :
    xev cs μ s₀ T (pre ++ A.map (xwhL u v)) =
      zsign k p • xev cs μ s₀ T (pre ++ B.map (xwhL u v)) +
        r • (xev cs μ s₀ T (pre ++ C.map (xwhL u v)) ≫ wordCast μ e e (plcL D Sc μ u v [] [] β)) := by
  subst e
  have h := fun (M : List (XLayer I)) (hM : XChain s M []) =>
    (xev_ctx cs μ (t₀ := u ++ [] ++ v) pre [] u v hpre hM)
  simp only [List.append_nil, xev_nil, cl_nil, Category.comp_id] at h
  rw [h A hA, h B hB, h C hC, E, map_add, map_smul, map_smul, plcL_comp]
  simp only [Preadditive.comp_add, Linear.comp_smul, Category.assoc]
  rfl

/-! ## The cap push through a dot -/

section PushDot

variable {μ : X} {w₀ : List (Letter I)}

theorem isBubbleProd_oddBubble (ν : X) (i : I) : IsBubbleProd cs ν (oddBubble cs i ν) := by
  simpa using IsBubbleProd.odd (cs := cs) (ν := ν) i .id

/-- **The cap push past a dot on a strand of `S`**: the dot slides through the crossing with `B`
((3.1)–(3.6), (4.1), (4.2)). -/
theorem push_dotS {c : ℕ} {ms : List (Mv I)} (hF : LowHyp cs μ w₀ c)
    (hIH : PushHyp cs μ w₀ c ms) {P S₁ S₂ Q : List (Letter I)} {x l : Letter I} (d : ℕ)
    (hms : MvChain w₀ ms (P ++ [flipL l] ++ (S₁ ++ [x] ++ S₂) ++ [l] ++ Q))
    (hc : xcnt (mvLay ms) + (S₁ ++ [x] ++ S₂).length ≤ c) :
    xev cs μ w₀ (P ++ (S₁ ++ [x] ++ S₂) ++ Q) (mvLay ms ++
        (xDotL x).map (xwhL (P ++ [flipL l] ++ S₁) (S₂ ++ [l] ++ Q)) ++
        (capBlk (S₁ ++ [x] ++ S₂) l d).map (xwhL P Q)) ∈
      CapTarget D Sc cs μ w₀ (P ++ (S₁ ++ [x] ++ S₂) ++ Q)
        (xcnt (mvLay ms) + (S₁ ++ [x] ++ S₂).length) := by
  have hB := xChain_capBlk' (S₁ ++ [x] ++ S₂) l d
  refine capT_of_xeq hF (c' := xcnt (mvLay ms) + (S₁.length + S₂.length)) (XEq.at (mvLay ms) []
    P Q (capBlk_dotS cs (wt D μ Q) S₁ S₂ x l d) (hms.xChain.cast rfl (by simp)) ?_ ?_ ?_ rfl
    (by simp)) (by simp at hc; omega) (by simp) ?_
  · exact ((xChain_xDotL x).whisk ([flipL l] ++ S₁) (S₂ ++ [l])).app hB (by simp) |>.cast
      (by simp) rfl
  · exact hB.app ((xChain_xDotL x).whisk S₁ S₂) (by simp) |>.cast (by simp) (by simp)
  · simp
  · refine push_tail (d := d) hIH hms [Mv.dot (P ++ S₁) x (S₂ ++ Q)] ⟨by simp [Mv.src, Mv.pre, Mv.lsrc,
      Mv.post], by simp [Mv.tgt, Mv.pre, Mv.ltgt, Mv.post, MvChain]⟩ ?_ (by omega)
      (by simp [mvLay, Mv.loc])
    simp [mvLay, Mv.lay, Mv.loc, Mv.pre, Mv.post]

/-- **The cap push past a dot on the leg `B`**: the dot passes the strands `S` and then moves
around the cap to `A` ((2.3), (4.3)); the odd-bubble term of (4.3) is moved out by
`BubbleSlideOut`. -/
theorem push_dotB (hS : BubbleSlideOut D Sc cs) {c : ℕ} {ms : List (Mv I)}
    (hF : LowHyp cs μ w₀ c) (hIH : PushHyp cs μ w₀ c ms) {P S Q : List (Letter I)}
    {l : Letter I} (d : ℕ) (hms : MvChain w₀ ms (P ++ [flipL l] ++ S ++ [l] ++ Q))
    (hc : xcnt (mvLay ms) + S.length ≤ c) :
    xev cs μ w₀ (P ++ S ++ Q) (mvLay ms ++
        (xDotL l).map (xwhL (P ++ [flipL l] ++ S) Q) ++ (capBlk S l d).map (xwhL P Q)) ∈
      CapTarget D Sc cs μ w₀ (P ++ S ++ Q) (xcnt (mvLay ms) + S.length) := by
  set A := flipL l
  set pre := mvLay ms ++ (lmLc S l).map (xwhL (P ++ [A]) Q)
  have hpre : XChain w₀ pre (P ++ [A, l] ++ (S ++ Q)) :=
    hms.xChain.app ((xChain_lmLc S l).whisk (P ++ [A]) Q) (by simp)
      |>.cast rfl (by simp)
  have hDs : ∀ n, XChain [A, l] ((xDotsL A n).map (xwhL [] [l]) ++ xCapL l) [] := fun n =>
    ((xChain_xDotsL A n).whisk [] [l]).app (xChain_xCapL l) (by simp [A])
  have hDB : XChain [A, l] ((xDotL l).map (xwhL [A] []) ++ (xDotsL A d).map (xwhL [] [l]) ++
      xCapL l) [] := by
    have := ((xChain_xDotL l).whisk [A] []).app (hDs d) (by simp)
    simpa using this
  -- the dot passes the strands `S`
  have h₂ : xev cs μ w₀ (P ++ S ++ Q) (pre ++ ((xDotL l).map (xwhL [A] []) ++
      (xDotsL A d).map (xwhL [] [l]) ++ xCapL l).map (xwhL P (S ++ Q))) ∈
      CapTarget D Sc cs μ w₀ (P ++ S ++ Q) (xcnt (mvLay ms) + S.length) := by
    obtain ⟨p, r, E⟩ := dotsCap_dotB cs (wt D μ (S ++ Q)) l d
    have e : P ++ [] ++ (S ++ Q) = P ++ S ++ Q := by simp
    rw [xev_bub_ctx μ pre P (S ++ Q) E hpre hDB (hDs (d + 1)) (hDs d) e]
    have hT : ∀ n, xev cs μ w₀ (P ++ S ++ Q) (pre ++
        ((xDotsL A n).map (xwhL [] [l]) ++ xCapL l).map (xwhL P (S ++ Q))) ∈
        CapTarget D Sc cs μ w₀ (P ++ S ++ Q) (xcnt (mvLay ms) + S.length) := by
      intro n
      have := hIH P S Q l n hms hc
      convert this using 2
      simp [pre, capBlk, A]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (hT (d + 1)))
      (Submodule.smul_mem _ _ ?_)
    exact capTarget_comp_bubble_mid hS e (hT d) (isBubbleProd_oddBubble _ _)
  rcases S.eq_nil_or_concat' with rfl | ⟨S', s, rfl⟩
  · convert h₂ using 2
    simp [pre, capBlk, lmLc, A]
  · refine capT_of_xeq hF (c' := xcnt (mvLay ms) + S'.length)
      (L' := pre ++ ((xDotL l).map (xwhL [A] []) ++ (xDotsL A d).map (xwhL [] [l]) ++
        xCapL l).map (xwhL P (S' ++ [s] ++ Q))) (XEq.at (mvLay ms) []
      P Q (capBlk_dotB cs (wt D μ Q) (S' ++ [s]) l d) (hms.xChain.cast rfl (by simp [A])) ?_ ?_ ?_ ?_ (by simp))
      (by simp at hc ⊢; omega) (by simp) ?_
    · exact ((xChain_xDotL l).whisk ([A] ++ (S' ++ [s])) []).app (xChain_capBlk' (S' ++ [s]) l d)
        (by simp [A]) |>.cast (by simp [A]) rfl
    · exact ((xChain_lmLc (S' ++ [s]) l).whisk [A] []).app (hDB.whisk [] (S' ++ [s]))
        (by simp) |>.cast (by simp [A]) (by simp)
    · simp [A]
    · simp [pre, A]
    · exact h₂

/-- **The cap push past a dot.** -/
theorem push_dot (hS : BubbleSlideOut D Sc cs) {c : ℕ} {ms : List (Mv I)}
    (hF : LowHyp cs μ w₀ c) (hIH : PushHyp cs μ w₀ c ms) (u : List (Letter I)) (x : Letter I)
    (v : List (Letter I)) (hms : MvChain w₀ ms (Mv.dot u x v).src) :
    PushGoal cs μ w₀ c ms (Mv.dot u x v) := by
  intro P S Q l d ht hc
  have ht' : u ++ [x] ++ v = P ++ [flipL l] ++ S ++ [l] ++ Q := ht
  rcases posDot ht' with ⟨R, h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩ | ⟨S₁, S₂, h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ |
    ⟨R, h₁, h₂⟩
  · exact push_disjL hIH hms d R h₁ h₂ hc
  · subst u x v; exact push_dotA hIH d hms hc
  · subst S u v
    have hms' : MvChain w₀ ms (P ++ [flipL l] ++ (S₁ ++ [x] ++ S₂) ++ [l] ++ Q) := by
      convert hms using 1; simp [Mv.src, Mv.pre, Mv.lsrc, Mv.post]
    have := push_dotS hF hIH d hms' (by simpa [Mv.lay, Mv.loc] using hc)
    exact capTarget_mono cs (le_of_eq (by simp [Mv.lay, Mv.loc])) this
  · subst u x v
    have hms' : MvChain w₀ ms (P ++ [flipL l] ++ S ++ [l] ++ Q) := by
      convert hms using 1; simp [Mv.src, Mv.pre, Mv.lsrc, Mv.post]
    have := push_dotB hS hF hIH d hms' (by simpa [Mv.lay, Mv.loc] using hc)
    exact capTarget_mono cs (le_of_eq (by simp [Mv.lay, Mv.loc])) this
  · exact push_disjR hIH hms d R h₁ h₂ hc

end PushDot

end OddMath.SKM

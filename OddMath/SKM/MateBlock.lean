/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Mates

/-!
# Mates with respect to blocks of cups and caps

A generic form of the right mate of `OddMath.SKM.Mates`, in which the single cup `η` and cap `ε`
are replaced by arbitrary even diagrams `Cu : 1 → W' W` and `Ca : W W' → 1` (blocks of layers in
normal form). This is used for the mates of 2-morphisms between words with several strands
(`OddMath.SKM.MateN`), needed for the rotated relations of Brundan–Ellis, Lemmas 3.2 and 3.3.

* `mateB Cu A Ca Wa' Wb'`: the mate `Wb' → Wa'` of `A : Wa → Wb`: the block `Cu` on the left,
  `A` in the middle, the block `Ca` on the right;
* `cl_mateB_comp`: `mate(A) ≫ mate(B) = (-1)^{|A||B|} mate(B ≫ A)`, given the zigzag relation
  for the middle word;
* `cl_mateB_splitL`, `cl_mateB_splitR`: the mate of a 2-morphism acting on one part of a word,
  for nested blocks, given the zigzag relation for the other part;
* `cl_ixc`, `cl_ixc'`: the super interchange law for two blocks with explicit contexts.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

/-! ## Whiskered chains -/

theorem SChain.wh {s t : List (Letter I)} {L : List (LayerData I)} (h : SChain s L t)
    (u v : List (Letter I)) {s' t' : List (Letter I)} (hs : s' = u ++ s ++ v)
    (ht : t' = u ++ t ++ v) : SChain s' (L.map (whL u v)) t' := hs ▸ ht ▸ h.whisk u v

@[simp] theorem whL_comp_whL (u v u' v' : List (Letter I)) :
    whL u v ∘ whL u' v' = whL (u ++ u') (v' ++ v) :=
  funext fun x => whL_whL u v u' v' x

@[simp] theorem map_whL_nil_nil (L : List (LayerData I)) : L.map (whL [] []) = L := by
  have : whL [] [] = (id : LayerData I → LayerData I) := funext whL_nil_nil
  simp [this]

theorem zsign_mul_self (p : ZMod 2) : zsign k p * zsign k p = 1 := by
  rw [← zsign_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, zsign_zero]

/-! ## Interchange of blocks with contexts -/

/-- **Block interchange with contexts.** A block `A : s → s'` placed after the strands `u` and
a block `B : t → t'` placed further right (the strands `m` between them, `v` to the right of
`B`) can be exchanged, with the sign `(-1)^{|A||B|}`. -/
theorem cl_ixc {μ : X} {S T : List (Letter I)} (pre post : List (LayerData I))
    (u m v : List (Letter I)) {s s' t t' : List (Letter I)} {A B : List (LayerData I)}
    (hA : SChain s A s') (hB : SChain t B t') :
    cl D Sc μ S T (pre ++ A.map (whL u (m ++ t ++ v)) ++ B.map (whL (u ++ s' ++ m) v) ++ post) =
      zsign k (parsum D A * parsum D B) •
        cl D Sc μ S T (pre ++ B.map (whL (u ++ s ++ m) v) ++ A.map (whL u (m ++ t' ++ v)) ++
          post) := by
  have E := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := S) (T := T) pre post
    (hA.whisk u m) (hB.whisk [] v)
  simpa only [map_whL_map_whL, parsum_map_whL, List.append_assoc, List.nil_append,
    List.append_nil] using E

/-- Block interchange with contexts, the right block first. -/
theorem cl_ixc' {μ : X} {S T : List (Letter I)} (pre post : List (LayerData I))
    (u m v : List (Letter I)) {s s' t t' : List (Letter I)} {A B : List (LayerData I)}
    (hA : SChain s A s') (hB : SChain t B t') :
    cl D Sc μ S T (pre ++ B.map (whL (u ++ s ++ m) v) ++ A.map (whL u (m ++ t' ++ v)) ++ post) =
      zsign k (parsum D A * parsum D B) •
        cl D Sc μ S T (pre ++ A.map (whL u (m ++ t ++ v)) ++ B.map (whL (u ++ s' ++ m) v) ++
          post) := by
  rw [cl_ixc pre post u m v hA hB, smul_smul, zsign_mul_self, one_smul]

/-- Block interchange with contexts, for an even block. -/
theorem cl_ixc_even {μ : X} {S T : List (Letter I)} (pre post : List (LayerData I))
    (u m v : List (Letter I)) {s s' t t' : List (Letter I)} {A B : List (LayerData I)}
    (hA : SChain s A s') (hB : SChain t B t') (h : parsum D A = 0 ∨ parsum D B = 0) :
    cl D Sc μ S T (pre ++ A.map (whL u (m ++ t ++ v)) ++ B.map (whL (u ++ s' ++ m) v) ++ post) =
      cl D Sc μ S T (pre ++ B.map (whL (u ++ s ++ m) v) ++ A.map (whL u (m ++ t' ++ v)) ++
          post) := by
  rw [cl_ixc pre post u m v hA hB]
  rcases h with h | h <;> simp [h, zsign_zero]

/-! ## Mates with respect to blocks -/

/-- The mate `Wb' → Wa'` of `A : Wa → Wb` with respect to the blocks `Cu : 1 → Wa' Wa` and
`Ca : Wb Wb' → 1`. -/
def mateB (Cu A Ca : List (LayerData I)) (Wa' Wb' : List (Letter I)) : List (LayerData I) :=
  Cu.map (whL [] Wb') ++ A.map (whL Wa' Wb') ++ Ca.map (whL Wa' [])

theorem sChain_mateB {Cu A Ca : List (LayerData I)} {Wa Wb Wa' Wb' : List (Letter I)}
    (hCu : SChain [] Cu (Wa' ++ Wa)) (hA : SChain Wa A Wb) (hCa : SChain (Wb ++ Wb') Ca []) :
    SChain Wb' (mateB Cu A Ca Wa' Wb') Wa' :=
  ((hCu.wh [] Wb' (by simp) (by simp)).append (t' := Wa' ++ Wa ++ Wb')
    (hA.wh Wa' Wb' (by simp) rfl)).append (hCa.wh Wa' [] (by simp) (by simp))

theorem parsum_mateB {Cu A Ca : List (LayerData I)} (Wa' Wb' : List (Letter I))
    (hCu : parsum D Cu = 0) (hCa : parsum D Ca = 0) :
    parsum D (mateB Cu A Ca Wa' Wb') = parsum D A := by
  simp [mateB, parsum_append, hCu, hCa]

/-- The zigzag relation `(W ⊗ Cu) ≫ (Ca ⊗ W) = 1_W` for blocks `Cu : 1 → W' W`,
`Ca : W W' → 1`, at every weight. -/
def ZigE (D : Datum I X) (Sc : Scalars D k) (Cu Ca : List (LayerData I)) (W : List (Letter I)) :
    Prop :=
  ∀ μ : X, cl D Sc μ W W (Cu.map (whL W []) ++ Ca.map (whL [] W)) = cl D Sc μ W W []

/-- The zigzag relation `(Cu ⊗ W') ≫ (W' ⊗ Ca) = 1_{W'}` for blocks `Cu : 1 → W' W`,
`Ca : W W' → 1`, at every weight. -/
def ZigF (D : Datum I X) (Sc : Scalars D k) (Cu Ca : List (LayerData I)) (W' : List (Letter I)) :
    Prop :=
  ∀ μ : X, cl D Sc μ W' W' (Cu.map (whL [] W') ++ Ca.map (whL W' [])) = cl D Sc μ W' W' []

/-- Apply a zigzag relation `ZigE` in context. -/
theorem cl_zigE_ctx {Cu Ca : List (LayerData I)} {W : List (Letter I)} (hz : ZigE D Sc Cu Ca W)
    (μ : X)
    {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I)) (u v : List (Letter I))
    (hpre : SChain s₀ pre (u ++ W ++ v)) (hpost : SChain (u ++ W ++ v) post t₀) :
    cl D Sc μ s₀ t₀ (pre ++ Cu.map (whL (u ++ W) v) ++ Ca.map (whL u (W ++ v)) ++ post) =
      cl D Sc μ s₀ t₀ (pre ++ post) := by
  have := cl_step (D := D) (Sc := Sc) μ pre post u v (hz (wt D μ v)) hpre hpost
    (L := pre ++ Cu.map (whL (u ++ W) v) ++ Ca.map (whL u (W ++ v)) ++ post) (L' := pre ++ post)
    (by simp [List.append_assoc]) (by simp)
  exact this

/-- Apply a zigzag relation `ZigF` in context. -/
theorem cl_zigF_ctx {Cu Ca : List (LayerData I)} {W' : List (Letter I)}
    (hz : ZigF D Sc Cu Ca W') (μ : X)
    {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I)) (u v : List (Letter I))
    (hpre : SChain s₀ pre (u ++ W' ++ v)) (hpost : SChain (u ++ W' ++ v) post t₀) :
    cl D Sc μ s₀ t₀ (pre ++ Cu.map (whL u (W' ++ v)) ++ Ca.map (whL (u ++ W') v) ++ post) =
      cl D Sc μ s₀ t₀ (pre ++ post) := by
  have := cl_step (D := D) (Sc := Sc) μ pre post u v (hz (wt D μ v)) hpre hpost
    (L := pre ++ Cu.map (whL u (W' ++ v)) ++ Ca.map (whL (u ++ W') v) ++ post) (L' := pre ++ post)
    (by simp [List.append_assoc]) (by simp)
  exact this

variable (Sc) in
/-- **Composition of mates**: `mate(A) ≫ mate(B) = (-1)^{|A||B|} mate(B ≫ A)` for
`A : W₁ → W₂`, `B : W₀ → W₁`, given even blocks and the zigzag relation for `W₁`. -/
theorem cl_mateB_comp (μ : X) {W₀ W₁ W₂ W₀' W₁' W₂' : List (Letter I)}
    {Cu₀ Cu₁ Ca₁ Ca₂ A B : List (LayerData I)}
    (hCu₀ : SChain [] Cu₀ (W₀' ++ W₀)) (hCu₁ : SChain [] Cu₁ (W₁' ++ W₁))
    (hCa₁ : SChain (W₁ ++ W₁') Ca₁ []) (hCa₂ : SChain (W₂ ++ W₂') Ca₂ [])
    (hA : SChain W₁ A W₂) (hB : SChain W₀ B W₁)
    (eCu₀ : parsum D Cu₀ = 0) (eCu₁ : parsum D Cu₁ = 0) (eCa₁ : parsum D Ca₁ = 0)
    (eCa₂ : parsum D Ca₂ = 0) (hz : ZigE D Sc Cu₁ Ca₁ W₁) :
    cl D Sc μ W₂' W₀' (mateB Cu₁ A Ca₂ W₁' W₂' ++ mateB Cu₀ B Ca₁ W₀' W₁') =
      zsign k (parsum D A * parsum D B) • cl D Sc μ W₂' W₀' (mateB Cu₀ (B ++ A) Ca₂ W₀' W₂') := by
  have hM := sChain_mateB hCu₁ hA hCa₂
  -- Step 1: `Cu₀` moves to the bottom.
  have s1 : cl D Sc μ W₂' W₀' (mateB Cu₁ A Ca₂ W₁' W₂' ++ mateB Cu₀ B Ca₁ W₀' W₁') =
      cl D Sc μ W₂' W₀' (Cu₀.map (whL [] W₂') ++ (mateB Cu₁ A Ca₂ W₁' W₂').map (whL (W₀' ++ W₀) [])
        ++ B.map (whL W₀' W₁') ++ Ca₁.map (whL W₀' [])) := by
    have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := W₂') (T := W₀') []
      (B.map (whL W₀' W₁') ++ Ca₁.map (whL W₀' [])) [] [] [] hCu₀ hM (Or.inl eCu₀)
    simp only [List.nil_append, List.append_nil] at E
    convert E.symm using 2 <;> simp [mateB, List.append_assoc]
  -- Step 2: `B` moves below the mate of `A`.
  have s2 : cl D Sc μ W₂' W₀' (Cu₀.map (whL [] W₂') ++
        (mateB Cu₁ A Ca₂ W₁' W₂').map (whL (W₀' ++ W₀) []) ++ B.map (whL W₀' W₁') ++
        Ca₁.map (whL W₀' [])) =
      zsign k (parsum D A * parsum D B) • cl D Sc μ W₂' W₀' (Cu₀.map (whL [] W₂') ++
        B.map (whL W₀' W₂') ++ (mateB Cu₁ A Ca₂ W₁' W₂').map (whL (W₀' ++ W₁) []) ++
        Ca₁.map (whL W₀' [])) := by
    have E := cl_ixc' (D := D) (Sc := Sc) (μ := μ) (S := W₂') (T := W₀') (Cu₀.map (whL [] W₂'))
      (Ca₁.map (whL W₀' [])) W₀' [] [] hB hM
    simp only [List.nil_append, List.append_nil, parsum_mateB W₁' W₂' eCu₁ eCa₂] at E
    rw [E, mul_comm]
  -- Step 3: `Ca₁` moves below `A` and `Ca₂`.
  have hR : SChain (W₁ ++ W₂') (A.map (whL [] W₂') ++ Ca₂) [] :=
    (hA.wh [] W₂' (by simp) (by simp)).append hCa₂
  have s3 : cl D Sc μ W₂' W₀' (Cu₀.map (whL [] W₂') ++
        B.map (whL W₀' W₂') ++ (mateB Cu₁ A Ca₂ W₁' W₂').map (whL (W₀' ++ W₁) []) ++
        Ca₁.map (whL W₀' [])) =
      cl D Sc μ W₂' W₀' (Cu₀.map (whL [] W₂') ++ B.map (whL W₀' W₂') ++
        Cu₁.map (whL (W₀' ++ W₁) W₂') ++ Ca₁.map (whL W₀' (W₁ ++ W₂')) ++
        (A.map (whL [] W₂') ++ Ca₂).map (whL W₀' [])) := by
    have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := W₂') (T := W₀')
      (Cu₀.map (whL [] W₂') ++ B.map (whL W₀' W₂') ++ Cu₁.map (whL (W₀' ++ W₁) W₂')) []
      W₀' [] [] hCa₁ hR (Or.inl eCa₁)
    simp only [List.nil_append, List.append_nil] at E
    rw [E]
    congr 1
    simp [mateB, List.append_assoc]
  -- Step 4: the zigzag relation for `W₁`.
  have s4 : cl D Sc μ W₂' W₀' (Cu₀.map (whL [] W₂') ++ B.map (whL W₀' W₂') ++
        Cu₁.map (whL (W₀' ++ W₁) W₂') ++ Ca₁.map (whL W₀' (W₁ ++ W₂')) ++
        (A.map (whL [] W₂') ++ Ca₂).map (whL W₀' [])) =
      cl D Sc μ W₂' W₀' (mateB Cu₀ (B ++ A) Ca₂ W₀' W₂') := by
    rw [cl_zigE_ctx hz μ _ _ W₀' W₂'
      ((hCu₀.wh [] W₂' (by simp) (by simp)).append (t' := W₀' ++ W₀ ++ W₂')
        (hB.wh W₀' W₂' (by simp) rfl))
      (hR.wh W₀' [] (by simp) (by simp))]
    simp [mateB, List.append_assoc]
  rw [s1, s2, s3, s4]

variable (Sc) in
/-- **Mates of 2-morphisms on the left part of a word.** For nested blocks
`Cu = CuR ++ (CuL placed inside)`, `Ca = (CaR placed inside) ++ CaL`, the mate of `A₀ ⊗ 1_{WR}`
is `1_{WR'} ⊗ mate(A₀)`, given the zigzag relation for `WR'`. -/
theorem cl_mateB_splitL (μ : X) {WL₁ WL₂ WR WL₁' WL₂' WR' : List (Letter I)}
    {CuR CuL CaR CaL A₀ : List (LayerData I)}
    (hCuL : SChain [] CuL (WL₁' ++ WL₁)) (hCaR : SChain (WR ++ WR') CaR [])
    (hA₀ : SChain WL₁ A₀ WL₂) (hCaL : SChain (WL₂ ++ WL₂') CaL [])
    (eCaR : parsum D CaR = 0) (hz : ZigF D Sc CuR CaR WR') :
    cl D Sc μ (WR' ++ WL₂') (WR' ++ WL₁')
        (mateB (CuR ++ CuL.map (whL WR' WR)) (A₀.map (whL [] WR))
          (CaR.map (whL WL₂ WL₂') ++ CaL) (WR' ++ WL₁') (WR' ++ WL₂')) =
      cl D Sc μ (WR' ++ WL₂') (WR' ++ WL₁') ((mateB CuL A₀ CaL WL₁' WL₂').map (whL WR' [])) := by
  have hQ : SChain [] (CuL ++ A₀.map (whL WL₁' [])) (WL₁' ++ WL₂) :=
    hCuL.append (hA₀.wh WL₁' [] (by simp) (by simp))
  have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := WR' ++ WL₂') (T := WR' ++ WL₁')
    (CuR.map (whL [] (WR' ++ WL₂'))) (CaL.map (whL (WR' ++ WL₁') [])) WR' [] WL₂' hQ hCaR
    (Or.inr eCaR)
  simp only [List.nil_append, List.append_nil] at E
  have e1 : mateB (CuR ++ CuL.map (whL WR' WR)) (A₀.map (whL [] WR))
      (CaR.map (whL WL₂ WL₂') ++ CaL) (WR' ++ WL₁') (WR' ++ WL₂') =
      CuR.map (whL [] (WR' ++ WL₂')) ++ (CuL ++ A₀.map (whL WL₁' [])).map
        (whL WR' (WR ++ WR' ++ WL₂')) ++ CaR.map (whL (WR' ++ (WL₁' ++ WL₂)) WL₂') ++
        CaL.map (whL (WR' ++ WL₁') []) := by
    simp [mateB, List.append_assoc]
  rw [e1, E]
  have hpost : SChain (WR' ++ WL₂') ((CuL ++ A₀.map (whL WL₁' [])).map (whL WR' WL₂') ++
      CaL.map (whL (WR' ++ WL₁') [])) (WR' ++ WL₁') :=
    SChain.append (t' := WR' ++ (WL₁' ++ WL₂) ++ WL₂') (hQ.wh WR' WL₂' (by simp) rfl)
      (hCaL.wh (WR' ++ WL₁') [] (by simp) (by simp))
  have Z := cl_zigF_ctx (D := D) (Sc := Sc) hz μ [] _ [] WL₂' rfl (by simpa using hpost)
  simp only [mateB, List.map_append, List.map_map, whL_comp_whL, List.append_assoc,
    List.nil_append, List.append_nil] at Z ⊢
  exact Z

variable (Sc) in
/-- **Mates of 2-morphisms on the right part of a word.** For nested blocks, the mate of
`1_{WL} ⊗ A₀` is `mate(A₀) ⊗ 1_{WL'}`, given the zigzag relation for `WL'`. -/
theorem cl_mateB_splitR (μ : X) {WL WR₁ WR₂ WL' WR₁' WR₂' : List (Letter I)}
    {CuR CuL CaR CaL A₀ : List (LayerData I)}
    (hCuR : SChain [] CuR (WR₁' ++ WR₁)) (hCuL : SChain [] CuL (WL' ++ WL))
    (hA₀ : SChain WR₁ A₀ WR₂) (hCaR : SChain (WR₂ ++ WR₂') CaR [])
    (eCuL : parsum D CuL = 0) (hz : ZigF D Sc CuL CaL WL') :
    cl D Sc μ (WR₂' ++ WL') (WR₁' ++ WL')
        (mateB (CuR ++ CuL.map (whL WR₁' WR₁)) (A₀.map (whL WL []))
          (CaR.map (whL WL WL') ++ CaL) (WR₁' ++ WL') (WR₂' ++ WL')) =
      cl D Sc μ (WR₂' ++ WL') (WR₁' ++ WL') ((mateB CuR A₀ CaR WR₁' WR₂').map (whL [] WL')) := by
  have hP : SChain (WR₁ ++ WR₂') (A₀.map (whL [] WR₂') ++ CaR) [] :=
    (hA₀.wh [] WR₂' (by simp) (by simp)).append hCaR
  have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := WR₂' ++ WL') (T := WR₁' ++ WL')
    (CuR.map (whL [] (WR₂' ++ WL'))) (CaL.map (whL (WR₁' ++ WL') [])) WR₁' [] WL' hCuL hP
    (Or.inl eCuL)
  simp only [List.nil_append, List.append_nil] at E
  have e1 : mateB (CuR ++ CuL.map (whL WR₁' WR₁)) (A₀.map (whL WL []))
      (CaR.map (whL WL WL') ++ CaL) (WR₁' ++ WL') (WR₂' ++ WL') =
      CuR.map (whL [] (WR₂' ++ WL')) ++ CuL.map (whL WR₁' (WR₁ ++ WR₂' ++ WL')) ++
        (A₀.map (whL [] WR₂') ++ CaR).map (whL (WR₁' ++ (WL' ++ WL)) WL') ++
        CaL.map (whL (WR₁' ++ WL') []) := by
    simp [mateB, List.append_assoc]
  rw [e1, E]
  have hpre : SChain (WR₂' ++ WL') (CuR.map (whL [] (WR₂' ++ WL')) ++
      (A₀.map (whL [] WR₂') ++ CaR).map (whL WR₁' WL')) (WR₁' ++ WL') :=
    SChain.append (t' := WR₁' ++ (WR₁ ++ WR₂') ++ WL') (hCuR.wh [] (WR₂' ++ WL') (by simp)
      (by simp)) (hP.wh WR₁' WL' rfl (by simp))
  have Z := cl_zigF_ctx (D := D) (Sc := Sc) hz μ _ [] WR₁' [] (by simpa using hpre)
    (show SChain (WR₁' ++ WL' ++ []) [] (WR₁' ++ WL') by simp)
  simp only [mateB, List.map_append, List.map_map, whL_comp_whL, List.append_assoc,
    List.nil_append, List.append_nil] at Z ⊢
  exact Z

end OddMath.SKM

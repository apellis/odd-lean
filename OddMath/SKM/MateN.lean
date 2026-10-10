/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.MateBlock

/-!
# Mates of 2-morphisms between upward words

The right mate of a 2-morphism `A : E_w → E_{w'}` between words of upward strands, with respect to
nested rightward cups and caps: `mateN w w' A : F_{w'}^∨ → F_w^∨`, where `F_w^∨` is the word of
downward strands of `w` in the reverse order. For one strand this is `mateL`
(`OddMath.SKM.Mates`); the downward crossing (2.1) is the mate of the upward crossing
(`dcrossL_eq_mateN`).

* `ups w`, `dns w`: the words `E_w` and `F_w^∨`; `cupN w : 1 → F_w^∨ E_w` (nested rightward cups,
  the outermost for the last letter), `capN w : E_w F_w^∨ → 1`;
* `zigE_N`, `zigF_N`: the zigzag relations for the nested cups and caps;
* `cl_mateN_comp`: `mate(A) ≫ mate(B) = (-1)^{|A||B|} mate(B ≫ A)`;
* `cl_mateN_whiskerR`, `cl_mateN_whiskerL`: the mate of `A ⊗ 1` is `1 ⊗ mate(A)` and the mate of
  `1 ⊗ A` is `mate(A) ⊗ 1`.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

/-! ## Words, nested cups and caps -/

/-- The word of upward strands `E_w`. -/
def ups (w : List I) : List (Letter I) := w.map up

/-- The word of downward strands `F_w^∨` (the letters of `w` in the reverse order). -/
def dns (w : List I) : List (Letter I) := (w.map dn).reverse

@[simp] theorem ups_nil : ups ([] : List I) = [] := rfl
@[simp] theorem ups_cons (a : I) (w : List I) : ups (a :: w) = up a :: ups w := rfl
@[simp] theorem dns_nil : dns ([] : List I) = [] := rfl
@[simp] theorem dns_cons (a : I) (w : List I) : dns (a :: w) = dns w ++ [dn a] := by
  simp [dns]

theorem ups_append (w w' : List I) : ups (w ++ w') = ups w ++ ups w' := by simp [ups]
theorem dns_append (w w' : List I) : dns (w ++ w') = dns w' ++ dns w := by simp [dns]

/-- Nested rightward cups `1 → F_w^∨ E_w`: the cup of the last letter is outermost. -/
def cupN : List I → List (LayerData I)
  | [] => []
  | a :: w => cupN w ++ [(dns w, Shape.cup a, ups w)]

/-- Nested rightward caps `E_w F_w^∨ → 1`: the cap of the first letter is outermost. -/
def capN : List I → List (LayerData I)
  | [] => []
  | a :: w => (capN w).map (whL [up a] [dn a]) ++ [([], Shape.cap a, [])]

theorem sChain_cupN (w : List I) : SChain [] (cupN w) (dns w ++ ups w) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    exact ih.append (t' := dns w ++ ups w) ⟨by simp [Shape.dom], by simp [Shape.cod]⟩

theorem sChain_capN (w : List I) : SChain (ups w ++ dns w) (capN w) [] := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    exact SChain.append (t' := [up a] ++ [] ++ [dn a]) (ih.wh [up a] [dn a] (by simp) rfl)
      ⟨by simp [Shape.dom], by simp [Shape.cod]⟩

theorem parsum_cupN (w : List I) : parsum D (cupN w) = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [cupN, parsum_append, ih, Shape.parity]

theorem parsum_capN (w : List I) : parsum D (capN w) = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [capN, parsum_append, ih, Shape.parity]

theorem cupN_append (w w' : List I) :
    cupN (w ++ w') = cupN w' ++ (cupN w).map (whL (dns w') (ups w')) := by
  induction w with
  | nil => simp [cupN]
  | cons a w ih => simp [cupN, ih, whL, dns_append, ups_append, List.append_assoc]

theorem capN_append (w w' : List I) :
    capN (w ++ w') = (capN w').map (whL (ups w) (dns w)) ++ capN w := by
  induction w with
  | nil => simp [capN]
  | cons a w ih => simp [capN, ih, List.append_assoc]

/-! ## Zigzag relations -/

variable (Sc) in
theorem zigE_one (a : I) : ZigE D Sc (cupN [a]) (capN [a]) (ups [a]) := by
  intro μ
  simpa [cupN, capN, whL] using cl_zigE Sc a μ

variable (Sc) in
theorem zigF_one (a : I) : ZigF D Sc (cupN [a]) (capN [a]) (dns [a]) := by
  intro μ
  show cl D Sc μ [dn a] [dn a] ((cupN [a]).map (whL [] [dn a]) ++ (capN [a]).map (whL [dn a] [])) =
    cl D Sc μ [dn a] [dn a] []
  simpa [cupN, capN, whL] using cl_zigF Sc a μ

variable (Sc) in
/-- The zigzag relation `(E_w ⊗ cupN) ≫ (capN ⊗ E_w) = 1`. -/
theorem zigE_N (w : List I) : ZigE D Sc (cupN w) (capN w) (ups w) := by
  induction w with
  | nil => intro μ; simp [cupN, capN]
  | cons a w ih =>
    intro μ
    -- the cup of `a` moves below the caps of `w`
    have E := cl_ixc' (D := D) (Sc := Sc) (μ := μ) (S := ups (a :: w)) (T := ups (a :: w))
      ((cupN w).map (whL (ups (a :: w)) [])) [([], Shape.cap a, ups (a :: w))] [up a] [] (ups w)
      (sChain_capN w) (B := [([], Shape.cup a, [])]) (t := []) (t' := [dn a, up a])
      ⟨rfl, rfl⟩
    simp only [parsum_capN, zero_mul, zsign_zero, one_smul] at E
    have e1 : (cupN (a :: w)).map (whL (ups (a :: w)) []) ++ (capN (a :: w)).map (whL [] (ups (a :: w))) =
        (cupN w).map (whL (ups (a :: w)) []) ++ [([], Shape.cup a, [])].map
          (whL ([up a] ++ (ups w ++ dns w) ++ []) (ups w)) ++
          (capN w).map (whL [up a] ([] ++ [dn a, up a] ++ ups w)) ++
          [([], Shape.cap a, ups (a :: w))] := by
      simp [cupN, capN, whL, List.append_assoc]
    rw [e1, E]
    have Z1 := cl_zigE_ctx (s₀ := ups (a :: w)) (t₀ := ups (a :: w)) ih μ []
      [([up a], Shape.cup a, ups w), ([], Shape.cap a, up a :: ups w)] [up a] [] (by simp)
      (by simp [Shape.dom, Shape.cod])
    have Z2 := cl_zigE_ctx (s₀ := ups (a :: w)) (t₀ := ups (a :: w)) (zigE_one Sc a) μ [] []
      [] (ups w) (by simp) (by simp)
    convert Z1.trans Z2 using 2 <;> simp [whL, List.append_assoc]

variable (Sc) in
/-- The zigzag relation `(cupN ⊗ F_w^∨) ≫ (F_w^∨ ⊗ capN) = 1`. -/
theorem zigF_N (w : List I) : ZigF D Sc (cupN w) (capN w) (dns w) := by
  induction w with
  | nil => intro μ; simp [cupN, capN]
  | cons a w ih =>
    intro μ
    -- the caps of `w` move below the cup of `a`
    have E := cl_ixc (D := D) (Sc := Sc) (μ := μ) (S := dns (a :: w)) (T := dns (a :: w))
      ((cupN w).map (whL [] (dns (a :: w)))) [(dns w ++ [dn a], Shape.cap a, [])] (dns w) []
      [dn a] (A := [([], Shape.cup a, [])]) (s := []) (s' := [dn a, up a]) ⟨rfl, rfl⟩
      (sChain_capN w)
    simp only [parsum_capN, mul_zero, zsign_zero, one_smul] at E
    have e1 : (cupN (a :: w)).map (whL [] (dns (a :: w))) ++ (capN (a :: w)).map (whL (dns (a :: w)) []) =
        (cupN w).map (whL [] (dns (a :: w))) ++ [([], Shape.cup a, [])].map
          (whL (dns w) ([] ++ (ups w ++ dns w) ++ [dn a])) ++
          (capN w).map (whL (dns w ++ [dn a, up a] ++ []) [dn a]) ++
          [(dns w ++ [dn a], Shape.cap a, [])] := by
      simp [cupN, capN, whL, List.append_assoc]
    rw [e1, E]
    have Z1 := cl_zigF_ctx (s₀ := dns (a :: w)) (t₀ := dns (a :: w)) ih μ []
      [(dns w, Shape.cup a, [dn a]), (dns w ++ [dn a], Shape.cap a, [])] [] [dn a] (by simp)
      (by simp [Shape.dom, Shape.cod])
    have Z2 := cl_zigF_ctx (s₀ := dns (a :: w)) (t₀ := dns (a :: w)) (zigF_one Sc a) μ [] []
      (dns w) [] (by simp) (by simp)
    have e2 : ([] ++ [(dns w, Shape.cup a, [dn a]), (dns w ++ [dn a], Shape.cap a, [])] :
        List (LayerData I)) = [] ++ (cupN [a]).map (whL (dns w) (dns [a] ++ [])) ++
          (capN [a]).map (whL (dns w ++ dns [a]) []) ++ [] := by
      simp [cupN, capN, whL]
    rw [e2] at Z1
    convert Z1.trans Z2 using 2 <;> simp [whL, List.append_assoc]

/-! ## Mates -/

/-- The mate `F_{w'}^∨ → F_w^∨` of `A : E_w → E_{w'}`. -/
def mateN (w w' : List I) (A : List (LayerData I)) : List (LayerData I) :=
  mateB (cupN w) A (capN w') (dns w) (dns w')

theorem sChain_mateN {w w' : List I} {A : List (LayerData I)} (hA : SChain (ups w) A (ups w')) :
    SChain (dns w') (mateN w w' A) (dns w) :=
  sChain_mateB (sChain_cupN w) hA (sChain_capN w')

theorem parsum_mateN (w w' : List I) (A : List (LayerData I)) :
    parsum D (mateN w w' A) = parsum D A :=
  parsum_mateB _ _ (parsum_cupN w) (parsum_capN w')

/-- The mate of a single-strand 2-morphism is `mateL`. -/
theorem mateN_one (a : I) (A : List (LayerData I)) : mateN [a] [a] A = mateL a A := by
  simp [mateN, mateB, mateL, cupN, capN, whL]

/-- The downward crossing (2.1) is the mate of the upward crossing. -/
theorem dcrossL_eq_mateN (i j : I) : dcrossL i j = mateN [i, j] [j, i] (crossL [] i j []) := by
  simp [dcrossL, mateN, mateB, cupN, capN, sigmaL, crossL, whL]

variable (Sc) in
/-- **Composition of mates**: `mate(A) ≫ mate(B) = (-1)^{|A||B|} mate(B ≫ A)`. -/
theorem cl_mateN_comp (μ : X) {w₀ w₁ w₂ : List I} {A B : List (LayerData I)}
    (hA : SChain (ups w₁) A (ups w₂)) (hB : SChain (ups w₀) B (ups w₁)) :
    cl D Sc μ (dns w₂) (dns w₀) (mateN w₁ w₂ A ++ mateN w₀ w₁ B) =
      zsign k (parsum D A * parsum D B) • cl D Sc μ (dns w₂) (dns w₀) (mateN w₀ w₂ (B ++ A)) :=
  cl_mateB_comp Sc μ (sChain_cupN w₀) (sChain_cupN w₁) (sChain_capN w₁) (sChain_capN w₂) hA hB
    (parsum_cupN w₀) (parsum_cupN w₁) (parsum_capN w₁) (parsum_capN w₂) (zigE_N Sc w₁)

variable (Sc) in
/-- The mate of `A ⊗ 1_{E_v}` is `1_{F_v^∨} ⊗ mate(A)`. -/
theorem cl_mateN_whiskerR (μ : X) {w w' : List I} (v : List I) {A : List (LayerData I)}
    (hA : SChain (ups w) A (ups w')) :
    cl D Sc μ (dns (w' ++ v)) (dns (w ++ v)) (mateN (w ++ v) (w' ++ v) (A.map (whL [] (ups v)))) =
      cl D Sc μ (dns (w' ++ v)) (dns (w ++ v)) ((mateN w w' A).map (whL (dns v) [])) := by
  have := cl_mateB_splitL Sc μ (CuR := cupN v) (sChain_cupN w) (sChain_capN v) hA (sChain_capN w')
    (parsum_capN v) (zigF_N Sc v)
  rw [dns_append, dns_append]
  simpa only [mateN, cupN_append, capN_append, dns_append] using this

variable (Sc) in
/-- The mate of `1_{E_v} ⊗ A` is `mate(A) ⊗ 1_{F_v^∨}`. -/
theorem cl_mateN_whiskerL (μ : X) (v : List I) {w w' : List I} {A : List (LayerData I)}
    (hA : SChain (ups w) A (ups w')) :
    cl D Sc μ (dns (v ++ w')) (dns (v ++ w)) (mateN (v ++ w) (v ++ w') (A.map (whL (ups v) []))) =
      cl D Sc μ (dns (v ++ w')) (dns (v ++ w)) ((mateN w w' A).map (whL [] (dns v))) := by
  have := cl_mateB_splitR Sc μ (CaL := capN v) (sChain_cupN w) (sChain_cupN v) hA (sChain_capN w')
    (parsum_cupN v) (zigF_N Sc v)
  rw [dns_append, dns_append]
  simpa only [mateN, cupN_append, capN_append, dns_append] using this

end OddMath.SKM

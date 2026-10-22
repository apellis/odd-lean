/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Realization.BraidEq
import StringDiagrams.LocalInterpretation

/-!
# The action of the quiver Hecke supercategory on the twisted module

Brundan–Ellis, arXiv:1701.04133v2, §11: the quiver Hecke supercategory `H` (the presentation
`QuiverHecke.pres`, relations (1.7)–(1.9)) acts on the twisted module of
Kang–Kashiwara–Tsuchioka, arXiv:1107.1039v2, Theorem 3.13. A word `t` goes to the component
of the colour sequence `p ↦ t[p]?`, a dot of colour `i` at list position `p` acts by
`dotOp D i p` and a crossing of colours `i`, `j` at positions `p`, `p + 1` by
`crossOp D Sc i j p`.

The relations hold by `Realization/Relations`, `Realization/Braid` and `Realization/BraidEq`;
the super interchange law holds because the operators at disjoint positions supercommute
(`SComm`).

Main declarations: `interp` (the local interpretation), `interp_rel` (every relation, whiskered,
acts by zero), `interp_interchange`, `respects`, and `rep`, the functor from the presented
supercategory `H` to `k`-modules.
-/

noncomputable section
open scoped TensorProduct
open Finset StringDiagrams
namespace OddMath.QuiverHecke.Realization

universe u v
variable {I : Type u} {X : Type v} [AddCommGroup X] {k : Type*} [CommRing k]

/-! ## Supercommutation -/

theorem zsign_add' (p q : ZMod 2) : SKM.zsign k (p + q) = SKM.zsign k p * SKM.zsign k q := by
  rcases parity_cases p with rfl | rfl <;> rcases parity_cases q with rfl | rfl
  · simp [SKM.zsign]
  · simp [SKM.zsign]
  · simp [SKM.zsign]
  · rw [show (1 : ZMod 2) + 1 = 0 by decide]; simp [SKM.zsign]

section SComm

variable {E : Type*} [Ring E] [Algebra k E]

variable (k) in
/-- `A B = (-1)^e B A`. -/
def SComm (A B : E) (e : ZMod 2) : Prop := A * B = SKM.zsign k e • (B * A)

variable {A A' B B' : E} {e e' : ZMod 2}

theorem SComm.congr (h : SComm k A B e) (he : e = e') : SComm k A B e' := he ▸ h

theorem SComm.mul_left (h : SComm k A B e) (h' : SComm k A' B e') :
    SComm k (A * A') B (e + e') := by
  unfold SComm at *
  rw [mul_assoc, h', mul_smul_comm, ← mul_assoc, h, smul_mul_assoc, smul_smul, mul_assoc,
    zsign_add', mul_comm]

theorem SComm.mul_right (h : SComm k A B e) (h' : SComm k A B' e') :
    SComm k A (B * B') (e + e') := by
  unfold SComm at *
  rw [← mul_assoc, h, smul_mul_assoc, mul_assoc, h', mul_smul_comm, smul_smul, ← mul_assoc,
    zsign_add']

theorem SComm.sub_left (h : SComm k A B e) (h' : SComm k A' B e) : SComm k (A - A') B e := by
  unfold SComm at *
  rw [sub_mul, h, h', mul_sub, smul_sub]

theorem SComm.sub_right (h : SComm k A B e) (h' : SComm k A B' e) : SComm k A (B - B') e := by
  unfold SComm at *
  rw [mul_sub, h, h', sub_mul, smul_sub]

theorem SComm.smul_left (c : k) (h : SComm k A B e) : SComm k (c • A) B e := by
  unfold SComm at *
  rw [smul_mul_assoc, h, mul_smul_comm, smul_comm]

theorem SComm.smul_right (c : k) (h : SComm k A B e) : SComm k A (c • B) e := by
  unfold SComm at *
  rw [mul_smul_comm, h, smul_mul_assoc, smul_comm]

theorem SComm.one_left (B : E) : SComm k (1 : E) B 0 := by
  simp [SComm, SKM.zsign]

theorem SComm.one_right (A : E) : SComm k A (1 : E) 0 := by
  simp [SComm, SKM.zsign]

theorem SComm.of_commute (h : Commute A B) : SComm k A B 0 := by
  simp [SComm, SKM.zsign, h.eq]

theorem SComm.of_anticomm (h : A * B = -(B * A)) : SComm k A B 1 := by
  simp [SComm, SKM.zsign, h]

end SComm

/-! ## Operators at disjoint positions supercommute -/

section Far

variable (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

theorem scomm_clif_clif {p q : ℕ} (h : p ≠ q) :
    SComm k (clif (k := k) (I := I) D.parity p) (clif D.parity q) 1 :=
  SComm.of_anticomm (clif_anticomm D.parity h)

theorem scomm_clif_Y {p q : ℕ} (h : p ≠ q) :
    SComm k (clif (k := k) (I := I) D.parity p) (Y q) 0 :=
  SComm.of_commute (clif_y_comm D.parity (Ne.symm h))

theorem scomm_Y_clif {p q : ℕ} (h : p ≠ q) :
    SComm k (Y (k := k) (I := I) p) (clif D.parity q) 0 :=
  SComm.of_commute (clif_y_comm D.parity h).symm

theorem scomm_Y_Y (p q : ℕ) : SComm k (Y (k := k) (I := I) p) (Y q) 0 :=
  SComm.of_commute (mulK_comm _ _)

/-- The Clifford factor of a crossing supercommutes with anything its two Clifford generators
supercommute with. -/
theorem SComm.dres_left {i j : I} {a : ℕ} {B : Module.End k (V k I)} {e : ZMod 2}
    (h₀ : SComm k (clif D.parity a) B e) (h₁ : SComm k (clif D.parity (a + 1)) B e)
    (h : SComm k (1 : Module.End k (V k I)) B 0) :
    SComm k (dres (k := k) D i j a) B (D.parity i * D.parity j * e) := by
  unfold dres
  split_ifs with hij
  · rw [hij.1, hij.2, one_mul, one_mul]; exact h₀.sub_left h₁
  · refine h.congr ?_
    rcases parity_cases (D.parity i) with hi | hi <;> rcases parity_cases (D.parity j) with hj | hj
    all_goals first | (exfalso; exact hij ⟨hi, hj⟩) | simp [hi, hj]

theorem SComm.dres_right {i j : I} {a : ℕ} {A : Module.End k (V k I)} {e : ZMod 2}
    (h₀ : SComm k A (clif D.parity a) e) (h₁ : SComm k A (clif D.parity (a + 1)) e)
    (h : SComm k A (1 : Module.End k (V k I)) 0) :
    SComm k A (dres (k := k) D i j a) (D.parity i * D.parity j * e) := by
  unfold dres
  split_ifs with hij
  · rw [hij.1, hij.2, one_mul, one_mul]; exact h₀.sub_right h₁
  · refine h.congr ?_
    rcases parity_cases (D.parity i) with hi | hi <;> rcases parity_cases (D.parity j) with hj | hj
    all_goals first | (exfalso; exact hij ⟨hi, hj⟩) | simp [hi, hj]

theorem SComm.dotOp_left {i : I} {p : ℕ} {B : Module.End k (V k I)} {e : ZMod 2}
    (hc : SComm k (clif D.parity p) B e) (hy : SComm k (Y (k := k) (I := I) p) B 0) :
    SComm k (dotOp (k := k) D i p) B (D.parity i * e) := by
  unfold dotOp
  split_ifs with hi
  · rw [hi, one_mul]; exact (hc.mul_left hy).congr (add_zero e)
  · rcases parity_cases (D.parity i) with h | h
    · rw [h, zero_mul]; exact hy
    · exact absurd h hi

theorem SComm.dotOp_right {i : I} {p : ℕ} {A : Module.End k (V k I)} {e : ZMod 2}
    (hc : SComm k A (clif D.parity p) e) (hy : SComm k A (Y (k := k) (I := I) p) 0) :
    SComm k A (dotOp (k := k) D i p) (D.parity i * e) := by
  unfold dotOp
  split_ifs with hi
  · rw [hi, one_mul]; exact (hc.mul_right hy).congr (add_zero e)
  · rcases parity_cases (D.parity i) with h | h
    · rw [h, zero_mul]; exact hy
    · exact absurd h hi

/-- A Clifford generator supercommutes with a dot at another position. -/
theorem scomm_clif_dotOp {j : I} {p q : ℕ} (h : p ≠ q) :
    SComm k (clif (k := k) (I := I) D.parity p) (dotOp D j q) (D.parity j) :=
  (SComm.dotOp_right D (scomm_clif_clif D h) (scomm_clif_Y D h)).congr (mul_one _)

theorem scomm_Y_dotOp {j : I} {p q : ℕ} (h : p ≠ q) :
    SComm k (Y (k := k) (I := I) p) (dotOp D j q) 0 :=
  (SComm.dotOp_right D (scomm_Y_clif D h) (scomm_Y_Y p q)).congr (mul_zero _)

variable [DecidableEq I]

theorem commute_sig_Y {a q : ℕ} (h₀ : q ≠ a) (h₁ : q ≠ a + 1) :
    Commute (sig D.parity (qt D Sc) a) (Y q) :=
  sig_mulK D.parity (qt D Sc) a _ (fun _ => by rw [permK_y, sw_apply_of_ne h₀ h₁])
    (fun _ _ => reflect_y_of_ne h₀) (fun _ _ => reflect_y_of_ne h₁)

theorem commute_sig_clif {a q : ℕ} (h₀ : q ≠ a) (h₁ : q ≠ a + 1) :
    Commute (sig D.parity (qt D Sc) a) (clif D.parity q) := by
  have := sig_clif D.parity (qt D Sc) (qt_isEven D Sc) a q
  rwa [sw_apply_of_ne h₀ h₁] at this

theorem SComm.crossOp_left {i j : I} {a : ℕ} {B : Module.End k (V k I)} {e : ZMod 2}
    (h₀ : SComm k (clif D.parity a) B e) (h₁ : SComm k (clif D.parity (a + 1)) B e)
    (h : SComm k (1 : Module.End k (V k I)) B 0)
    (hs : SComm k (sig D.parity (qt D Sc) a) B 0) :
    SComm k (crossOp (k := k) D Sc i j a) B (D.parity i * D.parity j * e) :=
  ((SComm.dres_left D h₀ h₁ h).mul_left hs).congr (add_zero _) |>.smul_left _

theorem SComm.crossOp_right {i j : I} {a : ℕ} {A : Module.End k (V k I)} {e : ZMod 2}
    (h₀ : SComm k A (clif D.parity a) e) (h₁ : SComm k A (clif D.parity (a + 1)) e)
    (h : SComm k A (1 : Module.End k (V k I)) 0)
    (hs : SComm k A (sig D.parity (qt D Sc) a) 0) :
    SComm k A (crossOp (k := k) D Sc i j a) (D.parity i * D.parity j * e) :=
  ((SComm.dres_right D h₀ h₁ h).mul_right hs).congr (add_zero _) |>.smul_right _

theorem scomm_clif_crossOp {j l : I} {p b : ℕ} (h₀ : p ≠ b) (h₁ : p ≠ b + 1) :
    SComm k (clif (k := k) (I := I) D.parity p) (crossOp D Sc j l b)
      (D.parity j * D.parity l) :=
  (SComm.crossOp_right D Sc (scomm_clif_clif D h₀) (scomm_clif_clif D h₁) (SComm.one_right _)
    (SComm.of_commute (commute_sig_clif D Sc h₀ h₁).symm)).congr
    (mul_one _)

theorem scomm_Y_crossOp {j l : I} {p b : ℕ} (h₀ : p ≠ b) (h₁ : p ≠ b + 1) :
    SComm k (Y (k := k) (I := I) p) (crossOp D Sc j l b) 0 :=
  (SComm.crossOp_right D Sc (scomm_Y_clif D h₀) (scomm_Y_clif D h₁) (SComm.one_right _)
    (SComm.of_commute (commute_sig_Y D Sc h₀ h₁).symm)).congr
    (mul_zero _)

theorem scomm_sig_dotOp {j : I} {a q : ℕ} (h₀ : q ≠ a) (h₁ : q ≠ a + 1) :
    SComm k (sig D.parity (qt D Sc) a) (dotOp (k := k) D j q) 0 :=
  (SComm.dotOp_right D (SComm.of_commute (commute_sig_clif D Sc h₀ h₁))
    (SComm.of_commute (commute_sig_Y D Sc h₀ h₁))).congr (mul_zero _)

theorem scomm_sig_crossOp {j l : I} {a b : ℕ} (hab : a + 1 < b ∨ b + 1 < a) :
    SComm k (sig D.parity (qt D Sc) a) (crossOp (k := k) D Sc j l b) 0 :=
  (SComm.crossOp_right D Sc
    (SComm.of_commute (commute_sig_clif D Sc (by omega) (by omega)))
    (SComm.of_commute (commute_sig_clif D Sc (by omega) (by omega))) (SComm.one_right _)
    (SComm.of_commute (sig_comm D.parity (qt D Sc) (qt_isEven D Sc) hab))).congr (mul_zero _)

omit [DecidableEq I] in
theorem scomm_dotOp_dotOp {i j : I} {p q : ℕ} (h : p ≠ q) :
    SComm k (dotOp (k := k) D i p) (dotOp D j q) (D.parity i * D.parity j) :=
  SComm.dotOp_left D (scomm_clif_dotOp D h) (scomm_Y_dotOp D h)

theorem scomm_dotOp_crossOp {i j l : I} {p b : ℕ} (h₀ : p ≠ b) (h₁ : p ≠ b + 1) :
    SComm k (dotOp (k := k) D i p) (crossOp D Sc j l b)
      (D.parity i * (D.parity j * D.parity l)) :=
  SComm.dotOp_left D (scomm_clif_crossOp D Sc h₀ h₁) (scomm_Y_crossOp D Sc h₀ h₁)

theorem scomm_crossOp_dotOp {i j l : I} {a q : ℕ} (h₀ : q ≠ a) (h₁ : q ≠ a + 1) :
    SComm k (crossOp (k := k) D Sc i j a) (dotOp D l q)
      (D.parity i * D.parity j * D.parity l) :=
  SComm.crossOp_left D Sc (scomm_clif_dotOp D (Ne.symm h₀)) (scomm_clif_dotOp D (Ne.symm h₁))
    (SComm.one_left _) (scomm_sig_dotOp D Sc h₀ h₁)

theorem scomm_crossOp_crossOp {i j l l' : I} {a b : ℕ} (hab : a + 1 < b ∨ b + 1 < a) :
    SComm k (crossOp (k := k) D Sc i j a) (crossOp D Sc l l' b)
      (D.parity i * D.parity j * (D.parity l * D.parity l')) :=
  SComm.crossOp_left D Sc (scomm_clif_crossOp D Sc (by omega) (by omega))
    (scomm_clif_crossOp D Sc (by omega) (by omega)) (SComm.one_left _)
    (scomm_sig_crossOp D Sc hab)

end Far

/-! ## Locality -/

section Local

variable {J : Type*}

/-- The component `ν` of `T x` depends only on the component `π ν` of `x`. -/
def DependsOn (T : Module.End k (V k J)) (π : Seq J → Seq J) : Prop :=
  ∀ x ν, x (π ν) = 0 → T x ν = 0

variable {T T' : Module.End k (V k J)} {π π' : Seq J → Seq J}

theorem DependsOn.add (h : DependsOn T π) (h' : DependsOn T' π) : DependsOn (T + T') π :=
  fun x ν hx => by rw [LinearMap.add_apply, Pi.add_apply, h x ν hx, h' x ν hx, add_zero]

theorem DependsOn.sub (h : DependsOn T π) (h' : DependsOn T' π) : DependsOn (T - T') π :=
  fun x ν hx => by rw [LinearMap.sub_apply, Pi.sub_apply, h x ν hx, h' x ν hx, sub_zero]

theorem DependsOn.smul (c : k) (h : DependsOn T π) : DependsOn (c • T) π :=
  fun x ν hx => by rw [LinearMap.smul_apply, Pi.smul_apply, h x ν hx, smul_zero]

theorem DependsOn.mul (h : DependsOn T π) (h' : DependsOn T' π') :
    DependsOn (T * T') (fun ν => π' (π ν)) :=
  fun x ν hx => h _ ν (h' x (π ν) hx)

theorem dependsOn_one : DependsOn (1 : Module.End k (V k J)) id := fun _ _ hx => hx

theorem dependsOn_diag (F : Seq J → Module.End k (Coeff k)) : DependsOn (diag F) id :=
  fun x ν hx => by rw [diag_apply]; simp only [id] at hx; rw [hx, map_zero]

theorem dependsOn_tw (a : ℕ) (r : Seq J → K k) : DependsOn (tw a r) (· ∘ sw a) :=
  fun x ν hx => by rw [tw_apply, hx, map_zero]

theorem comp_sw_of_eq {ν : Seq J} {a : ℕ} (h : ν a = ν (a + 1)) : ν ∘ sw a = ν := by
  ext1 p
  simp only [Function.comp_apply]
  by_cases h₀ : p = a
  · subst h₀; rw [sw_apply_left, h]
  · by_cases h₁ : p = a + 1
    · subst h₁; rw [sw_apply_right, h]
    · rw [sw_apply_of_ne h₀ h₁]

variable [DecidableEq J]

theorem dependsOn_fpq (par : J → ZMod 2) (a : ℕ) :
    DependsOn (fpq (k := k) par a (a + 1)) (· ∘ sw a) := fun x ν hx => by
  rw [fpq_eq_diag, diag_apply]
  by_cases h : ν a = ν (a + 1)
  · simp only [comp_sw_of_eq h] at hx
    rw [hx, map_zero]
  · rw [fP_eq_zero par h]; simp

theorem dependsOn_sig (par : J → ZMod 2) (Qt : PairFn J k) (a : ℕ) :
    DependsOn (sig par Qt a) (· ∘ sw a) :=
  (dependsOn_tw a _).add (dependsOn_fpq par a)

variable (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [DecidableEq I]

omit [DecidableEq I] in
theorem dependsOn_dotOp (i : I) (p : ℕ) : DependsOn (dotOp (k := k) D i p) id := by
  unfold dotOp
  split_ifs
  · exact (dependsOn_diag _).mul (dependsOn_diag _)
  · exact dependsOn_diag _

theorem dependsOn_crossOp (i j : I) (a : ℕ) :
    DependsOn (crossOp (k := k) D Sc i j a) (· ∘ sw a) := by
  have hd : DependsOn (dres (k := k) D i j a) id := by
    unfold dres
    split_ifs
    · exact (dependsOn_diag _).sub (dependsOn_diag _)
    · exact dependsOn_one
  exact (hd.mul (dependsOn_sig D.parity (qt D Sc) a)).smul _

end Local

/-! ## The interpretation -/

section Interp

variable (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [DecidableEq I]

/-- The colour sequence of a word: `p ↦ t[p]?`. -/
def seqOf (t : List I) : Seq I := fun p => t[p]?

/-- The operator of a layer: a dot or a crossing at the position given by its left context. -/
def layOp (L : Layer (QuiverHecke.sig D)) : Module.End k (V k I) :=
  match L.gen with
  | .dot i => dotOp D i L.left.length
  | .cross i j => crossOp D Sc i j L.left.length

omit [DecidableEq I] in
theorem seqOf_swap (l r : List I) (i j : I) :
    seqOf (l ++ [j, i] ++ r) ∘ sw l.length = seqOf (l ++ [i, j] ++ r) := by
  ext1 q
  simp only [seqOf, Function.comp_apply, List.append_assoc]
  rcases lt_trichotomy q l.length with h | h | h
  · rw [sw_apply_of_ne (by omega) (by omega), List.getElem?_append_left h,
      List.getElem?_append_left h]
  · subst h
    rw [sw_apply_left, List.getElem?_append_right (show l.length ≤ l.length + 1 by omega),
      List.getElem?_append_right (le_refl _)]
    simp
  · rcases Nat.lt_or_ge (l.length + 1) q with h' | h'
    · rw [sw_apply_of_ne (by omega) (by omega), List.getElem?_append_right (show l.length ≤ q by omega),
        List.getElem?_append_right (show l.length ≤ q by omega)]
      obtain ⟨n, rfl⟩ : ∃ n, q = l.length + 2 + n := ⟨q - l.length - 2, by omega⟩
      simp [show l.length + 2 + n - l.length = n + 2 by omega]
    · obtain rfl : q = l.length + 1 := by omega
      rw [sw_apply_right, List.getElem?_append_right (le_refl _),
        List.getElem?_append_right (show l.length ≤ l.length + 1 by omega)]
      simp

/-- Locality of a layer: the component of the target word only depends on the component of
the source word. -/
theorem layOp_local (L : Layer (QuiverHecke.sig D)) (x : V k I) :
    layOp D Sc L (sgl (seqOf (I := I) L.dom.word) (x (seqOf L.dom.word))) (seqOf L.cod.word) =
      layOp D Sc L x (seqOf L.cod.word) := by
  set y : V k I := x - sgl (seqOf (I := I) L.dom.word) (x (seqOf L.dom.word)) with hydef
  have hy : y (seqOf L.dom.word) = 0 := by simp [hydef]
  have h0 : layOp D Sc L y (seqOf L.cod.word) = 0 := by
    obtain ⟨st, l, g, r⟩ := L
    cases g with
    | dot i => exact dependsOn_dotOp D i l.length y _ hy
    | cross i j =>
      refine dependsOn_crossOp D Sc i j l.length y _ ?_
      convert hy using 2
      exact seqOf_swap l r i j
  have hx : x = sgl (seqOf (I := I) L.dom.word) (x (seqOf L.dom.word)) + y := by
    rw [hydef, add_sub_cancel]
  conv_rhs => rw [hx, map_add, Pi.add_apply, h0, add_zero]

/-- The interpretation of the free 2-category on the quiver Hecke signature by the dots and
crossings of the twisted module. -/
def interp : LocalInterpretation (QuiverHecke.sig D) k (V k I) (fun _ : Seq I => M k) where
  κ a := seqOf a.word
  ext ν := LinearMap.single k (fun _ : Seq I => M k) ν
  res ν := LinearMap.proj ν
  op := layOp D Sc
  res_comp_ext ν := LinearMap.ext fun m => by simp
  res_op_ext_res L _ := LinearMap.ext fun x => layOp_local D Sc L x

@[simp] theorem interp_κ (a : Obj (QuiverHecke.sig D)) : (interp D Sc).κ a = seqOf a.word := rfl

@[simp] theorem interp_op (L : Layer (QuiverHecke.sig D)) : (interp D Sc).op L = layOp D Sc L :=
  rfl

theorem interp_res_apply (ν : Seq I) (x : V k I) : (interp D Sc).res ν x = x ν := rfl

theorem interp_ext_apply (ν : Seq I) (m : M k) : (interp D Sc).ext ν m = sgl ν m := rfl

/-! ## Layers given by their data -/

/-- The operator of a layer datum whiskered on the left by `a` strands. -/
def ldOp (a : ℕ) (x : LayerData I) : Module.End k (V k I) :=
  match x.2.1 with
  | .dot i => dotOp D i (a + x.1.length)
  | .cross i j => crossOp D Sc i j (a + x.1.length)

/-- The product of the operators of a list of layer data, the first (bottom) one acting
first. -/
def ldList (a : ℕ) : List (LayerData I) → Module.End k (V k I)
  | [] => 1
  | x :: ls => ldList a ls * ldOp D Sc a x

theorem ldList_append (a : ℕ) (ls ms : List (LayerData I)) :
    ldList D Sc a (ls ++ ms) = ldList D Sc a ms * ldList D Sc a ls := by
  induction ls with
  | nil => simp [ldList]
  | cons x ls ih => simp [ldList, ih, mul_assoc]

theorem ldList_dotsL (a : ℕ) (l : List I) (i : I) (r : List I) (n : ℕ) :
    ldList D Sc a (dotsL l i r n) = dotOp D i (a + l.length) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dotsL, List.replicate_succ, ldList, ← dotsL, ih, pow_succ]
    rfl

theorem ldList_crossL (a : ℕ) (l : List I) (i j : I) (r : List I) :
    ldList D Sc a (crossL l i j r) = crossOp D Sc i j (a + l.length) := by
  simp only [crossL, ldList, one_mul]
  rfl

theorem opList_whisker (u : Obj (QuiverHecke.sig D)) (v : List I) (ls : List (LayerData I)) :
    (interp D Sc).opList ((layList D ls).map (·.whisker u v)) = ldList D Sc u.word.length ls := by
  induction ls with
  | nil => rfl
  | cons x ls ih =>
    rw [show (layList D (x :: ls)).map (·.whisker u v) =
      (lay D x.1 x.2.1 x.2.2).whisker u v :: (layList D ls).map (·.whisker u v) from rfl,
      LocalInterpretation.opList_cons, ih]
    obtain ⟨l, g, r⟩ := x
    cases g <;>
    · simp only [ldList, ldOp, interp_op, layOp, lay, Layer.whisker, List.length_append]
      rfl

/-! ## The interchange law -/

theorem layOp_left_length {s s' : (QuiverHecke.sig D).Region}
    {l l' r r' : List (QuiverHecke.sig D).Colour}
    {g : Shape I} (h : l.length = l'.length) :
    layOp D Sc ⟨s, l, g, r⟩ = layOp (k := k) D Sc ⟨s', l', g, r'⟩ := by
  cases g <;> simp [layOp, h]

omit [DecidableEq I] in
theorem length_cod (g : Shape I) :
    ((QuiverHecke.sig D).cod g).length = ((QuiverHecke.sig D).dom g).length := by
  cases g <;> rfl

theorem layOp_scomm (s : (QuiverHecke.sig D).Region) (l m r : List (QuiverHecke.sig D).Colour)
    (g g' : Shape I) :
    SComm k (layOp (k := k) D Sc ⟨s, l ++ ((QuiverHecke.sig D).cod g ++ m), g', r⟩)
      (layOp D Sc ⟨s, l, g, m ++ ((QuiverHecke.sig D).dom g' ++ r)⟩)
      (g'.parity D * g.parity D) := by
  cases g with
  | dot i =>
    cases g' with
    | dot j =>
      simp only [layOp, Shape.parity]
      exact scomm_dotOp_dotOp D (by simp [QuiverHecke.sig, Shape.cod])
    | cross j l' =>
      simp only [layOp, Shape.parity]
      exact scomm_crossOp_dotOp D Sc (by simp [QuiverHecke.sig, Shape.cod])
        (by simp [QuiverHecke.sig, Shape.cod]; omega)
  | cross i i' =>
    cases g' with
    | dot j =>
      simp only [layOp, Shape.parity]
      exact scomm_dotOp_crossOp D Sc (by simp [QuiverHecke.sig, Shape.cod])
        (by simp [QuiverHecke.sig, Shape.cod])
    | cross j l' =>
      simp only [layOp, Shape.parity]
      exact scomm_crossOp_crossOp D Sc (Or.inr (by simp [QuiverHecke.sig, Shape.cod]))

omit [DecidableEq I] in
theorem interchange_sign (s : (QuiverHecke.sig D).Region) (g g' : Shape I)
    (m : List (QuiverHecke.sig D).Colour) :
    (((⟨s, g, m, g'⟩ : InterchangeData (QuiverHecke.sig D)).sign : ℤ) : k) =
      SKM.zsign k (g'.parity D * g.parity D) := by
  simp only [InterchangeData.sign, QuiverHecke.sig]
  rcases parity_cases (g.parity D) with h | h <;> rcases parity_cases (g'.parity D) with h' | h' <;>
    simp [h, h', SKM.zsign]

theorem interp_interchange (x : InterchangeData (QuiverHecke.sig D)) (hx : x.Valid)
    (u : Obj (QuiverHecke.sig D)) (v : List I) :
    (interp D Sc).evalW ((interp D Sc).κ (x.dom.whisker u v)) ((interp D Sc).κ (x.cod.whisker u v))
      u v (InterchangeData.rel k hx) = 0 := by
  refine (interp D Sc).evalW_interchange_eq_zero_of_comm (fun s l m r g g' => ?_) x hx u v
  have h := layOp_scomm D Sc s l m r g g'
  rw [interp_op, interp_op, interp_op, interp_op, interchange_sign,
    layOp_left_length D Sc (l := l ++ ((QuiverHecke.sig D).dom g ++ m))
      (l' := l ++ ((QuiverHecke.sig D).cod g ++ m)) (s' := s) (r' := r)
      (by simp [length_cod]),
    layOp_left_length D Sc (l := l) (l' := l) (s' := s)
      (r' := m ++ ((QuiverHecke.sig D).dom g' ++ r)) rfl]
  exact h

/-! ## The relations -/

omit [DecidableEq I] in
theorem seqOf_append_at (l w r : List I) (n : ℕ) (h : n < w.length) :
    seqOf (l ++ w ++ r) (l.length + n) = w[n]? := by
  simp only [seqOf, List.append_assoc]
  rw [List.getElem?_append_right (by omega), show l.length + n - l.length = n by omega,
    List.getElem?_append_left h]

theorem evalW_dg_apply (u : Obj (QuiverHecke.sig D)) (v : List I) {t t' : List I}
    (ls : List (LayerData I)) (h : SChain t ls t') (ν ν' : Seq I) (x : M k) :
    (interp D Sc).evalW ν ν' u v (dg (k := k) D ls h) x =
      ldList D Sc u.word.length ls (sgl ν x) ν' := by
  rw [LocalInterpretation.evalW_of_apply, layers_mkD, opList_whisker]
  rfl

theorem evalW_idg_apply (u : Obj (QuiverHecke.sig D)) (v : List I) (t : List I) (ν ν' : Seq I)
    (x : M k) : (interp D Sc).evalW ν ν' u v (idg (k := k) D t) x = sgl ν x ν' := by
  rw [LocalInterpretation.evalW_of_apply]
  rfl

variable {D} in
/-- A word of the signature, as a list of colours. -/
abbrev wI (u : Obj (QuiverHecke.sig D)) : List I := u.word

variable {D} in
/-- A list of colours of the signature, as a list of colours. -/
abbrev cI (v : List (QuiverHecke.sig D).Colour) : List I := v

set_option linter.unusedSimpArgs false in
theorem interp_rel (r : Rel D) (u : Obj (QuiverHecke.sig D))
    (v : List (QuiverHecke.sig D).Colour) :
    (interp D Sc).evalW (seqOf (I := I) (wI u ++ r.dom ++ cI v))
      (seqOf (I := I) (wI u ++ r.cod ++ cI v)) u v (relation D Sc r) = 0 := by
  refine LinearMap.ext fun x => ?_
  have hp : ∀ (w : List I) (n : ℕ), n < w.length →
      seqOf (I := I) (wI u ++ w ++ cI v) (u.word.length + n) = w[n]? :=
    fun w n h => seqOf_append_at (wI u) w (cI v) n h
  have h0 : ∀ (w : List I), 0 < w.length →
      seqOf (I := I) (wI u ++ w ++ cI v) u.word.length = w[0]? :=
    fun w h => hp w 0 h
  cases r with
  | quadEq i =>
    have h := congrFun (quadEq_single D Sc u.word.length (h0 [i, i] (by simp)) (hp [i, i] 1 (by simp)) x) (seqOf (I := I) (wI u ++ [i, i] ++ cI v))
    simp only [relation, map_sub, map_smul, map_sum, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, Finset.sum_apply, Rel.dom, Rel.cod, Pi.sub_apply, Pi.smul_apply, evalW_dg_apply,
      evalW_idg_apply, ldList_append, ldList_crossL, ldList_dotsL, List.length_nil,
      List.length_cons, add_zero, zero_add, Nat.reduceAdd, Module.End.mul_apply,
      Module.End.one_apply, pow_one, LinearMap.zero_apply, Pi.zero_apply, add_assoc] at h ⊢
    exact h
  | quadZero i j hij hd =>
    have h := congrFun (quadZero_single D Sc u.word.length hij hd (h0 [i, j] (by simp)) (hp [i, j] 1 (by simp)) x) (seqOf (I := I) (wI u ++ [i, j] ++ cI v))
    simp only [relation, map_sub, map_smul, map_sum, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, Finset.sum_apply, Rel.dom, Rel.cod, Pi.sub_apply, Pi.smul_apply, evalW_dg_apply,
      evalW_idg_apply, ldList_append, ldList_crossL, ldList_dotsL, List.length_nil,
      List.length_cons, add_zero, zero_add, Nat.reduceAdd, Module.End.mul_apply,
      Module.End.one_apply, pow_one, LinearMap.zero_apply, Pi.zero_apply, add_assoc] at h ⊢
    exact h
  | quadNe i j hij hd =>
    have h := congrFun (quadNe_single D Sc u.word.length hij hd (h0 [i, j] (by simp)) (hp [i, j] 1 (by simp)) x) (seqOf (I := I) (wI u ++ [i, j] ++ cI v))
    simp only [relation, map_sub, map_smul, map_sum, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, Finset.sum_apply, Rel.dom, Rel.cod, Pi.sub_apply, Pi.smul_apply, evalW_dg_apply,
      evalW_idg_apply, ldList_append, ldList_crossL, ldList_dotsL, List.length_nil,
      List.length_cons, add_zero, zero_add, Nat.reduceAdd, Module.End.mul_apply,
      Module.End.one_apply, pow_one, LinearMap.zero_apply, Pi.zero_apply, add_assoc] at h ⊢
    exact h
  | slideL i j hij =>
    have h := congrFun (slideL_single D Sc u.word.length (h0 [i, j] (by simp)) (hp [i, j] 1 (by simp)) x) (seqOf (I := I) (wI u ++ [j, i] ++ cI v))
    simp only [relation, map_sub, map_smul, map_sum, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, Finset.sum_apply, Rel.dom, Rel.cod, Pi.sub_apply, Pi.smul_apply, evalW_dg_apply,
      evalW_idg_apply, ldList_append, ldList_crossL, ldList_dotsL, List.length_nil,
      List.length_cons, add_zero, zero_add, Nat.reduceAdd, Module.End.mul_apply,
      Module.End.one_apply, pow_one, LinearMap.zero_apply, Pi.zero_apply, add_assoc] at h ⊢
    simpa [hij] using h
  | slideLEq i =>
    have h := congrFun (slideL_single D Sc u.word.length (h0 [i, i] (by simp)) (hp [i, i] 1 (by simp)) x) (seqOf (I := I) (wI u ++ [i, i] ++ cI v))
    simp only [relation, map_sub, map_smul, map_sum, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, Finset.sum_apply, Rel.dom, Rel.cod, Pi.sub_apply, Pi.smul_apply, evalW_dg_apply,
      evalW_idg_apply, ldList_append, ldList_crossL, ldList_dotsL, List.length_nil,
      List.length_cons, add_zero, zero_add, Nat.reduceAdd, Module.End.mul_apply,
      Module.End.one_apply, pow_one, LinearMap.zero_apply, Pi.zero_apply, add_assoc] at h ⊢
    rw [sub_eq_zero]
    simpa using h
  | slideR i j hij =>
    have h := congrFun (slideR_single D Sc u.word.length (h0 [i, j] (by simp)) (hp [i, j] 1 (by simp)) x) (seqOf (I := I) (wI u ++ [j, i] ++ cI v))
    simp only [relation, map_sub, map_smul, map_sum, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, Finset.sum_apply, Rel.dom, Rel.cod, Pi.sub_apply, Pi.smul_apply, evalW_dg_apply,
      evalW_idg_apply, ldList_append, ldList_crossL, ldList_dotsL, List.length_nil,
      List.length_cons, add_zero, zero_add, Nat.reduceAdd, Module.End.mul_apply,
      Module.End.one_apply, pow_one, LinearMap.zero_apply, Pi.zero_apply, add_assoc] at h ⊢
    simpa [hij] using h
  | slideREq i =>
    have h := congrFun (slideR_single D Sc u.word.length (h0 [i, i] (by simp)) (hp [i, i] 1 (by simp)) x) (seqOf (I := I) (wI u ++ [i, i] ++ cI v))
    simp only [relation, map_sub, map_smul, map_sum, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, Finset.sum_apply, Rel.dom, Rel.cod, Pi.sub_apply, Pi.smul_apply, evalW_dg_apply,
      evalW_idg_apply, ldList_append, ldList_crossL, ldList_dotsL, List.length_nil,
      List.length_cons, add_zero, zero_add, Nat.reduceAdd, Module.End.mul_apply,
      Module.End.one_apply, pow_one, LinearMap.zero_apply, Pi.zero_apply, add_assoc] at h ⊢
    rw [sub_eq_zero]
    simpa using h
  | braid i j l hb =>
    have h := congrFun (braid_single D Sc hb (h0 [i, j, l] (by simp)) (hp [i, j, l] 1 (by simp)) (hp [i, j, l] 2 (by simp)) x) (seqOf (I := I) (wI u ++ [l, j, i] ++ cI v))
    simp only [relation, map_sub, map_smul, map_sum, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, Finset.sum_apply, Rel.dom, Rel.cod, Pi.sub_apply, Pi.smul_apply, evalW_dg_apply,
      evalW_idg_apply, ldList_append, ldList_crossL, ldList_dotsL, List.length_nil,
      List.length_cons, add_zero, zero_add, Nat.reduceAdd, Module.End.mul_apply,
      Module.End.one_apply, pow_one, LinearMap.zero_apply, Pi.zero_apply, add_assoc] at h ⊢
    exact h
  | braidEq i j hij =>
    have h := congrFun (braidEq_single D Sc hij (h0 [i, j, i] (by simp)) (hp [i, j, i] 1 (by simp)) (hp [i, j, i] 2 (by simp)) x) (seqOf (I := I) (wI u ++ [i, j, i] ++ cI v))
    simp only [relation, map_sub, map_smul, map_sum, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, Finset.sum_apply, Rel.dom, Rel.cod, Pi.sub_apply, Pi.smul_apply, evalW_dg_apply,
      evalW_idg_apply, ldList_append, ldList_crossL, ldList_dotsL, List.length_nil,
      List.length_cons, add_zero, zero_add, Nat.reduceAdd, Module.End.mul_apply,
      Module.End.one_apply, pow_one, LinearMap.zero_apply, Pi.zero_apply, add_assoc] at h ⊢
    exact h

/-- The local interpretation respects the presentation of the quiver Hecke supercategory:
the relations (1.7)–(1.9) and the super interchange law hold in the realization. -/
theorem respects : (pres D Sc).Respects (interp D Sc).functor :=
  (interp D Sc).respects_of _ (fun r u v _ => interp_rel D Sc r u v)
    (fun x hx u v _ => interp_interchange D Sc x hx u v)

/-- The polynomial–Clifford representation of the quiver Hecke supercategory `H`: the object
`i₁ ⋯ iₙ` goes to the component of `V` at the sequence `i₁ ⋯ iₙ`, dots and crossings to the
operators `dotOp` and `crossOp`. -/
noncomputable def rep :=
  (pres D Sc).lift (respects D Sc)

end Interp

end OddMath.QuiverHecke.Realization

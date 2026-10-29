/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.MixedCases
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.TwoSector
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.CoefficientIdeal

/-! # The probe residuals modulo the coefficient ideal

`docs/Nondegeneracy/SwappedHomInversion.md` (11)–(12): after eliminating the reservoir window
(`ProbeWindow.isIso_posMap_of_cap`, `ProbeWindow.isIso_posMap_of_cup`,
`ProbeWindow.isIso_negMap_of_cap`, `ProbeWindow.isIso_negMap_of_cup`), the probe residual agrees,
modulo the coefficient ideal `J`, with the auxiliary probe map of one of the cases (a)–(d) of
`docs/Nondegeneracy/ProbeWindowInverse.md` §3. The bent cross terms are (6) there:
`Cx = Σ_s q^(s+2) • (v_R s ≫ u ≫ y^{-s-1})` and `Dx = -Σ_r q^(r+1) • (x^{-r-1} ≫ v ≫ u_R r)`.
The contractions (7) are exact inside the reservoir window and lie in `J₁` outside it; the
closures (9) lie in `J₁`. Lifting along `J` (`ProbeWindow.CoefficientIdeal.isIso_gMap_of_sub_mem`)
then gives invertibility of the two-sector maps from the probe windows.

The matching of residuals and cases:

| two-sector map | reservoir window | probe case |
|---|---|---|
| `posMap` | cap | (c), `ProbeWindow.isIso_caseC_of_nonneg` |
| `posMap` | cup | (a), `ProbeWindow.exists_isCapInverse_caseA` |
| `negMap` | cap | (d), `ProbeWindow.exists_isCupInverse_caseD` |
| `negMap` | cup | (b), `ProbeWindow.isIso_caseB_of_nonneg` |

## Main results

* `ProbeWindow.isIso_posMap_of_cap_of_window`, `ProbeWindow.isIso_posMap_of_cup_of_window`,
  `ProbeWindow.isIso_negMap_of_cap_of_window`, `ProbeWindow.isIso_negMap_of_cup_of_window`.

The `J₀`-memberships assumed are those of the morphisms the lifting step multiplies by: the
probe window entries `u ≫ y^{-s-1}`, `x^{-r-1} ≫ v`, and the entries of an inverse of the
reference map. The `J₁`-memberships assumed are the closures (9) and the contractions (7) outside
the reservoir window.
-/

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

open CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

section Sign

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The sign `1 ⊕ (-1)` on `Y ⊕ Oᵏ`. -/
def gSign (Y O : C) (κ : Type) [Fintype κ] [DecidableEq κ] : gObj Y O κ ⟶ gObj Y O κ :=
  gMap (𝟙 Y) (fun _ => 0) (fun _ => 0) (fun r r' => if r = r' then -𝟙 O else 0)

lemma gSign_comp_gSign (Y O : C) : gSign Y O κ ≫ gSign Y O κ = 𝟙 _ := by
  rw [gSign, gMap_comp, gMap_id]
  refine gMap_congr (by simp) (fun _ => by simp) (fun _ => by simp) (fun r r' => ?_)
  by_cases h : r = r' <;> simp [h, comp_ite, eq_comm]

instance (Y O : C) : IsIso (gSign Y O κ) := ⟨gSign Y O κ, gSign_comp_gSign Y O, gSign_comp_gSign Y O⟩

/-- Negating the off-corner rows and columns of a block map preserves invertibility. -/
lemma isIso_gMap_neg {X Y O : C} {a : X ⟶ Y} {B : ι → (O ⟶ Y)} {Cc : κ → (X ⟶ O)}
    {E : ι → κ → (O ⟶ O)} (H : IsIso (gMap a B Cc E)) :
    IsIso (gMap a (fun i => -B i) (fun r => -Cc r) E) := by
  have : gMap a (fun i => -B i) (fun r => -Cc r) E =
      gSign X O ι ≫ gMap a B Cc E ≫ gSign Y O κ := by
    rw [gSign, gSign, gMap_comp, gMap_comp]
    refine gMap_congr (by simp) (fun i => by simp [ite_comp]) (fun r => by simp [comp_ite])
      (fun i r => by simp [comp_ite, ite_comp])
  rw [this]
  infer_instance

end Sign

section Contractions

variable (J : CoefficientIdeal C) {X Y O : C}

/-- The cap contractions (7): exact inside the reservoir window, in `J₁` outside it. -/
lemma cap_contraction {h : ℕ} {s : X ⟶ Y} {v : ℕ → (X ⟶ O)} {j : Y ⟶ X} {A : Fin h → (O ⟶ X)}
    (hR : IsCapInverse s (fun n : Fin h => v n) j A)
    (hout : ∀ (n : Fin h) (m : ℕ), h ≤ m → J.mem 1 (A n ≫ v m)) (n : Fin h) (m : ℕ) :
    J.mem 1 (A n ≫ v m - if (n : ℕ) = m then 𝟙 O else 0) := by
  by_cases hm : m < h
  · have := hR.2.2.2.1 n ⟨m, hm⟩
    simp only at this
    simpa [this, Fin.ext_iff] using J.zero_mem 1
  · have hnm : (n : ℕ) ≠ m := by omega
    simpa [hnm] using hout n m (by omega)

/-- The cup contractions (7): exact inside the reservoir window, in `J₁` outside it. -/
lemma cup_contraction {b : ℕ} {s : X ⟶ Y} {u : ℕ → (O ⟶ Y)} {j : Y ⟶ X} {D : Fin b → (Y ⟶ O)}
    (hR : IsCupInverse s (fun n : Fin b => u n) j D)
    (hout : ∀ (n : Fin b) (m : ℕ), b ≤ m → J.mem 1 (u m ≫ D n)) (m : ℕ) (n : Fin b) :
    J.mem 1 (u m ≫ D n - if m = (n : ℕ) then 𝟙 O else 0) := by
  by_cases hm : m < b
  · have := hR.2.2.2.1 ⟨m, hm⟩ n
    simp only at this
    simpa [this, Fin.ext_iff] using J.zero_mem 1
  · have hnm : m ≠ (n : ℕ) := by omega
    simpa [hnm] using hout n m (by omega)

end Contractions

section Bent

variable (J : CoefficientIdeal C) {XR YR XP YP O : C} (x : Aut XP) (y : Aut YP) (v : XP ⟶ O)
  (u : O ⟶ YP) (q : ℤ)

/-- The bent cross term `Cx` of (6), contracted with a reservoir cap inverse, is the probe
column `q^(n+2) • (u ≫ y^{-n-1})` modulo `J₁`. -/
lemma cap_bent {h N : ℕ} (hN : h ≤ N) {Cx : XR ⟶ YP} {vR : ℕ → (XR ⟶ O)}
    (hCx : Cx = ∑ s ∈ Finset.range N,
      q ^ (s + 2) • (vR s ≫ u ≫ (y ^ (-(s : ℤ) - 1)).hom))
    {AR : Fin h → (O ⟶ XR)} (hc : ∀ (n : Fin h) (m : ℕ), J.mem 1
      (AR n ≫ vR m - if (n : ℕ) = m then 𝟙 O else 0))
    (hw : ∀ s < N, J.mem 0 (u ≫ (y ^ (-(s : ℤ) - 1)).hom)) (n : Fin h) :
    J.mem 1 (AR n ≫ Cx - q ^ ((n : ℕ) + 2) • (u ≫ (y ^ (-((n : ℕ) : ℤ) - 1)).hom)) := by
  have hδ : ∑ s ∈ Finset.range N, q ^ (s + 2) •
      ((if (n : ℕ) = s then 𝟙 O else 0) ≫ u ≫ (y ^ (-(s : ℤ) - 1)).hom) =
      q ^ ((n : ℕ) + 2) • (u ≫ (y ^ (-((n : ℕ) : ℤ) - 1)).hom) := by
    rw [Finset.sum_eq_single (n : ℕ)]
    · simp
    · intro s _ hs; simp [Ne.symm hs]
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  have key : AR n ≫ Cx - q ^ ((n : ℕ) + 2) • (u ≫ (y ^ (-((n : ℕ) : ℤ) - 1)).hom) =
      ∑ s ∈ Finset.range N, q ^ (s + 2) •
        ((AR n ≫ vR s - if (n : ℕ) = s then 𝟙 O else 0) ≫ u ≫ (y ^ (-(s : ℤ) - 1)).hom) := by
    rw [hCx, ← hδ, Preadditive.comp_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Preadditive.sub_comp, smul_sub, Preadditive.comp_zsmul, Category.assoc]
  rw [key]
  exact J.sum_mem _ fun s hs => J.zsmul_mem (J.comp_mem (hc n s)
    (hw s (Finset.mem_range.1 hs))) _

/-- The bent cross term `Dx` of (6), contracted with a reservoir cup inverse, is the probe
row `-(q^(n+1) • (x^{-n-1} ≫ v))` modulo `J₁`. -/
lemma cup_bent {b N : ℕ} (hN : b ≤ N) {Dx : XP ⟶ YR} {uR : ℕ → (O ⟶ YR)}
    (hDx : Dx = -∑ r ∈ Finset.range N,
      q ^ (r + 1) • ((x ^ (-(r : ℤ) - 1)).hom ≫ v ≫ uR r))
    {BR : Fin b → (YR ⟶ O)} (hc : ∀ (m : ℕ) (n : Fin b), J.mem 1
      (uR m ≫ BR n - if m = (n : ℕ) then 𝟙 O else 0))
    (hz : ∀ r < N, J.mem 0 ((x ^ (-(r : ℤ) - 1)).hom ≫ v)) (n : Fin b) :
    J.mem 1 (Dx ≫ BR n - -(q ^ ((n : ℕ) + 1) • ((x ^ (-((n : ℕ) : ℤ) - 1)).hom ≫ v))) := by
  have hδ : ∑ r ∈ Finset.range N, q ^ (r + 1) •
      (((x ^ (-(r : ℤ) - 1)).hom ≫ v) ≫ (if r = (n : ℕ) then 𝟙 O else 0)) =
      q ^ ((n : ℕ) + 1) • ((x ^ (-((n : ℕ) : ℤ) - 1)).hom ≫ v) := by
    rw [Finset.sum_eq_single (n : ℕ)]
    · simp
    · intro r _ hr; simp [hr]
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  have key : Dx ≫ BR n - -(q ^ ((n : ℕ) + 1) • ((x ^ (-((n : ℕ) : ℤ) - 1)).hom ≫ v)) =
      -∑ r ∈ Finset.range N, q ^ (r + 1) •
        (((x ^ (-(r : ℤ) - 1)).hom ≫ v) ≫ (uR r ≫ BR n - if r = (n : ℕ) then 𝟙 O else 0)) := by
    rw [hDx, ← hδ, Preadditive.neg_comp, Preadditive.sum_comp, sub_neg_eq_add,
      ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Preadditive.comp_sub, smul_sub, Preadditive.zsmul_comp, Category.assoc, neg_sub]
    abel
  rw [key]
  exact J.neg_mem (J.sum_mem _ fun r hr => J.zsmul_mem (by
    simpa using J.comp_mem (hz r (Finset.mem_range.1 hr)) (hc r n)) _)

end Bent

section Residuals

variable (J : CoefficientIdeal C) {XR YR XP YP O : C} {sR : XR ⟶ YR} {sP : XP ⟶ YP}
  {Cx : XR ⟶ YP} {Dx : XP ⟶ YR} {vR : ℕ → (XR ⟶ O)} {uR : ℕ → (O ⟶ YR)} {jR : YR ⟶ XR}
  (x : Aut XP) (y : Aut YP) (v : XP ⟶ O) (u : O ⟶ YP) (q : ℤ)

/-- The reference map of case (c), (11) of `ProbeWindowInverse.md`. -/
abbrev caseCMap (s : XP ⟶ YP) (a h : ℕ) : gObj XP O (Fin a) ⟶ gObj YP O (Fin (a + h)) :=
  gMap s (fun t : Fin a => q ^ ((t : ℕ) + 2) • (u ≫ (y ^ (-(t : ℤ) - 1)).hom))
    (fun r : Fin (a + h) => (x ^ (r : ℤ)).hom ≫ v)
    (fun t r => if (t : ℕ) = r then 𝟙 O else 0)

/-- **Two sectors, `posMap`, reservoir cap window** (case (c) for the probe): `posMap` is
invertible if the probe cap window of height `h'` is, given the bent form (6) of `Cx`, the
contractions (7) outside the window and the closures (9) in `J₁`, and the `J₀`-memberships of
the probe window entries and of an inverse of the reference map. -/
theorem isIso_posMap_of_cap_of_window (hq : q * q = 1)
    (hslide : sP ≫ y.hom - q • (x.hom ≫ sP) = v ≫ u) {h h' N : ℕ}
    (rowP : Fin (h + h') → (XP ⟶ O)) (hrow : ∀ a, rowP a = (x ^ ((a : ℕ) : ℤ)).hom ≫ v)
    {AR : Fin h → (O ⟶ XR)} (hR : IsCapInverse sR (fun n => vR n) jR AR)
    (h0 : ∃ j A, IsCapInverse sP (fun n : Fin h' => (x ^ (n : ℤ)).hom ≫ v) j A)
    (hN : h ≤ N)
    (hCx : Cx = ∑ s ∈ Finset.range N,
      q ^ (s + 2) • (vR s ≫ u ≫ (y ^ (-(s : ℤ) - 1)).hom))
    (hout : ∀ (n : Fin h) (m : ℕ), h ≤ m → J.mem 1 (AR n ≫ vR m))
    (hclC : J.mem 1 (Dx ≫ jR ≫ Cx)) (hclv : ∀ a : Fin (h + h'), J.mem 1 (Dx ≫ jR ≫ vR a))
    (hw : ∀ s < N, J.mem 0 (u ≫ (y ^ (-(s : ℤ) - 1)).hom))
    (hinv : ∀ g, caseCMap x y v u q sP h h' ≫ g = 𝟙 _ → ∀ i k, J.mem 0 (g i k)) :
    IsIso (posMap sR sP Cx Dx vR rowP) := by
  have : IsIso (caseCMap x y v u q sP h h') := isIso_caseC_of_nonneg sP x y v u q hq hslide h0
  have hc := cap_contraction J hR hout
  refine isIso_posMap_of_cap rowP hR (J.isIso_gMap_of_sub_mem
    (hinv _ (IsIso.hom_inv_id _)) ?_ (fun n => ?_) (fun a => ?_) (fun n a => ?_))
  · rw [sub_sub_cancel_left]; exact J.neg_mem hclC
  · exact cap_bent J y u q hN hCx hc hw n
  · rw [hrow, sub_sub_cancel_left]; exact J.neg_mem (hclv a)
  · exact hc n a

/-- The reference map of case (a), (7) of `ProbeWindowInverse.md`, with the rows of the second
block negated. -/
abbrev caseAMap (s : XP ⟶ YP) (H b : ℕ) : gObj XP O Empty ⟶ gObj YP O (Fin H ⊕ Fin b) :=
  gMap s (fun e : Empty => e.elim)
    (Sum.elim (fun t : Fin H => (x ^ (t : ℤ)).hom ≫ v)
      (fun r : Fin b => -(q ^ ((r : ℕ) + 1) • ((x ^ (-((r : ℕ) : ℤ) - 1)).hom ≫ v))))
    (fun e _ => e.elim)

theorem isIso_caseAMap (hq : q * q = 1) (hslide : sP ≫ y.hom - q • (x.hom ≫ sP) = v ≫ u)
    {H b : ℕ} (h0 : ∃ j A, IsCapInverse sP (fun n : Fin (H + b) => (x ^ (n : ℤ)).hom ≫ v) j A) :
    IsIso (caseAMap x v q sP H b) := by
  obtain ⟨j, A, hA⟩ := exists_isCapInverse_caseA sP x y v u q hq hslide h0
  have hA' := hA.reindex (Equiv.refl _) (Fin.append (fun _ : Fin H => (1 : ℤ)) fun _ => -1)
    (fun m => by refine Fin.addCases (fun t => ?_) (fun r => ?_) m <;> simp)
  refine isIso_gMap_of_reindex_target _ _ _ _ finSumFinEquiv.symm ?_
  convert isIso_gMap_capWindow hA' using 2
  funext m
  refine Fin.addCases (fun t => ?_) (fun r => ?_) m <;> simp

/-- **Two sectors, `posMap`, reservoir cup window** (case (a) for the probe). -/
theorem isIso_posMap_of_cup_of_window (hq : q * q = 1)
    (hslide : sP ≫ y.hom - q • (x.hom ≫ sP) = v ≫ u) {H b N : ℕ}
    (rowP : Fin H → (XP ⟶ O)) (hrow : ∀ a, rowP a = (x ^ ((a : ℕ) : ℤ)).hom ≫ v)
    {BR : Fin b → (YR ⟶ O)} (hR : IsCupInverse sR (fun n => uR n) jR BR)
    (h0 : ∃ j A, IsCapInverse sP (fun n : Fin (H + b) => (x ^ (n : ℤ)).hom ≫ v) j A)
    (hN : b ≤ N)
    (hDx : Dx = -∑ r ∈ Finset.range N,
      q ^ (r + 1) • ((x ^ (-(r : ℤ) - 1)).hom ≫ v ≫ uR r))
    (hout : ∀ (n : Fin b) (m : ℕ), b ≤ m → J.mem 1 (uR m ≫ BR n))
    (hclC : J.mem 1 (Dx ≫ jR ≫ Cx)) (hclv : ∀ a : Fin H, J.mem 1 (Dx ≫ jR ≫ vR a))
    (hz : ∀ r < N, J.mem 0 ((x ^ (-(r : ℤ) - 1)).hom ≫ v))
    (hinv : ∀ g, caseAMap x v q sP H b ≫ g = 𝟙 _ → ∀ i k, J.mem 0 (g i k)) :
    IsIso (posMap sR sP Cx Dx vR rowP) := by
  have := isIso_caseAMap x y v u q hq hslide h0
  have hc := cup_contraction J hR hout
  refine isIso_posMap_of_cup rowP hR (J.isIso_gMap_of_sub_mem
    (hinv _ (IsIso.hom_inv_id _)) ?_ (fun e => e.elim) (fun a => ?_) (fun e => e.elim))
  · rw [sub_sub_cancel_left]; exact J.neg_mem hclC
  · rcases a with a | n
    · simp only [Sum.elim_inl]; rw [hrow, sub_sub_cancel_left]; exact J.neg_mem (hclv a)
    · simp only [Sum.elim_inr]; exact cup_bent J x v q hN hDx hc hz n

/-- The reference map of case (d), (14) of `ProbeWindowInverse.md`, with the columns of the
second block negated. -/
abbrev caseDMap (s : XP ⟶ YP) (a g : ℕ) : gObj XP O (Fin a ⊕ Fin g) ⟶ gObj YP O Empty :=
  gMap s (Sum.elim (fun r : Fin a => q ^ ((r : ℕ) + 2) • (u ≫ (y ^ (-((r : ℕ) : ℤ) - 1)).hom))
      (fun t : Fin g => u ≫ (y ^ ((t : ℕ) : ℤ)).hom))
    (fun e : Empty => e.elim) (fun _ e => e.elim)

theorem isIso_caseDMap (hq : q * q = 1) (hslide : sP ≫ y.hom - q • (x.hom ≫ sP) = v ≫ u)
    {a g : ℕ} (h0 : ∃ j D, IsCupInverse sP (fun n : Fin (a + g) => u ≫ (y ^ (n : ℤ)).hom) j D) :
    IsIso (caseDMap y u q sP a g) := by
  obtain ⟨j, D, hD⟩ := exists_isCupInverse_caseD sP x y v u q hq hslide h0
  have hD' := hD.reindex (Equiv.refl _) (Fin.append (fun _ : Fin a => (1 : ℤ)) fun _ => -1)
    (fun m => by refine Fin.addCases (fun t => ?_) (fun r => ?_) m <;> simp)
  refine isIso_gMap_of_reindex_source _ _ _ _ finSumFinEquiv.symm ?_
  convert isIso_gMap_cupWindow hD' using 2
  funext m
  refine Fin.addCases (fun t => ?_) (fun r => ?_) m <;> simp

/-- **Two sectors, `negMap`, reservoir cap window** (case (d) for the probe). -/
theorem isIso_negMap_of_cap_of_window (hq : q * q = 1)
    (hslide : sP ≫ y.hom - q • (x.hom ≫ sP) = v ≫ u) {h G N : ℕ}
    (colP : Fin G → (O ⟶ YP)) (hcol : ∀ a, colP a = u ≫ (y ^ ((a : ℕ) : ℤ)).hom)
    {AR : Fin h → (O ⟶ XR)} (hR : IsCapInverse sR (fun n => vR n) jR AR)
    (h0 : ∃ j D, IsCupInverse sP (fun n : Fin (h + G) => u ≫ (y ^ (n : ℤ)).hom) j D)
    (hN : h ≤ N)
    (hCx : Cx = ∑ s ∈ Finset.range N,
      q ^ (s + 2) • (vR s ≫ u ≫ (y ^ (-(s : ℤ) - 1)).hom))
    (hout : ∀ (n : Fin h) (m : ℕ), h ≤ m → J.mem 1 (AR n ≫ vR m))
    (hclC : J.mem 1 (Dx ≫ jR ≫ Cx)) (hclu : ∀ a : Fin G, J.mem 1 (uR a ≫ jR ≫ Cx))
    (hw : ∀ s < N, J.mem 0 (u ≫ (y ^ (-(s : ℤ) - 1)).hom))
    (hinv : ∀ g, caseDMap y u q sP h G ≫ g = 𝟙 _ → ∀ i k, J.mem 0 (g i k)) :
    IsIso (negMap sR sP Cx Dx uR colP) := by
  have := isIso_caseDMap x y v u q hq hslide h0
  have hc := cap_contraction J hR hout
  refine isIso_negMap_of_cap colP hR (J.isIso_gMap_of_sub_mem
    (hinv _ (IsIso.hom_inv_id _)) ?_ (fun a => ?_) (fun e => e.elim) (fun _ e => e.elim))
  · rw [sub_sub_cancel_left]; exact J.neg_mem hclC
  · rcases a with n | a
    · simp only [Sum.elim_inl]; exact cap_bent J y u q hN hCx hc hw n
    · simp only [Sum.elim_inr]; rw [hcol, sub_sub_cancel_left]; exact J.neg_mem (hclu a)

/-- The reference map of case (b), (8) of `ProbeWindowInverse.md`, with its off-corner rows and
columns negated. -/
abbrev caseBMap (s : XP ⟶ YP) (d h : ℕ) : gObj XP O (Fin d) ⟶ gObj YP O (Fin (d + h)) :=
  gMap s (fun t : Fin d => u ≫ (y ^ ((t : ℕ) : ℤ)).hom)
    (fun r : Fin (d + h) => -(q ^ ((r : ℕ) + 1) • ((x ^ (-((r : ℕ) : ℤ) - 1)).hom ≫ v)))
    (fun t r => if (t : ℕ) = r then 𝟙 O else 0)

theorem isIso_caseBMap (hq : q * q = 1) (hslide : sP ≫ y.hom - q • (x.hom ≫ sP) = v ≫ u)
    {d h : ℕ} (h0 : ∃ j A, IsCapInverse sP (fun n : Fin h => (x ^ (n : ℤ)).hom ≫ v) j A) :
    IsIso (caseBMap x y v u q sP d h) := by
  have H := isIso_gMap_neg (isIso_caseB_of_nonneg sP x y v u q hq hslide (d := d) h0)
  have e : caseBMap x y v u q sP d h = gMap sP (fun t : Fin d => -(-(u ≫ (y ^ (t : ℤ)).hom)))
      (fun r : Fin (d + h) => -(q ^ ((r : ℕ) + 1) • ((x ^ (-(r : ℤ) - 1)).hom ≫ v)))
      (fun t r => if (t : ℕ) = r then 𝟙 O else 0) :=
    gMap_congr rfl (fun t => by rw [neg_neg]) (fun _ => rfl) (fun _ _ => rfl)
  rw [e]; exact H

/-- **Two sectors, `negMap`, reservoir cup window** (case (b) for the probe). -/
theorem isIso_negMap_of_cup_of_window (hq : q * q = 1)
    (hslide : sP ≫ y.hom - q • (x.hom ≫ sP) = v ≫ u) {G h' N : ℕ}
    (colP : Fin G → (O ⟶ YP)) (hcol : ∀ a, colP a = u ≫ (y ^ ((a : ℕ) : ℤ)).hom)
    {BR : Fin (G + h') → (YR ⟶ O)} (hR : IsCupInverse sR (fun n => uR n) jR BR)
    (h0 : ∃ j A, IsCapInverse sP (fun n : Fin h' => (x ^ (n : ℤ)).hom ≫ v) j A)
    (hN : G + h' ≤ N)
    (hDx : Dx = -∑ r ∈ Finset.range N,
      q ^ (r + 1) • ((x ^ (-(r : ℤ) - 1)).hom ≫ v ≫ uR r))
    (hout : ∀ (n : Fin (G + h')) (m : ℕ), G + h' ≤ m → J.mem 1 (uR m ≫ BR n))
    (hclC : J.mem 1 (Dx ≫ jR ≫ Cx)) (hclu : ∀ a : Fin G, J.mem 1 (uR a ≫ jR ≫ Cx))
    (hz : ∀ r < N, J.mem 0 ((x ^ (-(r : ℤ) - 1)).hom ≫ v))
    (hinv : ∀ g, caseBMap x y v u q sP G h' ≫ g = 𝟙 _ → ∀ i k, J.mem 0 (g i k)) :
    IsIso (negMap sR sP Cx Dx uR colP) := by
  have := isIso_caseBMap x y v u q hq hslide (d := G) h0
  have hc := cup_contraction J hR hout
  refine isIso_negMap_of_cup colP hR (J.isIso_gMap_of_sub_mem
    (hinv _ (IsIso.hom_inv_id _)) ?_ (fun a => ?_) (fun n => ?_) (fun a n => ?_))
  · rw [sub_sub_cancel_left]; exact J.neg_mem hclC
  · rw [hcol, sub_sub_cancel_left]; exact J.neg_mem (hclu a)
  · exact cup_bent J x v q hN hDx hc hz n
  · exact hc a n

end Residuals

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

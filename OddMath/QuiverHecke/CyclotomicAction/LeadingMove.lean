import OddMath.QuiverHecke.CyclotomicAction.AppendContent
import OddMath.QuiverHecke.SerreWords
import OddMath.QuiverHecke.CyclotomicAction.SignedIntertwiner
import OddMath.QuiverHecke.HnBasis
import OddMath.QuiverHecke.CyclotomicAction.PrependCoordinates

/-!
# Leading move

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Signed top-crossing part of the moving chain

The polynomial decorations are retained in their chronological positions.
At equal colours the leading decoration is `(v-u)^2` in even parity and
`-(v^2-u^2)^2` in odd parity. Multiplication in `End` reverses categorical
composition, so these decorate the output of the crossing. The theorem
`moveHom_sub_leading_mem_low` discards every choice of a crossing-free
summand in the prescribed chain, at arbitrary word length. Collecting these
decorations into one ordered polynomial is a separate normal-ordering step.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Composition adds crossing bounds, without identifying any leading scalar. -/
theorem filt_comp_mem {s t v : List I} {m n : ℕ}
    {f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)}
    {g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D v)}
    (hf : f ∈ Filt D Sc s t m) (hg : g ∈ Filt D Sc t v n) :
    f ≫ g ∈ Filt D Sc s v (m + n) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Q, hQ, hq, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨R, hR, hr, rfl⟩ := hg
      rw [cl_comp]
      exact cl_mem_filt D Sc _ (by simp only [crossCount_append]; omega)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [Linear.comp_smul]; exact Submodule.smul_mem _ c hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hx

/-- A strict crossing bound stays strict after composition. -/
theorem filt_comp_low_mem {s t v : List I} {m n : ℕ}
    {f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)}
    {g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D v)}
    (hf : f ∈ Filt D Sc s t m) (hg : g ∈ Low D Sc t v n) :
    f ≫ g ∈ Low D Sc s v (m + n) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Q, hQ, hq, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨R, hR, hr, rfl⟩ := hg
      rw [cl_comp]
      exact cl_mem_low D Sc _ (by simp only [crossCount_append]; omega)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [Linear.comp_smul]; exact Submodule.smul_mem _ c hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hx

/-- A strict bound also stays strict on the lower side of a composite. -/
theorem low_comp_filt_mem {s t v : List I} {m n : ℕ}
    {f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)}
    {g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D v)}
    (hf : f ∈ Low D Sc s t m) (hg : g ∈ Filt D Sc t v n) :
    f ≫ g ∈ Low D Sc s v (m + n) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Q, hQ, hq, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨R, hR, hr, rfl⟩ := hg
      rw [cl_comp]
      exact cl_mem_low D Sc _ (by simp only [crossCount_append]; omega)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [Linear.comp_smul]; exact Submodule.smul_mem _ c hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hx

/-- Telescoping two specified leading terms preserves their exact coefficients. -/
theorem filtered_comp_sub_mem_low {s t v : List I} {m n : ℕ}
    {f f' : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)}
    {g g' : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D v)}
    (hf : f ∈ Filt D Sc s t m) (hg' : g' ∈ Filt D Sc t v n)
    (hff' : f - f' ∈ Low D Sc s t m) (hgg' : g - g' ∈ Low D Sc t v n) :
    f ≫ g - f' ≫ g' ∈ Low D Sc s v (m + n) := by
  have h := (Low D Sc s v (m + n)).add_mem
    (filt_comp_low_mem D Sc hf hgg') (low_comp_filt_mem D Sc hff' hg')
  simpa only [Preadditive.comp_sub, Preadditive.sub_comp, sub_add_sub_cancel] using h

private theorem filt_eqToHom {s t : List I} (h : s = t) :
    eqToHom (congrArg (fun v => (pres D Sc).obj (ob D v)) h) ∈ Filt D Sc s t 0 := by
  subst t
  have hc := cl_mem_filt D Sc (show SChain s (pl s []) s from rfl) (n := 0) (by simp)
  simpa only [cl_nil, eqToHom_refl] using hc

private theorem filt_mul {s : List I} {m n : ℕ}
    {f g : End ((pres D Sc).obj (ob D s))}
    (hf : f ∈ Filt D Sc s s m) (hg : g ∈ Filt D Sc s s n) :
    f * g ∈ Filt D Sc s s (m + n) := by
  simpa only [End.mul_def, Nat.add_comm] using filt_comp_mem D Sc hg hf

private theorem filt_dot (s : List I) (a : ℕ) : dotE D Sc s a ∈ Filt D Sc s s 0 := by
  rw [dotE_eq_cl D Sc (sChain_dotAny s a)]
  exact cl_mem_filt D Sc _ (by simp [crossCount, PG.isCross])

/-- Signed leading same-colour polynomial, with no crossing-free summand. -/
def leadingSameIntertwiner (s : List I) (a : ℕ) (i : I) :
    End ((pres D Sc).obj (ob D s)) :=
  if D.parity i = 1 then
    -((dotE D Sc s (a + 1) ^ 2 - dotE D Sc s a ^ 2) ^ 2 * crossE D Sc s a)
  else (dotE D Sc s (a + 1) - dotE D Sc s a) ^ 2 * crossE D Sc s a

private theorem leadingSame_bounds (s : List I) (a : ℕ) (i : I) :
    leadingSameIntertwiner D Sc s a i ∈ Filt D Sc s s 1 ∧
    sameIntertwiner D Sc s a i - leadingSameIntertwiner D Sc s a i ∈ Filt D Sc s s 0 := by
  have hu := filt_dot D Sc s a
  have hv := filt_dot D Sc s (a + 1)
  have he := (Filt D Sc s s 0).sub_mem hv hu
  have hd := (Filt D Sc s s 0).sub_mem
    (show dotE D Sc s (a + 1) ^ 2 ∈ Filt D Sc s s 0 by
      simpa only [pow_two] using filt_mul D Sc hv hv)
    (show dotE D Sc s a ^ 2 ∈ Filt D Sc s s 0 by
      simpa only [pow_two] using filt_mul D Sc hu hu)
  have ht : crossE D Sc s a ∈ Filt D Sc s s 1 := by
    unfold crossE genE
    split_ifs with h
    · exact cl_mem_filt D Sc h (by simp [crossCount, PG.isCross])
    · exact Submodule.zero_mem _
  have hee : (dotE D Sc s (a + 1) - dotE D Sc s a) ^ 2 ∈
      Filt D Sc s s 0 := by simpa only [pow_two] using filt_mul D Sc he he
  have hdd : (dotE D Sc s (a + 1) ^ 2 - dotE D Sc s a ^ 2) ^ 2 ∈
      Filt D Sc s s 0 := by simpa only [pow_two] using filt_mul D Sc hd hd
  have hddt := filt_mul D Sc hdd ht
  have heet := filt_mul D Sc hee ht
  have hde := filt_mul D Sc hd he
  by_cases hp : D.parity i = 1
  · simp only [leadingSameIntertwiner, sameIntertwiner, hp, ite_true]
    constructor
    · exact (Filt D Sc s s 1).neg_mem hddt
    · rw [movingOdd_crossingCoefficient]
      simpa only [sub_neg_eq_add, sub_add_cancel] using hde
  · simp only [leadingSameIntertwiner, sameIntertwiner, hp, ite_false]
    constructor
    · exact heet
    · rw [movingEven_crossingCoefficient, add_sub_cancel_right]
      exact he

/-- The leading summand of an adjacent intertwiner, with its library sign. -/
def leadingIntertwinerHom (l r : List I) (i j : I) :
    (pres D Sc).obj (ob D (l ++ [i, j] ++ r)) ⟶
      (pres D Sc).obj (ob D (l ++ [j, i] ++ r)) :=
  if h : i = j then
    leadingSameIntertwiner D Sc (l ++ [i, j] ++ r) l.length i ≫ eqToHom (by rw [h])
  else cl D Sc _ _ [.cross l.length] (sChain_crossAt l r i j)

/-- Local leading term and discarded error have respectively one and zero crossings. -/
theorem leadingIntertwiner_bounds (l r : List I) (i j : I) :
    leadingIntertwinerHom D Sc l r i j ∈ Filt D Sc _ _ 1 ∧
    intertwinerHom D Sc l r i j - leadingIntertwinerHom D Sc l r i j ∈
      Filt D Sc _ _ 0 := by
  by_cases h : i = j
  · subst j
    simpa [leadingIntertwinerHom, intertwinerHom] using
      leadingSame_bounds D Sc (l ++ [i, i] ++ r) l.length i
  · simp only [leadingIntertwinerHom, intertwinerHom, dite_eq_right h, sub_self]
    exact ⟨cl_mem_filt D Sc _ (by simp [crossCount, PG.isCross]), Submodule.zero_mem _⟩

/-- Chronological product of the signed polynomial-decorated crossings. -/
def leadingMoveHom (i : I) : (l ν : List I) →
    (pres D Sc).obj (ob D (l ++ i :: ν)) ⟶ (pres D Sc).obj (ob D (l ++ ν ++ [i]))
  | l, [] => eqToHom (by simp)
  | l, j :: ν =>
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by simp)) ≫
        leadingIntertwinerHom D Sc l ν i j ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
            (show l ++ [j, i] ++ ν = (l ++ [j]) ++ i :: ν by simp)) ≫
            leadingMoveHom i (l ++ [j]) ν ≫
              eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by simp))

private theorem leadingIntertwiner_filt (l r : List I) (i j : I) :
    intertwinerHom D Sc l r i j ∈ Filt D Sc _ _ 1 := by
  obtain ⟨hL, hE⟩ := leadingIntertwiner_bounds D Sc l r i j
  have h := (Filt D Sc _ _ 1).add_mem (filt_mono D Sc (by omega : 0 ≤ 1) hE) hL
  simpa only [sub_add_cancel] using h

private theorem moveHom_leading_bounds (i : I) (l ν : List I) :
    moveHom D Sc i l ν ∈ Filt D Sc _ _ ν.length ∧
    leadingMoveHom D Sc i l ν ∈ Filt D Sc _ _ ν.length ∧
    moveHom D Sc i l ν - leadingMoveHom D Sc i l ν ∈ Low D Sc _ _ ν.length := by
  induction ν generalizing l with
  | nil =>
    simp only [moveHom, leadingMoveHom, List.length_nil, sub_self]
    exact ⟨filt_eqToHom D Sc (by simp), filt_eqToHom D Sc (by simp), Submodule.zero_mem _⟩
  | cons j ν ih =>
    obtain ⟨hG, hL, hE⟩ := ih (l ++ [j])
    have hA := leadingIntertwiner_filt D Sc l ν i j
    obtain ⟨hB, hAB⟩ := leadingIntertwiner_bounds D Sc l ν i j
    have h0 := filt_eqToHom D Sc
      (show l ++ i :: j :: ν = l ++ [i, j] ++ ν by simp)
    have h1 := filt_eqToHom D Sc
      (show l ++ [j, i] ++ ν = (l ++ [j]) ++ i :: ν by simp)
    have h2 := filt_eqToHom D Sc
      (show (l ++ [j]) ++ ν ++ [i] = l ++ (j :: ν) ++ [i] by simp)
    have hG2 := filt_comp_mem D Sc hG h2
    have hL2 := filt_comp_mem D Sc hL h2
    have hE2 := low_comp_filt_mem D Sc hE h2
    rw [Preadditive.sub_comp] at hE2
    have hG1 := filt_comp_mem D Sc h1 hG2
    have hL1 := filt_comp_mem D Sc h1 hL2
    have hE1 := filt_comp_low_mem D Sc h1 hE2
    rw [Preadditive.comp_sub] at hE1
    have hGA := filt_comp_mem D Sc hA hG1
    have hLA := filt_comp_mem D Sc hB hL1
    have hEA := filtered_comp_sub_mem_low D Sc hA hL1
      (filt_le_low D Sc (by omega : 0 < 1) hAB) hE1
    have hG0 := filt_comp_mem D Sc h0 hGA
    have hL0 := filt_comp_mem D Sc h0 hLA
    have hE0 := filt_comp_low_mem D Sc h0 hEA
    rw [Preadditive.comp_sub] at hE0
    simpa only [moveHom, leadingMoveHom, List.length_cons, Nat.add_zero,
      Nat.zero_add, Nat.add_comm 1] using And.intro hG0 (And.intro hL0 hE0)

/-- Every discarded summand of the full prescribed chain has fewer crossings
than the old word. The remaining chain retains the explicit even positive and
odd negative polynomial factors, not an unspecified leading unit. -/
theorem moveHom_sub_leading_mem_low (i : I) (l ν : List I) :
    moveHom D Sc i l ν - leadingMoveHom D Sc i l ν ∈
      Low D Sc (l ++ i :: ν) (l ++ ν ++ [i]) ν.length :=
  (moveHom_leading_bounds D Sc i l ν).2.2

end OddMath.QuiverHecke
end

end

section

/-!
# Signed source-endpoint dot transport

Dots are moved from the output of a crossing word to its input. The
coefficient records each incident slide and each distant super interchange,
with the colours evaluated before that crossing. No unit is chosen from
`Approx`. `decorated_crossings_normal_order` collects arbitrarily many
interleaved monomial decorations in chronological input-endpoint dot order.
Expanding `leadingMoveHom` into these monomials and identifying the assembled
Mackey coefficient remain separate steps.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Incident slides use the crossing parity; distant slides also use the dot parity. -/
def crossDotExponent (t : List I) (a p : ℕ) : ZMod 2 :=
  if p = a ∨ p = a + 1 then (PG.cross a).par D t
  else (PG.cross a).par D t * (PG.dot p).par D t

private theorem signed_slide_right {t t' : List I} {a : ℕ} (ha : a + 1 < t.length)
    (h : SChain t (pl t [.cross a, .dot a]) t')
    (h' : SChain t (pl t [.dot (a + 1), .cross a]) t') :
    cl D Sc t t' [.cross a, .dot a] h -
      SKM.zsign k ((PG.cross a).par D t) •
        cl D Sc t t' [.dot (a + 1), .cross a] h' ∈ Filt D Sc t t' 0 := by
  obtain ⟨l, x, y, r, rfl, rfl⟩ := exists_split_cross ha
  have ht : tgt (l ++ [x, y] ++ r) [.cross l.length, .dot l.length] =
      l ++ [y, x] ++ r := by simp [PG.act]
  obtain rfl : _ = t' := ht ▸ tgt_eq h
  simpa [PG.par] using slide_right D Sc l r x y h h'

private theorem signed_slide_left {t t' : List I} {a : ℕ} (ha : a + 1 < t.length)
    (h : SChain t (pl t [.dot a, .cross a]) t')
    (h' : SChain t (pl t [.cross a, .dot (a + 1)]) t') :
    cl D Sc t t' [.dot a, .cross a] h -
      SKM.zsign k ((PG.cross a).par D t) •
        cl D Sc t t' [.cross a, .dot (a + 1)] h' ∈ Filt D Sc t t' 0 := by
  obtain ⟨l, x, y, r, rfl, rfl⟩ := exists_split_cross ha
  have ht : tgt (l ++ [x, y] ++ r) [.dot l.length, .cross l.length] =
      l ++ [y, x] ++ r := by simp [PG.act]
  obtain rfl : _ = t' := ht ▸ tgt_eq h
  simpa [PG.par] using slide_left D Sc l r x y h h'

private theorem transport_sign_square (p : ZMod 2) :
    SKM.zsign k p * SKM.zsign k p = 1 := by
  unfold SKM.zsign; split_ifs <;> simp

/-- The signed adjacent dot transport, including distant odd dots. -/
theorem cross_dot_move_signed {t t' : List I} {a p : ℕ}
    (ha : a + 1 < t.length) (hp : p < t.length)
    (h : SChain t (pl t [.cross a, .dot p]) t')
    (h' : SChain t (pl t [.dot (swapNat a p), .cross a]) t') :
    cl D Sc t t' [.cross a, .dot p] h -
      SKM.zsign k (crossDotExponent D t a p) •
        cl D Sc t t' [.dot (swapNat a p), .cross a] h' ∈ Filt D Sc t t' 0 := by
  by_cases hpa : p = a
  · subst p
    simp only [swapNat, ite_true] at h' ⊢
    simpa [crossDotExponent, swapNat] using signed_slide_right D Sc ha h h'
  by_cases hpa' : p = a + 1
  · subst p
    simp only [swapNat, ite_eq_right (by omega : a + 1 ≠ a)] at h' ⊢
    have hm := signed_slide_left D Sc ha h' h
    have hm' := (Filt D Sc t t' 0).smul_mem (-SKM.zsign k ((PG.cross a).par D t)) hm
    simpa only [crossDotExponent, or_true, ite_true, smul_sub, smul_smul,
      neg_mul, transport_sign_square, neg_smul, one_smul, sub_neg_eq_add,
      neg_add_eq_sub] using hm'
  have hs : swapNat a p = p := by simp [swapNat, hpa, hpa']
  simp only [hs] at h' ⊢
  simp only [crossDotExponent, hpa, hpa', or_self, ite_false]
  by_cases hlt : p < a
  · have he := far_swap_eq D Sc (.dot p) (.cross a)
      (by simp; omega) (by simp; omega) h' h
    rw [he, smul_smul, mul_comm ((PG.dot p).par D t), transport_sign_square,
      one_smul, sub_self]
    exact Submodule.zero_mem _
  · have he := far_swap_eq D Sc (.cross a) (.dot p)
      (by simp; omega) (by simp; omega) h h'
    rw [he, sub_self]
    exact Submodule.zero_mem _

/-- Input position of an output dot, following the crossing word backwards. -/
def sourceDotPosition : List ℕ → ℕ → ℕ
  | [], p => p
  | a :: σ, p => sourceDotPosition σ (swapNat a p)

/-- Product of the local library signs, evaluated on the intermediate words. -/
def sourceDotSign (t : List I) : List ℕ → ℕ → k
  | [], _ => 1
  | a :: σ, p => SKM.zsign k (crossDotExponent D (tgt t (cw σ)) a p) *
      sourceDotSign t σ (swapNat a p)

/-- Move a dot across an arbitrary crossing word, retaining the computed sign
and its source-endpoint position, in any diagrammatic context. -/
theorem dot_down_signed {t t' : List I} (P : List PG) {n : ℕ} (hn : t.length = n)
    (σ : List ℕ) (hv : ValidWord n σ) (p : ℕ) (hp : p < n) (R : List PG)
    (h : SChain t (pl t (P ++ cw σ ++ [.dot p] ++ R)) t') :
    ∃ h' : SChain t (pl t (P ++ [.dot (sourceDotPosition σ p)] ++ cw σ ++ R)) t',
      cl D Sc t t' (P ++ cw σ ++ [.dot p] ++ R) h -
        sourceDotSign D (k := k) (tgt t P) σ p •
          cl D Sc t t' (P ++ [.dot (sourceDotPosition σ p)] ++ cw σ ++ R) h' ∈
        Low D Sc t t' (crossCount P + σ.length + crossCount R) := by
  induction σ generalizing p R with
  | nil =>
    have e : P ++ cw [] ++ [.dot p] ++ R =
        P ++ [.dot (sourceDotPosition [] p)] ++ cw [] ++ R := by simp [sourceDotPosition]
    refine ⟨e ▸ h, ?_⟩
    simp only [sourceDotSign, one_smul, cl_eq_cl e h (e ▸ h), sub_self]
    exact Submodule.zero_mem _
  | cons a σ ih =>
    have ha : a + 1 < n := hv a (by simp)
    let Q := P ++ cw σ
    have e₁ : P ++ cw (a :: σ) ++ [.dot p] ++ R =
        Q ++ [.cross a, .dot p] ++ R := by simp [Q, cw_cons]
    let s := tgt t Q
    have hl : s.length = n := by simp [s, hn]
    let M := [PG.cross a, PG.dot p]
    let M' := [PG.dot (swapNat a p), PG.cross a]
    have hM : SChain s (pl s M) (tgt s M) := sChain_pl _ _
    have hM' : SChain s (pl s M') (tgt s M) :=
      sChain_of_tgt hM (by rfl)
    have hR : SChain (tgt s M) (pl (tgt s M) R) t' := by
      have he : tgt (tgt s M) R = t' := by
        have he := tgt_eq (e₁ ▸ h)
        simpa only [tgt_append] using he
      exact he ▸ sChain_pl _ _
    have hmid : SChain t (pl t (Q ++ M' ++ R)) t' :=
      sChain_append_of (sChain_append_of (sChain_pl t Q) hM') hR
    have hm := cross_dot_move_signed D Sc (by omega : a + 1 < s.length)
      (by omega : p < s.length) hM hM'
    have hctx := move_ctx D Sc Q M M' R
      (SKM.zsign k (crossDotExponent D s a p)) (sChain_pl t Q) hR hM hM' hm
      (e₁ ▸ h) hmid
    have hA := filt_le_low D Sc
      (show crossCount Q + 0 + crossCount R <
        crossCount P + (a :: σ).length + crossCount R by simp [Q]) hctx
    have e₂ : Q ++ M' ++ R = P ++ cw σ ++ [.dot (swapNat a p)] ++ ([.cross a] ++ R) := by
      simp [Q, M']
    have hp' : swapNat a p < n := by unfold swapNat; split_ifs <;> omega
    obtain ⟨hout, hB⟩ := ih (fun x hx => hv x (by simp [hx]))
      (swapNat a p) hp' ([.cross a] ++ R) (e₂ ▸ hmid)
    have e₃ : P ++ [.dot (sourceDotPosition σ (swapNat a p))] ++ cw σ ++ ([.cross a] ++ R) =
        P ++ [.dot (sourceDotPosition (a :: σ) p)] ++ cw (a :: σ) ++ R := by
      simp [sourceDotPosition, cw_cons]
    refine ⟨e₃ ▸ hout, ?_⟩
    have hB' : cl D Sc t t' _ (e₂ ▸ hmid) -
        sourceDotSign D (k := k) (tgt t P) σ (swapNat a p) • cl D Sc t t' _ hout ∈
        Low D Sc t t' (crossCount P + (a :: σ).length + crossCount R) := by
      simpa [crossCount, PG.isCross, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hB
    have hh := (Low D Sc t t' (crossCount P + (a :: σ).length + crossCount R)).add_mem hA
      ((Low D Sc t t' _).smul_mem (SKM.zsign k (crossDotExponent D s a p)) hB')
    rw [smul_sub, smul_smul, cl_eq_cl e₂ hmid (e₂ ▸ hmid), sub_add_sub_cancel] at hh
    simpa only [sourceDotSign, s, Q, tgt_append,
      cl_eq_cl e₁ h (e₁ ▸ h), ← cl_eq_cl e₃ hout (e₃ ▸ hout)] using hh

/-- Sign for a whole output dot monomial, in its given multiplication order. -/
def sourceDotsSign (t : List I) (σ ps : List ℕ) : k :=
  (ps.map (sourceDotSign D (k := k) t σ)).prod

/-- Collect an arbitrary output dot monomial at the input endpoint. Dot order
is preserved; no commutativity of odd variables is assumed. -/
theorem dots_down_signed {t t' : List I} (P : List PG) {n : ℕ} (hn : t.length = n)
    (σ : List ℕ) (hv : ValidWord n σ) (ps : List ℕ) (hp : ∀ p ∈ ps, p < n) (R : List PG)
    (h : SChain t (pl t (P ++ cw σ ++ ps.map PG.dot ++ R)) t') :
    ∃ h' : SChain t
        (pl t (P ++ (ps.map (sourceDotPosition σ)).map PG.dot ++ cw σ ++ R)) t',
      cl D Sc t t' (P ++ cw σ ++ ps.map PG.dot ++ R) h -
        sourceDotsSign D (k := k) (tgt t P) σ ps •
          cl D Sc t t' (P ++ (ps.map (sourceDotPosition σ)).map PG.dot ++ cw σ ++ R) h' ∈
        Low D Sc t t' (crossCount P + σ.length + crossCount R) := by
  induction ps generalizing P with
  | nil =>
    have e : P ++ cw σ ++ [].map PG.dot ++ R =
        P ++ ([].map (sourceDotPosition σ)).map PG.dot ++ cw σ ++ R := by simp
    refine ⟨e ▸ h, ?_⟩
    simp [sourceDotsSign]
  | cons p ps ih =>
    have e₁ : P ++ cw σ ++ (p :: ps).map PG.dot ++ R =
        P ++ cw σ ++ [.dot p] ++ (ps.map PG.dot ++ R) := by simp
    obtain ⟨hmid, hA⟩ := dot_down_signed D Sc P hn σ hv p (hp p (by simp))
      (ps.map PG.dot ++ R) (e₁ ▸ h)
    let P' := P ++ [.dot (sourceDotPosition σ p)]
    have e₂ : P ++ [.dot (sourceDotPosition σ p)] ++ cw σ ++ (ps.map PG.dot ++ R) =
        P' ++ cw σ ++ ps.map PG.dot ++ R := by simp [P']
    obtain ⟨hout, hB⟩ := ih P' (fun q hq => hp q (by simp [hq])) (e₂ ▸ hmid)
    have e₃ : P' ++ (ps.map (sourceDotPosition σ)).map PG.dot ++ cw σ ++ R =
        P ++ ((p :: ps).map (sourceDotPosition σ)).map PG.dot ++ cw σ ++ R := by simp [P']
    refine ⟨e₃ ▸ hout, ?_⟩
    have hA' : cl D Sc t t' _ (e₁ ▸ h) -
        sourceDotSign D (k := k) (tgt t P) σ p • cl D Sc t t' _ hmid ∈
        Low D Sc t t' (crossCount P + σ.length + crossCount R) := by
      simpa only [crossCount_append, crossCount_dots, Nat.zero_add] using hA
    have hB' : cl D Sc t t' _ (e₂ ▸ hmid) -
        sourceDotsSign D (k := k) (tgt t P) σ ps • cl D Sc t t' _ hout ∈
        Low D Sc t t' (crossCount P + σ.length + crossCount R) := by
      simpa [P', tgt_append, crossCount, PG.isCross, PG.act] using hB
    have hh := (Low D Sc t t' _).add_mem hA'
      ((Low D Sc t t' _).smul_mem (sourceDotSign D (k := k) (tgt t P) σ p) hB')
    rw [smul_sub, smul_smul, cl_eq_cl e₂ hmid (e₂ ▸ hmid), sub_add_sub_cancel] at hh
    simpa [sourceDotsSign, P', List.append_assoc] using hh

/-- Crossing word with a dot monomial above each crossing. Blocks are listed
from top to bottom, as in `cw`. -/
def decoratedCrossingGens : List (ℕ × List ℕ) → List PG
  | [] => []
  | (a, ps) :: bs => decoratedCrossingGens bs ++ [.cross a] ++ ps.map PG.dot

/-- Chronological input-endpoint dot order after collecting every block. -/
def collectedSourceDots : List (ℕ × List ℕ) → List ℕ
  | [] => []
  | (a, ps) :: bs => collectedSourceDots bs ++
      ps.map (sourceDotPosition (a :: bs.map Prod.fst))

/-- Computed signed coefficient of the collected monomial. -/
def collectedSourceSign (t : List I) : List (ℕ × List ℕ) → k
  | [] => 1
  | (a, ps) :: bs => collectedSourceSign t bs *
      sourceDotsSign D (k := k) t (a :: bs.map Prod.fst) ps

/-- Collect all interleaved dot decorations at the source endpoint, in
chronological monomial order, with the exact product of transport signs.
The statement is uniform in the number of crossings and decorations. -/
theorem decorated_crossings_normal_order {t t' : List I} (P : List PG)
    {n : ℕ} (hn : t.length = n) (bs : List (ℕ × List ℕ))
    (hv : ValidWord n (bs.map Prod.fst))
    (hp : ∀ b ∈ bs, ∀ p ∈ b.2, p < n) (R : List PG)
    (h : SChain t (pl t (P ++ decoratedCrossingGens bs ++ R)) t') :
    ∃ h' : SChain t
        (pl t (P ++ (collectedSourceDots bs).map PG.dot ++ cw (bs.map Prod.fst) ++ R)) t',
      cl D Sc t t' (P ++ decoratedCrossingGens bs ++ R) h -
        collectedSourceSign D (k := k) (tgt t P) bs •
          cl D Sc t t' (P ++ (collectedSourceDots bs).map PG.dot ++ cw (bs.map Prod.fst) ++ R) h' ∈
        Low D Sc t t' (crossCount P + bs.length + crossCount R) := by
  induction bs generalizing P R with
  | nil =>
    have e : P ++ decoratedCrossingGens [] ++ R =
        P ++ (collectedSourceDots []).map PG.dot ++ cw (([] : List (ℕ × List ℕ)).map Prod.fst) ++ R := by
      simp [decoratedCrossingGens, collectedSourceDots]
    refine ⟨e ▸ h, ?_⟩
    simp [decoratedCrossingGens, collectedSourceDots, collectedSourceSign]
  | cons b bs ih =>
    obtain ⟨a, ps⟩ := b
    let R' := [PG.cross a] ++ ps.map PG.dot ++ R
    have e₁ : P ++ decoratedCrossingGens ((a, ps) :: bs) ++ R =
        P ++ decoratedCrossingGens bs ++ R' := by simp [decoratedCrossingGens, R']
    obtain ⟨hmid, hA⟩ := ih P
      (fun x hx => hv x (by simp [hx]))
      (fun b hb p hpb => hp b (by simp [hb]) p hpb) R' (e₁ ▸ h)
    let P' := P ++ (collectedSourceDots bs).map PG.dot
    have e₂ : P ++ (collectedSourceDots bs).map PG.dot ++ cw (bs.map Prod.fst) ++ R' =
        P' ++ cw (a :: bs.map Prod.fst) ++ ps.map PG.dot ++ R := by simp [P', R', cw_cons]
    obtain ⟨hout, hB⟩ := dots_down_signed D Sc P' hn (a :: bs.map Prod.fst) hv ps
      (hp (a, ps) (by simp)) R (e₂ ▸ hmid)
    have e₃ : P' ++ (ps.map (sourceDotPosition (a :: bs.map Prod.fst))).map PG.dot ++
        cw (a :: bs.map Prod.fst) ++ R =
        P ++ (collectedSourceDots ((a, ps) :: bs)).map PG.dot ++
          cw (((a, ps) :: bs).map Prod.fst) ++ R := by simp [P', collectedSourceDots]
    refine ⟨e₃ ▸ hout, ?_⟩
    have hA' : cl D Sc t t' _ (e₁ ▸ h) -
        collectedSourceSign D (k := k) (tgt t P) bs • cl D Sc t t' _ hmid ∈
        Low D Sc t t' (crossCount P + ((a, ps) :: bs).length + crossCount R) := by
      simpa [R', crossCount_append, crossCount_dots, crossCount_cons, crossCount_nil,
        PG.isCross, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hA
    have hB' : cl D Sc t t' _ (e₂ ▸ hmid) -
        sourceDotsSign D (k := k) (tgt t P) (a :: bs.map Prod.fst) ps • cl D Sc t t' _ hout ∈
        Low D Sc t t' (crossCount P + ((a, ps) :: bs).length + crossCount R) := by
      simpa only [P', tgt_append, tgt_map_dot, crossCount_append, crossCount_dots,
        Nat.add_zero, List.length_cons, List.length_map] using hB
    have hh := (Low D Sc t t' _).add_mem hA'
      ((Low D Sc t t' _).smul_mem (collectedSourceSign D (k := k) (tgt t P) bs) hB')
    rw [smul_sub, smul_smul, cl_eq_cl e₂ hmid (e₂ ▸ hmid), sub_add_sub_cancel] at hh
    simpa [collectedSourceSign, decoratedCrossingGens, collectedSourceDots,
      P', R', cw_cons, List.append_assoc] using hh

end OddMath.QuiverHecke
end

end

section

/-!
# Four-term expansion of a leading intertwiner

The local polynomial factors of `MoveHomLeading` are expanded without commuting
any dots. Lists record chronological output decorations after the crossing.
This supplies the local finite expansion for the moving-chain normal ordering.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Chronological output dots of the four local monomials. -/
def leadingBlockDots (i j : I) (a : ℕ) (c : Fin 4) : List ℕ :=
  if i = j then
    if D.parity i = 1 then
      ![[a+1,a+1,a+1,a+1], [a,a,a+1,a+1], [a+1,a+1,a,a], [a,a,a,a]] c
    else ![[a+1,a+1], [a,a+1], [a+1,a], [a,a]] c
  else []

/-- Explicit local signs; unequal colours retain only the zeroth term. -/
def leadingBlockCoeff (i j : I) (c : Fin 4) : k :=
  if i = j then
    if D.parity i = 1 then ![-1,1,1,-1] c else ![1,-1,-1,1] c
  else if c = 0 then 1 else 0

/-- Every decoration stays within the two strands of the crossing. -/
theorem leadingBlockDots_lt (i j : I) {a n : ℕ} (ha : a + 1 < n)
    (c : Fin 4) : ∀ p ∈ leadingBlockDots D i j a c, p < n := by
  intro p hp
  unfold leadingBlockDots at hp
  split_ifs at hp <;> fin_cases c <;> simp at hp <;> omega

/-- Canonical chain from the input word to the swapped output word. -/
theorem leadingBlock_sChain (l r : List I) (i j : I) (c : Fin 4) :
    SChain (l ++ [i,j] ++ r)
      (pl (l ++ [i,j] ++ r)
        ([.cross l.length] ++ (leadingBlockDots D i j l.length c).map PG.dot))
      (l ++ [j,i] ++ r) := by
  have h := sChain_pl (l ++ [i,j] ++ r)
    ([.cross l.length] ++ (leadingBlockDots D i j l.length c).map PG.dot)
  simpa only [tgt_append, tgt_map_dot, tgt_eq (sChain_crossAt l r i j)] using h

/-- Exact four-term expansion, crossing first and output dots afterwards. -/
theorem leadingIntertwinerHom_expansion (l r : List I) (i j : I) :
    leadingIntertwinerHom D Sc l r i j =
      ∑ c : Fin 4, leadingBlockCoeff D (k := k) i j c •
        cl D Sc _ _
          ([.cross l.length] ++ (leadingBlockDots D i j l.length c).map PG.dot)
          (leadingBlock_sChain D l r i j c) := by
  by_cases hij : i = j
  · subst j
    by_cases hp : D.parity i = 1
    all_goals
      simp only [leadingIntertwinerHom, dite_true, Category.comp_id,
        eqToHom_refl, leadingSameIntertwiner, hp, ite_true, ite_false,
        Fin.sum_univ_succ, leadingBlockCoeff, leadingBlockDots,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        neg_smul, one_smul, Fin.sum_univ_zero, add_zero]
      simp only [pow_two, sub_mul, mul_sub, neg_sub]
      rw [show crossE D Sc (l ++ [i,i] ++ r) l.length =
        cl D Sc _ _ [.cross l.length] (sChain_crossAt l r i i) from
          genE_eq D Sc (sChain_crossAt l r i i)]
      simp only [dotE_eq_cl D Sc (sChain_dotAny _ _), cl_mul,
        List.cons_append, List.nil_append]
      abel
  · simp [leadingIntertwinerHom, hij, leadingBlockCoeff, leadingBlockDots]

end OddMath.QuiverHecke
end

end

section

/-!
# Finite expansion of the leading moving chain

Expand the recursive leading move into products of the four local terms of
`leadingIntertwinerHom_expansion`. Blocks are recorded from top to bottom,
with canonical chains and position bounds for signed dot normal ordering.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

def MoveChoices : List I → Type
  | [] => Unit
  | _ :: ν => Fin 4 × MoveChoices ν

instance moveChoicesFintype : (ν : List I) → Fintype (MoveChoices ν)
  | [] => inferInstanceAs (Fintype Unit)
  | _ :: ν => @instFintypeProd _ _ inferInstance (moveChoicesFintype ν)

def leadingMoveBlocks (i : I) : (l ν : List I) → MoveChoices ν → List (ℕ × List ℕ)
  | _, [], _ => []
  | l, j :: ν, c => leadingMoveBlocks i (l ++ [j]) ν c.2 ++
      [(l.length, leadingBlockDots D i j l.length c.1)]

def leadingMoveCoeff (i : I) : (ν : List I) → MoveChoices ν → k
  | [], _ => 1
  | j :: ν, c => leadingBlockCoeff D i j c.1 * leadingMoveCoeff i ν c.2

def leadingMoveWord : (l ν : List I) → List ℕ
  | _, [] => []
  | l, j :: ν => leadingMoveWord (l ++ [j]) ν ++ [l.length]

theorem leadingMoveBlocks_map_fst (i : I) (l ν : List I) (c : MoveChoices ν) :
    (leadingMoveBlocks D i l ν c).map Prod.fst = leadingMoveWord l ν := by
  induction ν generalizing l with
  | nil => rfl
  | cons j ν ih => simp [leadingMoveBlocks, leadingMoveWord, ih]

theorem leadingMoveBlocks_length (i : I) (l ν : List I) (c : MoveChoices ν) :
    (leadingMoveBlocks D i l ν c).length = ν.length := by
  induction ν generalizing l with
  | nil => rfl
  | cons j ν ih => simp [leadingMoveBlocks, ih]

theorem leadingMoveWord_valid (l ν : List I) :
    ValidWord (l.length + ν.length + 1) (leadingMoveWord l ν) := by
  induction ν generalizing l with
  | nil => intro a ha; simp [leadingMoveWord] at ha
  | cons j ν ih =>
    intro a ha
    simp only [leadingMoveWord, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · have h := ih (l ++ [j]) a ha
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    · simp only [List.length_cons]; omega

theorem leadingMoveBlocks_valid (i : I) (l ν : List I) (c : MoveChoices ν) :
    ValidWord (l.length + ν.length + 1) ((leadingMoveBlocks D i l ν c).map Prod.fst) := by
  rw [leadingMoveBlocks_map_fst]
  exact leadingMoveWord_valid l ν

theorem leadingMoveBlocks_dots_lt (i : I) (l ν : List I) (c : MoveChoices ν) :
    ∀ b ∈ leadingMoveBlocks D i l ν c, ∀ p ∈ b.2, p < l.length + ν.length + 1 := by
  induction ν generalizing l with
  | nil => simp [leadingMoveBlocks]
  | cons j ν ih =>
    intro b hb p hp
    simp only [leadingMoveBlocks, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · have h := ih (l ++ [j]) c.2 b hb p hp
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    · exact leadingBlockDots_lt D i j (by simp only [List.length_cons]; omega) c.1 p hp

theorem decoratedCrossingGens_append (bs cs : List (ℕ × List ℕ)) :
    decoratedCrossingGens (bs ++ cs) = decoratedCrossingGens cs ++ decoratedCrossingGens bs := by
  induction bs with
  | nil => simp [decoratedCrossingGens]
  | cons b bs ih => simp [decoratedCrossingGens, ih, List.append_assoc]

theorem leadingMoveBlocks_sChain (i : I) (l ν : List I) (c : MoveChoices ν) :
    SChain (l ++ i :: ν)
      (pl (l ++ i :: ν) (decoratedCrossingGens (leadingMoveBlocks D i l ν c)))
      (l ++ ν ++ [i]) := by
  induction ν generalizing l with
  | nil => simp [leadingMoveBlocks, decoratedCrossingGens]
  | cons j ν ih =>
    have h₁ := leadingBlock_sChain D l ν i j c.1
    have h₂ := ih (l ++ [j]) c.2
    have h₁' : SChain (l ++ i :: j :: ν)
        (pl (l ++ i :: j :: ν)
          ([.cross l.length] ++ (leadingBlockDots D i j l.length c.1).map PG.dot))
        ((l ++ [j]) ++ i :: ν) := by simpa using h₁
    simpa [leadingMoveBlocks, decoratedCrossingGens_append, decoratedCrossingGens,
      List.append_assoc] using sChain_append_of h₁' h₂

private theorem cl_nil_eqToHom {t t' : List I} (e : t = t')
    (h : SChain t (pl t []) t') :
    cl D Sc t t' [] h = eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s)) e) := by
  subst t'
  simp [cl_nil]

theorem leadingMoveHom_expansion (i : I) (l ν : List I) :
    leadingMoveHom D Sc i l ν =
      ∑ c : MoveChoices ν, leadingMoveCoeff D (k := k) i ν c •
        cl D Sc _ _ (decoratedCrossingGens (leadingMoveBlocks D i l ν c))
          (leadingMoveBlocks_sChain D i l ν c) := by
  induction ν generalizing l with
  | nil =>
    simp only [leadingMoveHom, leadingMoveCoeff, leadingMoveBlocks, decoratedCrossingGens,
      MoveChoices, Fintype.sum_unique, one_smul]
    exact (cl_nil_eqToHom D Sc (by simp) _).symm
  | cons j ν ih =>
    rw [leadingMoveHom, leadingIntertwinerHom_expansion, ih]
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, Linear.comp_smul,
      Linear.smul_comp, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    rw [show (∑ c : MoveChoices (j :: ν), _) = _ from Fintype.sum_prod_type _]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    simp only [leadingMoveCoeff, leadingMoveBlocks, decoratedCrossingGens_append,
      decoratedCrossingGens, List.nil_append]
    rw [mul_comm (leadingMoveCoeff D i ν b)]
    congr 1
    rw [cl_comp_eqToHom D Sc _
      (show (l ++ [j]) ++ ν ++ [i] = l ++ (j :: ν) ++ [i] by simp),
      eqToHom_comp_cl D Sc
        (show l ++ [j,i] ++ ν = (l ++ [j]) ++ i :: ν by simp),
      cl_comp, eqToHom_comp_cl D Sc
        (show l ++ i :: j :: ν = l ++ [i,j] ++ ν by simp)]
end OddMath.QuiverHecke
end

end

section

/-!
# Collected endpoint polynomial of the leading moving chain

The finite polynomial is given explicitly by its chronological dot monomials.
Each coefficient is the product of the local four-term expansion coefficient
and the computed transport sign. No reordering of odd dots, choice of a unit,
or identification of a colour count with a dot degree is made.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- The undecorated crossing chain of the prescribed move. -/
theorem leadingMoveWord_sChain (i : I) (l ν : List I) :
    SChain (l ++ i :: ν) (pl (l ++ i :: ν) (cw (leadingMoveWord l ν)))
      (l ++ ν ++ [i]) := by
  induction ν generalizing l with
  | nil => simp [leadingMoveWord]
  | cons j ν ih =>
    have h := sChain_append_of (sChain_crossAt l ν i j) (by
      simpa using ih (l ++ [j]))
    simpa [leadingMoveWord, cw_append, cw, List.append_assoc] using h

/-- An ordered dot monomial at a fixed endpoint. Multiplication order is
chronological categorical composition, not increasing strand order. -/
def endpointDotMonomial (t : List I) (ps : List ℕ) :
    (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t) :=
  cl D Sc t t (ps.map PG.dot) (by simpa only [tgt_map_dot] using sChain_pl t (ps.map PG.dot))

/-- The explicitly expanded source-endpoint polynomial of the prescribed
moving chain. Local coefficients include the negative odd square factor;
transport coefficients include every incident and distant slide. -/
def leadingMoveEndpointPolynomial (i : I) (l ν : List I) :
    (pres D Sc).obj (ob D (l ++ i :: ν)) ⟶ (pres D Sc).obj (ob D (l ++ i :: ν)) :=
  ∑ c : MoveChoices ν,
    (leadingMoveCoeff D (k := k) i ν c *
      collectedSourceSign D (k := k) (l ++ i :: ν) (leadingMoveBlocks D i l ν c)) •
        endpointDotMonomial D Sc (l ++ i :: ν)
          (collectedSourceDots (leadingMoveBlocks D i l ν c))

/-- Applying signed decorated-block normal ordering to the finite expansion
of `leadingMoveHom` gives its concrete collected endpoint polynomial for
arbitrary words and either parity. -/
theorem leadingMoveHom_sub_endpointPolynomial_mem_low (i : I) (l ν : List I) :
    leadingMoveHom D Sc i l ν -
      leadingMoveEndpointPolynomial D Sc i l ν ≫
        cl D Sc _ _ (cw (leadingMoveWord l ν)) (leadingMoveWord_sChain i l ν) ∈
      Low D Sc (l ++ i :: ν) (l ++ ν ++ [i]) ν.length := by
  rw [leadingMoveHom_expansion, leadingMoveEndpointPolynomial]
  simp only [Preadditive.sum_comp, Linear.smul_comp, ← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro c hc
  obtain ⟨h', hh⟩ := decorated_crossings_normal_order D Sc
    (t' := l ++ ν ++ [i]) []
    (show (l ++ i :: ν).length = l.length + ν.length + 1 by simp; omega)
    (leadingMoveBlocks D i l ν c) (leadingMoveBlocks_valid D i l ν c)
    (leadingMoveBlocks_dots_lt D i l ν c) []
    (by simpa using leadingMoveBlocks_sChain D i l ν c)
  have hm := (Low D Sc (l ++ i :: ν) (l ++ ν ++ [i]) ν.length).smul_mem
    (leadingMoveCoeff D (k := k) i ν c)
    (show _ ∈ Low D Sc (l ++ i :: ν) (l ++ ν ++ [i]) ν.length from by
      simpa only [List.nil_append, List.append_nil, crossCount_nil, Nat.zero_add,
        Nat.add_zero, leadingMoveBlocks_length, tgt_nil] using hh)
  simpa only [smul_sub, smul_smul, endpointDotMonomial, cl_comp,
    leadingMoveBlocks_map_fst, List.nil_append, List.append_nil] using hm

/-- The collected formula also computes the top-crossing part of the
prescribed (not just leading) moving homomorphism. -/
theorem moveHom_sub_endpointPolynomial_mem_low (i : I) (l ν : List I) :
    moveHom D Sc i l ν -
      leadingMoveEndpointPolynomial D Sc i l ν ≫
        cl D Sc _ _ (cw (leadingMoveWord l ν)) (leadingMoveWord_sChain i l ν) ∈
      Low D Sc (l ++ i :: ν) (l ++ ν ++ [i]) ν.length := by
  have h := (Low D Sc _ _ ν.length).add_mem
    (moveHom_sub_leading_mem_low D Sc i l ν)
    (leadingMoveHom_sub_endpointPolynomial_mem_low D Sc i l ν)
  simpa only [sub_add_sub_cancel] using h

/-- Every longest scalar prepend coordinate is computed by the collected
polynomial. This includes indices with nonidentity old permutation. -/
theorem moveHom_long_prepend_repr_endpointPolynomial (i : I) (ν : List I)
    (x : PrependIdx i ν (ν ++ [i]))
    (hx : x.1.2.2.2 = longPrependShuffle ν.length) :
    (prependBasis D Sc (i := i) (s := ν) (t := ν ++ [i])).repr (moveHom D Sc i [] ν) x =
      (prependBasis D Sc (i := i) (s := ν) (t := ν ++ [i])).repr
        (leadingMoveEndpointPolynomial D Sc i [] ν ≫
          cl D Sc _ _ (cw (leadingMoveWord [] ν)) (leadingMoveWord_sChain i [] ν)) x := by
  have h := prependBasis_long_repr_eq_zero_of_low D Sc i ν (ν ++ [i]) _
    (moveHom_sub_endpointPolynomial_mem_low D Sc i [] ν) x hx
  simpa only [map_sub, Finsupp.sub_apply, sub_eq_zero, List.nil_append] using h

end OddMath.QuiverHecke
end

end

section

/-!
# Source transport for a leading moving-strand expansion

`collectedSourceSign_leadingMoveBlocks` eliminates the transport coefficient.
`collectedSourceDots_leadingMoveBlocks` evaluates the original collection recursion
at explicit moving and old-strand source positions. Together they identify the
source dot word needed for the ordered moving-strand polynomial product.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k]

theorem sourceDotPosition_append (σ τ : List ℕ) (p : ℕ) :
    sourceDotPosition (σ ++ τ) p = sourceDotPosition τ (sourceDotPosition σ p) := by
  induction σ generalizing p with
  | nil => rfl
  | cons a σ ih => exact ih (swapNat a p)

theorem sourceDotSign_append (t : List I) (σ τ : List ℕ) (p : ℕ) :
    sourceDotSign D (k := k) t (σ ++ τ) p =
      sourceDotSign D (tgt t (cw τ)) σ p *
        sourceDotSign D t τ (sourceDotPosition σ p) := by
  induction σ generalizing p with
  | nil => simp [sourceDotSign, sourceDotPosition]
  | cons a σ ih =>
    simp [sourceDotSign, sourceDotPosition, cw_append, tgt_append, ih, mul_assoc]

theorem sourceDotSign_sq (t : List I) (σ : List ℕ) (p : ℕ) :
    sourceDotSign D (k := k) t σ p * sourceDotSign D t σ p = 1 := by
  induction σ generalizing p with
  | nil => simp [sourceDotSign]
  | cons a σ ih =>
    have hs (q : ZMod 2) : SKM.zsign k q * SKM.zsign k q = 1 := by
      unfold SKM.zsign; split_ifs <;> simp
    rw [sourceDotSign, mul_mul_mul_comm, hs, ih, one_mul]

theorem collectedSourceDots_snoc (bs : List (ℕ × List ℕ)) (a : ℕ) (ps : List ℕ) :
    collectedSourceDots (bs ++ [(a, ps)]) =
      ps.map (swapNat a) ++ (collectedSourceDots bs).map (swapNat a) := by
  induction bs with
  | nil => simp [collectedSourceDots, sourceDotPosition]
  | cons b bs ih =>
    simp [collectedSourceDots, ih, sourceDotPosition_append, sourceDotPosition,
      List.map_append, List.map_map, List.append_assoc, Function.comp_def]

private theorem collectedSourceSign_snoc_even (t : List I)
    (bs : List (ℕ × List ℕ)) (a : ℕ) (ps : List ℕ)
    (ha : ∀ p, sourceDotSign D (k := k) t [a] p = 1) :
    collectedSourceSign D (k := k) t (bs ++ [(a, ps)]) =
      collectedSourceSign D (tgt t (cw [a])) bs := by
  have hs (σ qs : List ℕ) : sourceDotsSign D (k := k) t (σ ++ [a]) qs =
      sourceDotsSign D (tgt t (cw [a])) σ qs := by
    have hf : sourceDotSign D (k := k) t (σ ++ [a]) =
        sourceDotSign D (tgt t (cw [a])) σ := by
      funext p
      rw [sourceDotSign_append, ha, mul_one]
    simp only [sourceDotsSign, hf]
  have hf : sourceDotSign D (k := k) t [a] = fun _ => 1 := funext ha
  induction bs with
  | nil => simp [collectedSourceSign, sourceDotsSign, hf]
  | cons b bs ih =>
    simp only [List.cons_append, collectedSourceSign, ih, List.map_append,
      List.map_cons, List.map_nil]
    rw [show b.1 :: (bs.map Prod.fst ++ [a]) = (b.1 :: bs.map Prod.fst) ++ [a] from rfl, hs]

private theorem sourceDotsSign_leadingBlock_odd (i j : I) (hi : D.parity i = 1)
    (t : List I) (σ : List ℕ) (a : ℕ) (c : Fin 4) :
    sourceDotsSign D (k := k) t σ (leadingBlockDots D i j a c) = 1 := by
  by_cases hij : i = j
  · subst j
    fin_cases c <;>
      simp [leadingBlockDots, hi, sourceDotsSign, sourceDotSign_sq]
  · simp [leadingBlockDots, hij, sourceDotsSign]

private theorem collectedSourceSign_of_blocks (t : List I) (bs : List (ℕ × List ℕ))
    (h : ∀ b ∈ bs, ∀ σ, sourceDotsSign D (k := k) t σ b.2 = 1) :
    collectedSourceSign D (k := k) t bs = 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [collectedSourceSign, h b (by simp), mul_one]
    exact ih (fun d hd => h d (by simp [hd]))

/-- Every computed transport coefficient is one, including all distant odd slides. -/
theorem collectedSourceSign_leadingMoveBlocks (i : I) (l ν : List I)
    (c : MoveChoices ν) :
    collectedSourceSign D (k := k) (l ++ i :: ν) (leadingMoveBlocks D i l ν c) = 1 := by
  rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
  · induction ν generalizing l with
    | nil => rfl
    | cons j ν ih =>
      have ha : ∀ p, sourceDotSign D (k := k) (l ++ i :: j :: ν) [l.length] p = 1 := by
        intro p
        have he : (PG.cross l.length).par D (l ++ i :: j :: ν) = 0 := by
          simp [PG.par, hi]
        simp [sourceDotSign, crossDotExponent, he, SKM.zsign]
      rw [leadingMoveBlocks, collectedSourceSign_snoc_even D _ _ _ _ ha]
      have ht : tgt (l ++ i :: j :: ν) (cw [l.length]) = (l ++ [j]) ++ i :: ν := by
        simpa [cw] using tgt_eq (sChain_crossAt l ν i j)
      rw [ht]
      exact ih (l ++ [j]) c.2
  · apply collectedSourceSign_of_blocks
    intro b hb σ
    have h : ∀ l ν (c : MoveChoices ν), ∀ b ∈ leadingMoveBlocks D i l ν c,
        ∀ t, sourceDotsSign D (k := k) t σ b.2 = 1 := by
      intro l ν
      induction ν generalizing l with
      | nil => simp [leadingMoveBlocks]
      | cons j ν ih =>
        intro c b hb t
        simp only [leadingMoveBlocks, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact ih _ c.2 _ hb t
        · exact sourceDotsSign_leadingBlock_odd D i j hi t σ _ c.1
    exact h l ν c b hb _

/-- A local block at its source endpoints: `m` is the moving strand and `p` the old strand. -/
def leadingSourceBlockDots (i j : I) (m p : ℕ) (c : Fin 4) : List ℕ :=
  if i = j then
    if D.parity i = 1 then
      match c.val with
      | 0 => [m, m, m, m]
      | 1 => [p, p, m, m]
      | 2 => [m, m, p, p]
      | _ => [p, p, p, p]
    else
      match c.val with
      | 0 => [m, m]
      | 1 => [p, m]
      | 2 => [m, p]
      | _ => [p, p]
  else []

/-- Explicit source positions, in collection order. At old index `b`, the old
strand has position `a + b + 1`, while the moving strand stays at `m`. -/
def leadingSourceDots (i : I) (m a : ℕ) :
    (ν : List I) → MoveChoices ν → List ℕ
  | [], _ => []
  | j :: ν, c => leadingSourceBlockDots D i j m (a + 1) c.1 ++
      leadingSourceDots i m (a + 1) ν c.2

private theorem leadingSourceBlockDots_map (i j : I) (m p : ℕ) (c : Fin 4)
    (f : ℕ → ℕ) :
    (leadingSourceBlockDots D i j m p c).map f =
      leadingSourceBlockDots D i j (f m) (f p) c := by
  unfold leadingSourceBlockDots
  split_ifs <;> fin_cases c <;> rfl

private theorem leadingSourceDots_map (i : I) (m m' a : ℕ) (ν : List I)
    (c : MoveChoices ν) (f : ℕ → ℕ) (hm : f m = m')
    (hp : ∀ b, a ≤ b → f (b + 1) = b + 1) :
    (leadingSourceDots D i m a ν c).map f = leadingSourceDots D i m' a ν c := by
  induction ν generalizing a with
  | nil => rfl
  | cons j ν ih =>
    simp only [leadingSourceDots, List.map_append, leadingSourceBlockDots_map, hm,
      hp a le_rfl]
    rw [ih (a + 1) c.2 (fun b hb => hp b (by omega))]

private theorem leadingBlockDots_swap (i j : I) (a : ℕ) (c : Fin 4) :
    (leadingBlockDots D i j a c).map (swapNat a) =
      leadingSourceBlockDots D i j a (a + 1) c := by
  unfold leadingBlockDots leadingSourceBlockDots
  split_ifs <;> fin_cases c <;> simp [swapNat]

/-- Evaluation of the original collected dot list at explicit source positions,
for arbitrary prefixes, words, choices and parity of the moving colour. -/
theorem collectedSourceDots_leadingMoveBlocks (i : I) (l ν : List I)
    (c : MoveChoices ν) :
    collectedSourceDots (leadingMoveBlocks D i l ν c) =
      leadingSourceDots D i l.length l.length ν c := by
  induction ν generalizing l with
  | nil => rfl
  | cons j ν ih =>
    rw [leadingMoveBlocks, collectedSourceDots_snoc, ih, leadingBlockDots_swap]
    simp only [List.length_append, List.length_singleton]
    rw [leadingSourceDots_map D i (l.length + 1) l.length (l.length + 1) ν c.2
      (swapNat l.length) (by simp [swapNat])
      (by intro b hb; simp [swapNat, show b + 1 ≠ l.length by omega,
        show b ≠ l.length by omega])]
    rfl

end OddMath.QuiverHecke
end

end

section

/-!
# Ordered square-difference product of a leading move

The source-endpoint polynomial of the leading moving chain is the ordered
product of signed square differences. The product uses endomorphism-ring
multiplication, with the earliest chronological factor on the right.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- The local signed square difference, independently of expansion choices. -/
def leadingSourceSquare (t : List I) (i j : I) (m p : ℕ) :
    End ((pres D Sc).obj (ob D t)) :=
  if i = j then
    if D.parity i = 1 then -(dotE D Sc t m ^ 2 - dotE D Sc t p ^ 2) ^ 2
    else (dotE D Sc t m - dotE D Sc t p) ^ 2
  else 1

/-- Ordered product at a fixed source word. Old positions increase from `a+1`;
endomorphism multiplication puts earlier chronological factors on the right. -/
def leadingSourceProduct (t : List I) (i : I) (m : ℕ) : ℕ → List I →
    End ((pres D Sc).obj (ob D t))
  | _, [] => 1
  | a, j :: ν => leadingSourceProduct t i m (a + 1) ν *
      leadingSourceSquare D Sc t i j m (a + 1)

/-- The ordered square-difference product on the original source endpoint. -/
def leadingMoveProduct (i : I) (l ν : List I) :
    End ((pres D Sc).obj (ob D (l ++ i :: ν))) :=
  leadingSourceProduct D Sc (l ++ i :: ν) i l.length l.length ν

theorem endpointDotMonomial_append (t : List I) (ps qs : List ℕ) :
    endpointDotMonomial D Sc t (ps ++ qs) =
      (show End ((pres D Sc).obj (ob D t)) from endpointDotMonomial D Sc t qs) *
        (show End ((pres D Sc).obj (ob D t)) from endpointDotMonomial D Sc t ps) := by
  simp only [endpointDotMonomial, List.map_append, cl_mul]

theorem leadingSourceSquare_expansion (t : List I) (i j : I) (m p : ℕ) :
    leadingSourceSquare D Sc t i j m p =
      ∑ c : Fin 4, leadingBlockCoeff D (k := k) i j c •
        (show End ((pres D Sc).obj (ob D t)) from
          endpointDotMonomial D Sc t (leadingSourceBlockDots D i j m p c)) := by
  by_cases hij : i = j
  · subst j
    by_cases hp : D.parity i = 1
    all_goals
      simp only [leadingSourceSquare, leadingBlockCoeff, leadingSourceBlockDots,
        hp, ite_true, ite_false, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue,
        Fin.sum_univ_zero, add_zero, neg_smul, one_smul, Fin.val_zero, Fin.val_succ]
      simp only [pow_two, sub_mul, mul_sub, neg_sub]
      simp only [dotE_eq_cl D Sc (sChain_dotAny _ _), cl_mul,
        endpointDotMonomial, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append]
      abel
  · simp [leadingSourceSquare, leadingBlockCoeff, leadingSourceBlockDots, hij,
      endpointDotMonomial, cl_nil]

theorem leadingSourceProduct_expansion (t : List I) (i : I) (m a : ℕ) (ν : List I) :
    leadingSourceProduct D Sc t i m a ν =
      ∑ c : MoveChoices ν, leadingMoveCoeff D (k := k) i ν c •
        (show End ((pres D Sc).obj (ob D t)) from
          endpointDotMonomial D Sc t (leadingSourceDots D i m a ν c)) := by
  induction ν generalizing a with
  | nil =>
    change (1 : End ((pres D Sc).obj (ob D t))) = ∑ c : Unit, _
    simp [leadingMoveCoeff, leadingSourceDots, endpointDotMonomial, cl_nil]
  | cons j ν ih =>
    rw [leadingSourceProduct, ih, leadingSourceSquare_expansion]
    conv_rhs =>
      change ∑ c : Fin 4 × MoveChoices ν, _
      rw [Fintype.sum_prod_type]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    simp only [leadingMoveCoeff, leadingSourceDots, endpointDotMonomial_append,
      smul_mul_assoc, mul_smul_comm, smul_smul]

/-- Exact endpoint identification for arbitrary prefixes and words, in either parity. -/
theorem leadingMoveEndpointPolynomial_eq_product (i : I) (l ν : List I) :
    leadingMoveEndpointPolynomial D Sc i l ν = leadingMoveProduct D Sc i l ν := by
  simp only [leadingMoveEndpointPolynomial, collectedSourceSign_leadingMoveBlocks,
    mul_one, collectedSourceDots_leadingMoveBlocks, leadingMoveProduct,
    leadingSourceProduct_expansion]

end OddMath.QuiverHecke
end

end

section

/-!
# Concrete ordered coefficients of the moving product

`prependWordCoefficients_moveHom_ordered` computes the longest-shuffle
coefficient of the prescribed moving homomorphism by a finite sum over local
choices. `leadingMoveOrderedCoefficients_explicit` separates the moving degree
from the old diagonal dot monomial. All distant separation signs cancel for
these square factors, in both parities. The old monomials are already sorted,
and `leadingMoveOrderedCoefficients_nonidentity` excludes every nonidentity
old permutation.

The degree-normalizing sign is trivial on this producer. Invariance under the
separate old matrix twist is not asserted here.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification Categorification.TypeA MonoidalCategory
open scoped Classical
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The moving degree counts only dots at the new source position zero. -/
def sourceMovingDegree : List ℕ → ℕ
  | [] => 0
  | 0 :: ps => sourceMovingDegree ps + 1
  | (_ + 1) :: ps => sourceMovingDegree ps

/-- Dot monomials with the object family fixed to the matrix object family. -/
def wordEndpointDots {n : ℕ} (w : Word I n) (ps : List ℕ) : End (wordObj D Sc w) :=
  endpointDotMonomial D Sc w.1 ps

/-- A positioned dot with the object family fixed. -/
def wordPositionDot {n : ℕ} (w : Word I n) (p : ℕ) : End (wordObj D Sc w) :=
  dotE D Sc w.1 p

/-- Delete moving dots and renumber every old source position. -/
def sourceOldDots : List ℕ → List ℕ
  | [] => []
  | 0 :: ps => sourceOldDots ps
  | (p + 1) :: ps => p :: sourceOldDots ps

theorem sourceMovingDegree_append (ps qs : List ℕ) :
    sourceMovingDegree (ps ++ qs) = sourceMovingDegree ps + sourceMovingDegree qs := by
  induction ps with
  | nil => simp [sourceMovingDegree]
  | cons p ps ih =>
    cases p <;> simp [sourceMovingDegree, ih, Nat.add_right_comm]

omit [Fintype I] in
/-- Odd moving colours have only even moving degrees, including zero. -/
theorem sourceMovingDegree_leadingSourceDots_even (i : I) (hi : D.parity i = 1)
    (a : ℕ) (ν : List I) (c : MoveChoices ν) :
    sourceMovingDegree (leadingSourceDots D i 0 a ν c) % 2 = 0 := by
  induction ν generalizing a with
  | nil => rfl
  | cons j ν ih =>
    rcases c with ⟨b, c⟩
    by_cases hij : i = j
    · subst j
      fin_cases b <;>
        simp [leadingSourceDots, leadingSourceBlockDots, hi,
          sourceMovingDegree, Nat.add_mod, ih]
    · simp [leadingSourceDots, leadingSourceBlockDots, hij, ih]

omit [Fintype I] in
/-- The prescribed leading crossing word is already the canonical descending run. -/
theorem leadingMoveWord_eq_descRun (l ν : List I) :
    leadingMoveWord l ν = descRun l.length ν.length := by
  induction ν generalizing l with
  | nil => rfl
  | cons j ν ih => simp [leadingMoveWord, ih, descRun_succ]

omit [Fintype I] in
/-- Old positions in the finite producer are already in PBW order and bounded. -/
theorem sourceOldDots_leadingSourceDots_ordered (i : I) (a : ℕ)
    (ν : List I) (c : MoveChoices ν) :
    (sourceOldDots (leadingSourceDots D i 0 a ν c)).Pairwise (· ≤ ·) ∧
      ∀ p ∈ sourceOldDots (leadingSourceDots D i 0 a ν c), a ≤ p ∧ p < a + ν.length := by
  induction ν generalizing a with
  | nil => simp [leadingSourceDots, sourceOldDots]
  | cons j ν ih =>
    rcases c with ⟨b, c⟩
    obtain ⟨hs, hb⟩ := ih (a + 1) c
    have hlo : ∀ p ∈ sourceOldDots (leadingSourceDots D i 0 (a + 1) ν c), a ≤ p := by
      intro p hp
      exact Nat.le_trans (Nat.le_succ a) (hb p hp).1
    have hrange : ∀ p ∈ sourceOldDots (leadingSourceDots D i 0 (a + 1) ν c),
        a ≤ p ∧ p < a + (j :: ν).length := by
      intro p hp
      have := hb p hp
      simp only [List.length_cons]
      omega
    by_cases hij : i = j
    · subst j
      rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
      all_goals
        fin_cases b <;>
          simp [leadingSourceDots, leadingSourceBlockDots, hi,
            sourceOldDots, List.pairwise_cons, hs] <;>
          first | exact hrange | exact ⟨hlo, hrange⟩
    · simp only [leadingSourceDots, leadingSourceBlockDots, hij, ↓reduceIte,
        List.nil_append]
      exact ⟨hs, hrange⟩

end OddMath.QuiverHecke
end

end

section

/-!
# Last-output-dot normalization for the long moving shuffle

The position and sign in signed dot normal ordering are evaluated on the
canonical long shuffle. This supplies the scalar normalization needed to compare
output-last-dot coordinates with the input PBW coordinates in
`DeformedMackeyBoundary.md` (2). It does not identify the short submodule.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} {k : Type w} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X)

/-- The last output dot returns to the moving position in every prefix. -/
theorem sourceDotPosition_leadingMoveWord_last (l s : List I) :
    sourceDotPosition (leadingMoveWord l s) (l.length + s.length) = l.length := by
  induction s generalizing l with
  | nil => simp [leadingMoveWord, sourceDotPosition]
  | cons j s ih =>
    rw [leadingMoveWord, sourceDotPosition_append]
    have he : l.length + (j :: s).length = (l ++ [j]).length + s.length := by simp; omega
    rw [he, ih]
    simp [sourceDotPosition, swapNat]

/-- Each incident slide contributes the moving-colour times old-colour parity. -/
theorem sourceDotSign_leadingMoveWord_last (i : I) (l s : List I) :
    sourceDotSign D (k := k) (l ++ i :: s) (leadingMoveWord l s)
      (l.length + s.length) = SKM.zsign k (D.parity i * wordSumParity D s) := by
  induction s generalizing l with
  | nil => simp [leadingMoveWord, sourceDotSign, wordSumParity, SKM.zsign]
  | cons j s ih =>
    rw [leadingMoveWord, sourceDotSign_append]
    have he : l.length + (j :: s).length = (l ++ [j]).length + s.length := by simp; omega
    rw [he, sourceDotPosition_leadingMoveWord_last]
    have ht : tgt (l ++ i :: j :: s) (cw [l.length]) = (l ++ [j]) ++ i :: s := by
      simp [cw, PG.act, List.append_assoc]
    rw [ht, ih]
    simp [sourceDotSign, crossDotExponent, PG.par, wordSumParity, mul_add,
      zsign_add_aux, mul_comm]

/-- The long canonical shuffle sends the last output dot to input position zero. -/
theorem sourceDotPosition_longPrependShuffle_last (s : List I) :
    sourceDotPosition (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹)
      s.length = 0 := by
  rw [canWord_longPrependShuffle]
  have hw := leadingMoveWord_eq_descRun ([] : List I) s
  simp only [List.length_nil] at hw
  rw [← hw]
  simpa using sourceDotPosition_leadingMoveWord_last ([] : List I) s

/-- Exact library sign for the last output dot on the long canonical shuffle. -/
theorem sourceDotSign_longPrependShuffle_last (i : I) (s : List I) :
    sourceDotSign D (k := k) (i :: s)
      (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹) s.length =
      SKM.zsign k (D.parity i * wordSumParity D s) := by
  rw [canWord_longPrependShuffle]
  have hw := leadingMoveWord_eq_descRun ([] : List I) s
  simp only [List.length_nil] at hw
  rw [← hw]
  simpa using sourceDotSign_leadingMoveWord_last D (k := k) i [] s
end OddMath.QuiverHecke
end

end

section

/-!
# Full-coefficient long coordinates of output dots

The signed output-to-input dot transport gives a triangular comparison for the
bare long moving crossing, retaining arbitrary exterior coefficients over `k`.
The last-output-dot specialization evaluates its sign and input position.
These are affine PBW coefficients, not a descended Mackey extraction: transport
of arbitrary output-old arrows and the short-image inclusion remain necessary
for `DeformedMackeyBoundary.md` (2) and (5).
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Output dots on the long crossing have the signed input coordinates,
with the full exterior coefficient retained over the ground ring. -/
theorem prependAffineEquiv_long_output_dots (i : I) (s t : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (ps : List ℕ) (hp : ∀ p ∈ ps, p < s.length + 1)
    (h : SChain (i :: s)
      (pl (i :: s) (cw (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹) ++
        ps.map PG.dot)) t) :
    ∃ h' : SChain (i :: s)
      (pl (i :: s) ((ps.map (sourceDotPosition
        (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹))).map PG.dot ++
        cw (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹))) t,
      ∀ (x : PrependIdx i s t), x.1.2.2.2 = longPrependShuffle s.length →
      prependAffineEquiv D Sc cutoff i s t
        (a ⊗ₜ[k] cl D Sc _ _ _ h) x =
      sourceDotsSign D (k := k) (i :: s)
        (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹) ps •
      prependAffineEquiv D Sc cutoff i s t
        (a ⊗ₜ[k] cl D Sc _ _ _ h') x := by
  obtain ⟨h', he⟩ := dots_down_signed D Sc [] (show (i :: s).length = s.length + 1 from rfl)
    (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹)
    (validWord_canWord _ _) ps hp [] (by simpa using h)
  simp only [List.nil_append, List.append_nil, tgt_nil, crossCount_nil,
    Nat.zero_add, Nat.add_zero, length_canWord, length_inv,
    length_longPrependShuffle] at he h'
  refine ⟨h', ?_⟩
  intro x hx
  have hz := prependBasis_long_repr_eq_zero_of_low D Sc i s t _ he x hx
  simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
    smul_eq_mul] at hz
  rw [sub_eq_zero] at hz
  rw [prependAffineEquiv_tmul, prependAffineEquiv_tmul, hz, mul_smul]
/-- The actual last-output-dot monomial has the evaluated moving parity sign.
No dot on the first input has been substituted in the left-hand side. -/
theorem prependAffineEquiv_long_last_dots (i : I) (s t : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (m : ℕ)
    (h : SChain (i :: s)
      (pl (i :: s) (cw (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹) ++
        (List.replicate m s.length).map PG.dot)) t) :
    ∃ h' : SChain (i :: s)
      (pl (i :: s) ((List.replicate m 0).map PG.dot ++
        cw (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹))) t,
      ∀ (x : PrependIdx i s t), x.1.2.2.2 = longPrependShuffle s.length →
      prependAffineEquiv D Sc cutoff i s t
        (a ⊗ₜ[k] cl D Sc _ _ _ h) x =
      (SKM.zsign k (D.parity i * wordSumParity D s)) ^ m •
      prependAffineEquiv D Sc cutoff i s t
        (a ⊗ₜ[k] cl D Sc _ _ _ h') x := by
  have hp : ∀ p ∈ List.replicate m s.length, p < s.length + 1 := by
    intro p hp
    have he : p = s.length := (List.mem_replicate.mp hp).2
    omega
  obtain ⟨h', he⟩ := prependAffineEquiv_long_output_dots D Sc cutoff i s t a
    (List.replicate m s.length) hp h
  simpa only [List.map_replicate, sourceDotPosition_longPrependShuffle_last,
    sourceDotsSign, sourceDotSign_longPrependShuffle_last, List.prod_replicate] using
    (show ∃ h', ∀ (x : PrependIdx i s t), x.1.2.2.2 = longPrependShuffle s.length →
      prependAffineEquiv D Sc cutoff i s t (a ⊗ₜ[k] cl D Sc _ _ _ h) x =
        sourceDotsSign D (k := k) (i :: s)
          (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹)
          (List.replicate m s.length) •
        prependAffineEquiv D Sc cutoff i s t (a ⊗ₜ[k] cl D Sc _ _ _ h') x from ⟨h', he⟩)

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Long output coordinate functionals on the old-only quotient

`outputLongCoordinate` is a prescribed ground-ring-linear functional on the
existing `Target`, obtained from old-quotient extraction and the evaluated
output-dot sign. `prependOldCoordinate_long_last_dots` descends the bare-long
output-dot comparison through the old-only relations, with full exterior
coefficients and arbitrary balance parity.

This is the coordinate-functional step toward `DeformedMackeyBoundary.md` (2).
Finite polynomial assembly, output-old-arrow transport, the relative short
kernel, corrected-rho intertwining and moving-chain extraction are not asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem prependExtractOld_congr_long (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (hx : x.1.2.2.2 = longPrependShuffle v.length)
    (f g : hom D Sc cutoff (i :: v) w)
    (h : ∀ y : PrependIdx i v w, y.1.2.2.2 = longPrependShuffle v.length →
      prependAffineEquiv D Sc cutoff i v w f y = prependAffineEquiv D Sc cutoff i v w g y) :
    prependExtractOld D Sc cutoff p x f = prependExtractOld D Sc cutoff p x g := by
  unfold prependExtractOld
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  congr 3
  ext y
  simp only [Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply]
  apply h
  exact hx

private theorem long_canWord_one (n : ℕ) : canWord n 1 = [] := by
  apply List.length_eq_zero_iff.mp
  rw [length_canWord, Categorification.TypeA.length_one]

def longOutputIndex (i : I) (v : List I) (m : ℕ) : PrependIdx i v (v ++ [i]) :=
  ⟨(m, [], 1, longPrependShuffle v.length), by simp, by simp, by
    simp only [prependCrossingWord, long_canWord_one, shiftWord, List.map_nil,
      List.append_nil]
    rw [canWord_longPrependShuffle]
    have hw := leadingMoveWord_eq_descRun ([] : List I) v
    simp only [List.length_nil] at hw
    rw [← hw]
    exact tgt_eq (leadingMoveWord_sChain i [] v)⟩

@[simp] theorem longOutputIndex_oldTarget (i : I) (v : List I) (m : ℕ) :
    (longOutputIndex i v m).oldTarget = v := by
  simp [longOutputIndex, PrependIdx.oldTarget, long_canWord_one, cw]

/-- One normalized long coordinate, on the old-only quotient itself. -/
def outputLongCoordinate (p : ZMod 2) (i : I) (v : List I) (m : ℕ) :
    Target D Sc cutoff i v (v ++ [i]) →ₗ[k] Old D Sc cutoff v v :=
  Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
      Old D Sc cutoff v t) (longOutputIndex_oldTarget i v m))
    ((SKM.zsign k (D.parity i * wordSumParity D v)) ^ m •
      prependOldCoordinate D Sc cutoff p (longOutputIndex i v m))

/-- The output/input triangular comparison descends through the old-only relations. -/
theorem prependOldCoordinate_long_last_dots (p : ZMod 2) (i : I) (s t : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (m : ℕ)
    (h : SChain (i :: s)
      (pl (i :: s) (cw (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹) ++
        (List.replicate m s.length).map PG.dot)) t) :
    ∃ h' : SChain (i :: s)
      (pl (i :: s) ((List.replicate m 0).map PG.dot ++
        cw (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹))) t,
      ∀ (x : PrependIdx i s t), x.1.2.2.2 = longPrependShuffle s.length →
      prependOldCoordinate D Sc cutoff p x
        (projection D Sc cutoff i s t (a ⊗ₜ[k] cl D Sc _ _ _ h)) =
      (SKM.zsign k (D.parity i * wordSumParity D s)) ^ m •
      prependOldCoordinate D Sc cutoff p x
        (projection D Sc cutoff i s t (a ⊗ₜ[k] cl D Sc _ _ _ h')) := by
  obtain ⟨h', he⟩ := prependAffineEquiv_long_last_dots D Sc cutoff i s t a m h
  refine ⟨h', ?_⟩
  intro x hx
  let f : hom D Sc cutoff (i :: s) t := a ⊗ₜ[k] cl D Sc _ _ _ h
  let g : hom D Sc cutoff (i :: s) t := a ⊗ₜ[k] cl D Sc _ _ _ h'
  let c : k := (SKM.zsign k (D.parity i * wordSumParity D s)) ^ m
  have hc := prependExtractOld_congr_long D Sc cutoff p x hx f (c • g) (by
    intro y hy
    rw [(prependAffineEquiv D Sc cutoff i s t).map_smul, Finsupp.smul_apply]
    exact he y hy)
  rw [(prependExtractOld D Sc cutoff p x).map_smul] at hc
  change (ideal D Sc cutoff s x.oldTarget).mkQ
      (prependExtractOld D Sc cutoff p x f) =
    c • (ideal D Sc cutoff s x.oldTarget).mkQ
      (prependExtractOld D Sc cutoff p x g)
  rw [hc, map_smul]

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Finite normalized long-coordinate extraction

`outputLongExtraction` assembles the prescribed long coordinate functionals into
an actual finitely supported polynomial row over the old quotient, as required
for `DeformedMackeyBoundary.md` (2). Finite support is proved from the affine
PBW support of an arbitrary quotient representative, not assumed.

The coefficients retain the evaluated bare-long last-output-dot normalization.
Arbitrary output-old-arrow triangularity, the relative-short kernel, moving-chain
S evaluation and corrected-rho compatibility remain separate obligations.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem castCoordinate_zero (i : I) (v w t t' : List I) (e : t = t')
    (f : Target D Sc cutoff i v w →ₗ[k] Old D Sc cutoff v t)
    (z : Target D Sc cutoff i v w) (hz : f z = 0) :
    (Eq.mp (congrArg (fun t => Target D Sc cutoff i v w →ₗ[k]
      Old D Sc cutoff v t) e) f) z = 0 := by
  cases e
  exact hz

theorem outputLongCoordinate_finite_support (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    ∃ N : ℕ, ∀ m, N ≤ m → outputLongCoordinate D Sc cutoff p i v m z = 0 := by
  obtain ⟨f, rfl⟩ := projection_surjective D Sc cutoff i v (v ++ [i]) z
  let c := prependAffineEquiv D Sc cutoff i v (v ++ [i]) f
  refine ⟨c.support.sup (fun x => x.1.1) + 1, ?_⟩
  intro m hm
  unfold outputLongCoordinate
  apply castCoordinate_zero D Sc cutoff i v (v ++ [i]) _ v
    (longOutputIndex_oldTarget i v m)
  rw [LinearMap.smul_apply]
  suffices hz : prependOldCoordinate D Sc cutoff p (longOutputIndex i v m)
      (projection D Sc cutoff i v (v ++ [i]) f) = 0 by rw [hz, smul_zero]
  rw [prependOldCoordinate_projection]
  have he : Finsupp.lcomapDomain (R := k) (longOutputIndex i v m).replaceOld
      (longOutputIndex i v m).replaceOld_injective c = 0 := by
    ext y
    simp only [Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply, Finsupp.zero_apply]
    apply Finsupp.notMem_support_iff.mp
    intro hy
    have hd := Finset.le_sup (f := fun x : PrependIdx i v (v ++ [i]) => x.1.1) hy
    have hdegree : ((longOutputIndex i v m).replaceOld y).1.1 = m := rfl
    rw [hdegree] at hd
    omega
  change (ideal D Sc cutoff v (longOutputIndex i v m).oldTarget).mkQ
    (prependExtractOld D Sc cutoff p (longOutputIndex i v m) f) = 0
  unfold prependExtractOld
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  change (ideal D Sc cutoff v (longOutputIndex i v m).oldTarget).mkQ
    ((twist k p) ((oldAffineEquiv D Sc cutoff v (longOutputIndex i v m).oldTarget).symm
      ((Finsupp.mapRange.linearMap (coefficientTwist D cutoff
        (prependTailParity D (longOutputIndex i v m))))
        (Finsupp.lcomapDomain (R := k) (longOutputIndex i v m).replaceOld
          (longOutputIndex i v m).replaceOld_injective c)))) = 0
  rw [he, map_zero, map_zero, map_zero, map_zero]
/-- All prescribed normalized long coefficients, as a finite polynomial row. -/
def outputLongExtraction (p : ZMod 2) (i : I) (v : List I) :
    Target D Sc cutoff i v (v ++ [i]) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) where
  toFun z := Finsupp.ofSupportFinite
    (fun m => outputLongCoordinate D Sc cutoff p i v m z) (by
      obtain ⟨N, hN⟩ := outputLongCoordinate_finite_support D Sc cutoff p i v z
      apply (Finset.finite_toSet (Finset.range N)).subset
      intro m hm
      simp only [Finset.mem_coe, Finset.mem_range]
      by_contra h
      exact hm (hN m (by omega)))
  map_add' z z' := by
    ext m
    exact (outputLongCoordinate D Sc cutoff p i v m).map_add z z'
  map_smul' c z := by
    ext m
    exact (outputLongCoordinate D Sc cutoff p i v m).map_smul c z

@[simp] theorem outputLongExtraction_apply (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) (m : ℕ) :
    outputLongExtraction D Sc cutoff p i v z m =
      outputLongCoordinate D Sc cutoff p i v m z := rfl

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Explicit normalized moving-source extraction

The old diagonal dot monomials have even parity, so every old matrix twist
acts trivially. Together with the checked moving-degree sign cancellation,
this evaluates the actual content moving source by a finite word/choice sum.
The affine result holds at all old heights; the append tensor result retains
the existing old-height `n+1` scope and the unchanged right coefficient.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification Categorification.TypeA
open scoped Classical
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

omit [Fintype I] in
private theorem oldDots_parity (i : I) (w l μ : List I) (h : w = l ++ μ)
    (c : MoveChoices μ) :
    chainParity D w ((sourceOldDots (leadingSourceDots D i 0 l.length μ c)).map PG.dot) = 0 := by
  induction μ generalizing l with
  | nil => simp [leadingSourceDots, sourceOldDots]
  | cons j μ ih =>
    rcases c with ⟨b, c⟩
    have ht := ih (l ++ [j]) (by simpa [List.append_assoc] using h) c
    simp only [List.length_append, List.length_singleton] at ht
    have hj : w[l.length]? = some j := by simp [h]
    by_cases hij : i = j
    · subst j
      rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
      all_goals
        fin_cases b <;>
          simp [leadingSourceDots, leadingSourceBlockDots, hi, sourceOldDots,
            chainParity, PG.act, PG.par, hj, ht]
    · simpa [leadingSourceDots, leadingSourceBlockDots, hij, sourceOldDots] using ht

omit [Fintype I] in
/-- The old diagonal monomials in the moving product have even total parity. -/
theorem leadingMoveOldDots_twist (i : I) (ν : List I) (c : MoveChoices ν) (q : ZMod 2) :
    Supercategory.twist k q
      (wordEndpointDots D Sc ⟨ν, rfl⟩ (sourceOldDots (leadingSourceDots D i 0 0 ν c))) =
      wordEndpointDots D Sc ⟨ν, rfl⟩ (sourceOldDots (leadingSourceDots D i 0 0 ν c)) := by
  have hp := oldDots_parity D i ν [] ν rfl c
  have hf : Fits ν.length ((sourceOldDots (leadingSourceDots D i 0 0 ν c)).map PG.dot) := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
    have hb := (sourceOldDots_leadingSourceDots_ordered D i 0 ν c).2 p hp |>.2
    change p + 1 ≤ ν.length
    omega
  have hm := cl_mem_chainParity D Sc _
    (show SChain ν (pl ν ((sourceOldDots (leadingSourceDots D i 0 0 ν c)).map PG.dot)) ν from
      by simpa only [tgt_map_dot] using
        sChain_pl ν ((sourceOldDots (leadingSourceDots D i 0 0 ν c)).map PG.dot)) hf
  simp only [List.length_nil] at hp
  rw [hp] at hm
  exact (Supercategory.twist_of_mem q hm).trans (by
    simp [wordEndpointDots, endpointDotMonomial])

end OddMath.QuiverHecke
end

end

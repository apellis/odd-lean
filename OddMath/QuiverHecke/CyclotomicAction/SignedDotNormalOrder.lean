/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.MoveHomLeading
import OddMath.QuiverHecke.SerreWords

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

/-- The recursively tracked input position is the inverse permutation action. -/
theorem sourceDotPosition_eq {n : ℕ} {σ : List ℕ} (hv : ValidWord n σ)
    (p : Fin n) : sourceDotPosition σ p = ((wordProd n σ)⁻¹ p : ℕ) := by
  induction σ generalizing p with
  | nil => simp [sourceDotPosition]
  | cons a σ ih =>
    have ha : a + 1 < n := hv a (by simp)
    have hp : swapNat a p < n := by unfold swapNat; split_ifs <;> omega
    rw [sourceDotPosition, ih (fun x hx => hv x (by simp [hx])) ⟨swapNat a p, hp⟩]
    simp only [wordProd_cons, mul_inv_rev, sadj_inv, Equiv.Perm.mul_apply]
    congr 2
    ext
    rw [sadj_val_of_lt ha]

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

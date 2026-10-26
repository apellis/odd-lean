/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerMeet
import OddMath.QuiverHecke.ShuffleBasis
import OddMath.QuiverHecke.SerreWords
import OddMath.QuiverHecke.Spanning

/-!
# Balance of the moving-strand map on positioned words

Kang–Kashiwara–Oh, arXiv:1206.5933v2, (8.13) and Proposition 8.4: for every positioned word
`gs` on `ν` (a diagram of `R(β)`), placing it to the right of the moving strand `i` and then
applying `g_n ⋯ g_1` equals applying `g_n ⋯ g_1` and then `gs` on the first `n` strands, up to the
sign `(-1)^{p(gs) p(i) p(ν)}`. This is the balance needed for KKO's map
`Q : a e(β, i) ⊗ b ↦ a g_n ⋯ g_1 v(i, β) ⊗ π b` to be well defined over `R(β)`: the generator
cases are `dot_mem_comp_moveHom` and `cross_comp_moveHom_all`.

## Main results

* `chainParity`: the parity of a positioned word on a word `ν`.
* `gen_comp_moveHom`: the balance for one positioned generator.
* `cl_comp_moveHom`: the balance for every positioned word fitting in `ν`.
-/

noncomputable section

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams
open SKM (zsign)

variable {I : Type*} {X : Type*} [AddCommGroup X] (D : SKM.Datum I X) {k : Type*} [CommRing k]
  (Sc : SKM.Scalars D k)

/-- The parity of the positioned word `gs` read on the word `t`. -/
def chainParity : List I → List PG → ZMod 2
  | _, [] => 0
  | t, g :: gs => g.par D t + chainParity (g.act t) gs

@[simp] theorem chainParity_nil (t : List I) : chainParity D t [] = 0 := rfl

@[simp] theorem chainParity_cons (t : List I) (g : PG) (gs : List PG) :
    chainParity D t (g :: gs) = g.par D t + chainParity D (g.act t) gs := rfl

theorem cl_congr_gs {t t' : List I} {gs gs' : List PG} (hg : gs = gs')
    (h : SChain t (pl t gs) t') (h' : SChain t (pl t gs') t') :
    cl D Sc t t' gs h = cl D Sc t t' gs' h' := by
  subst hg
  rfl

theorem sChain_shift_one (i : I) {ν ν' : List I} {gs : List PG} (h : SChain ν (pl ν gs) ν') :
    SChain (i :: ν) (pl (i :: ν) (gs.map (PG.shift 1))) (i :: ν') := by
  have := sChain_wh h [i] []
  rw [show (1 : ℕ) = [i].length from rfl, show i :: ν = [i] ++ ν from rfl, pl_shift]
  simpa using this

theorem sChain_append_one (i : I) {ν ν' : List I} {gs : List PG} (h : SChain ν (pl ν gs) ν')
    (hfit : Fits ν.length gs) : SChain (ν ++ [i]) (pl (ν ++ [i]) gs) (ν' ++ [i]) := by
  rw [pl_append_right [i] hfit]
  simpa using sChain_wh h [] [i]

/-- KKO (8.13) for one positioned generator `g` of `R(β)`, together with the invariance of the
word parity. -/
theorem gen_comp_moveHom (i : I) {ν ν' : List I} (g : PG) (h : SChain ν (pl ν [g]) ν')
    (hfit : Fits ν.length [g]) :
    cl D Sc (i :: ν) (i :: ν') ([g].map (PG.shift 1)) (sChain_shift_one i h) ≫
        moveHom D Sc i [] ν' =
      zsign k (g.par D ν * (D.parity i * wordSumParity D ν)) •
        (moveHom D Sc i [] ν ≫ cl D Sc (ν ++ [i]) (ν' ++ [i]) [g] (sChain_append_one i h hfit)) ∧
      wordSumParity D ν' = wordSumParity D ν := by
  obtain ⟨m, s, v, hν, hg, -, -⟩ := exists_split g 0 ν (Nat.zero_le _)
    (by simpa using hfit g (by simp))
  subst hg
  have ht := tgt_eq h
  cases s with
  | dot x =>
    obtain rfl : ν = m ++ x :: v := by simpa [Shape.dom] using hν
    obtain rfl : ν' = m ++ x :: v := by simpa [PG.ofShape, PG.act] using ht.symm
    refine ⟨?_, rfl⟩
    have key : dotE D Sc (i :: (m ++ x :: v)) ([].length + 1 + m.length) ≫
          moveHom D Sc i [] (m ++ x :: v) =
        zsign k (D.parity x * (D.parity i * wordSumParity D (m ++ x :: v))) •
          (moveHom D Sc i [] (m ++ x :: v) ≫ dotE D Sc (m ++ x :: v ++ [i]) ([].length + m.length)) :=
      dot_mem_comp_moveHom D Sc i x v m [] (m ++ x :: v) (by simp)
    rw [cl_congr_gs D Sc (t := i :: (m ++ x :: v)) (gs' := [.dot ([].length + 1 + m.length)])
        (by simp [PG.ofShape, PG.shift]) _ (sChain_dotAny _ _), ← dotE_eq_cl,
      cl_congr_gs D Sc (t := m ++ x :: v ++ [i]) (gs' := [.dot ([].length + m.length)])
        (by simp [PG.ofShape]) _ (sChain_dotAny _ _), ← dotE_eq_cl]
    have hp : PG.par D (m ++ x :: v) (PG.ofShape (Shape.dot x) (0 + m.length)) = D.parity x := by
      simp [PG.par, PG.ofShape]
    rw [hp]
    exact key
  | cross j c =>
    obtain rfl : ν = m ++ j :: c :: v := by simpa [Shape.dom] using hν
    obtain rfl : ν' = m ++ c :: j :: v := by
      simpa [PG.ofShape, PG.act, List.take_append, List.drop_append] using ht.symm
    refine ⟨?_, ?_⟩
    · have key : cl D Sc (i :: (m ++ j :: c :: v)) (i :: (m ++ c :: j :: v))
            [.cross ([].length + 1 + m.length)] (sChain_mid₁ [] m v i j c) ≫
            moveHom D Sc i [] (m ++ c :: j :: v) =
          zsign k (D.parity j * D.parity c *
              (D.parity i * (wordSumParity D m + wordSumParity D v))) •
            (moveHom D Sc i [] (m ++ j :: c :: v) ≫
              cl D Sc (m ++ j :: c :: v ++ [i]) (m ++ c :: j :: v ++ [i])
                [.cross ([].length + m.length)] (sChain_mid₂ [] m v i j c)) :=
        cross_comp_moveHom_all D Sc v i j c m []
      rw [cl_congr_gs D Sc (t := i :: (m ++ j :: c :: v)) (t' := i :: (m ++ c :: j :: v))
          (gs' := [.cross ([].length + 1 + m.length)])
          (by simp [PG.ofShape, PG.shift, Nat.add_comm]) _ (sChain_mid₁ [] m v i j c),
        cl_congr_gs D Sc (t := m ++ j :: c :: v ++ [i]) (t' := m ++ c :: j :: v ++ [i])
          (gs' := [.cross ([].length + m.length)]) (by simp [PG.ofShape]) _
          (sChain_mid₂ [] m v i j c)]
      rw [key]
      congr 1
      have hp : PG.par D (m ++ j :: c :: v) (PG.ofShape (Shape.cross j c) (0 + m.length)) =
          D.parity j * D.parity c := by simp [PG.par, PG.ofShape]
      rw [hp]
      simp only [wordSumParity, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      generalize D.parity i = a
      generalize D.parity j = b
      generalize D.parity c = d
      generalize (List.map D.parity m).sum = e
      generalize (List.map D.parity v).sum = f
      congr 1
      revert a b d e f
      decide
    · simp only [wordSumParity, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      abel

/-- KKO (8.13) for every positioned word `gs` on `ν`: placed to the right of the moving strand,
it passes through `g_n ⋯ g_1` with the sign `(-1)^{p(gs) p(i) p(ν)}`. -/
theorem cl_comp_moveHom (i : I) : ∀ {ν ν' : List I} (gs : List PG) (h : SChain ν (pl ν gs) ν')
    (hfit : Fits ν.length gs),
    cl D Sc (i :: ν) (i :: ν') (gs.map (PG.shift 1)) (sChain_shift_one i h) ≫
        moveHom D Sc i [] ν' =
      zsign k (chainParity D ν gs * (D.parity i * wordSumParity D ν)) •
        (moveHom D Sc i [] ν ≫ cl D Sc (ν ++ [i]) (ν' ++ [i]) gs (sChain_append_one i h hfit)) ∧
      wordSumParity D ν' = wordSumParity D ν
  | ν, ν', [], h, _ => by
    obtain rfl : ν = ν' := h
    refine ⟨?_, rfl⟩
    simp [cl_nil, zsign]
  | ν, ν', g :: gs, h, hfit => by
    have h₁ : SChain ν (pl ν [g]) (g.act ν) := sChain_pl ν [g]
    have h₂ : SChain (g.act ν) (pl (g.act ν) gs) ν' := by
      have := tgt_eq h
      simpa [← this] using sChain_pl (g.act ν) gs
    have hfit₁ : Fits ν.length [g] := fun g' hg' => hfit g' (by simp_all)
    have hfit₂ : Fits (g.act ν).length gs := by
      rw [length_act]; exact fun g' hg' => hfit g' (by simp [hg'])
    obtain ⟨e₁, p₁⟩ := gen_comp_moveHom D Sc i g h₁ hfit₁
    obtain ⟨e₂, p₂⟩ := cl_comp_moveHom i gs h₂ hfit₂
    refine ⟨?_, p₂.trans p₁⟩
    have s₁ : cl D Sc (i :: ν) (i :: ν') ((g :: gs).map (PG.shift 1)) (sChain_shift_one i h) =
        cl D Sc (i :: ν) (i :: g.act ν) ([g].map (PG.shift 1)) (sChain_shift_one i h₁) ≫
          cl D Sc (i :: g.act ν) (i :: ν') (gs.map (PG.shift 1)) (sChain_shift_one i h₂) := by
      rw [cl_comp]; rfl
    have s₂ : cl D Sc (ν ++ [i]) (ν' ++ [i]) (g :: gs) (sChain_append_one i h hfit) =
        cl D Sc (ν ++ [i]) (g.act ν ++ [i]) [g] (sChain_append_one i h₁ hfit₁) ≫
          cl D Sc (g.act ν ++ [i]) (ν' ++ [i]) gs (sChain_append_one i h₂ hfit₂) := by
      rw [cl_comp]; rfl
    rw [s₁, s₂, Category.assoc, e₂, Linear.comp_smul, ← Category.assoc, e₁, Linear.smul_comp,
      smul_smul, Category.assoc, p₁, chainParity_cons, ← zsign_add_eq]
    congr 2
    ring

import OddMath.SKM.RightCapAttachment
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.List.Rotate

/-!
# Cyclic endpoint changes for matching pairings

The pairing-class coverage step in the upward-to-oriented reduction of
Brundan–Ellis §8: cyclic cuts preserve pairing isomorphism, validity and
oriented endpoint letters. No preservation of strict reducedness is asserted.
-/
namespace StringDiagrams.Chord

variable {α : Type*}

private def rotationIndex (m n : ℕ) : Equiv.Perm (Fin m) :=
  if h : 0 < m then finCycle ⟨n % m, Nat.mod_lt _ h⟩ else _root_.Equiv.refl _

private theorem rotationIndex_val (m n : ℕ) (i : Fin m) :
    (rotationIndex m n i).val = (i.val + n) % m := by
  have hm : 0 < m := i.pos
  simp [rotationIndex, hm, finCycle, Fin.add_def, Nat.add_mod]

theorem same_rotate_iff {s : List (ℕ × α)} (n : ℕ) {i j : ℕ}
    (hi : i < s.length) (hj : j < s.length) :
    Same (s.rotate n) i j ↔
      Same s ((i + n) % s.length) ((j + n) % s.length) := by
  let e := rotationIndex s.length n
  have hne : i ≠ j ↔ (i + n) % s.length ≠ (j + n) % s.length := by
    have he : (e ⟨i, hi⟩).val = (e ⟨j, hj⟩).val ↔ i = j := by
      constructor
      · intro h
        exact congrArg Fin.val (e.injective (Fin.ext h))
      · rintro rfl; rfl
    simpa only [e, rotationIndex_val] using not_congr he.symm
  have hp : 0 < s.length := by omega
  simp only [Same, idAt, List.getElem?_rotate hi, List.getElem?_rotate hj,
    List.getElem?_eq_getElem (Nat.mod_lt _ hp), Option.map_some, ne_eq,
    reduceCtorEq, not_false_eq_true, true_and, Option.some.injEq]
  exact and_congr hne Iff.rfl

theorem Iso.rotate {s t : List (ℕ × α)} (h : Iso s t) (n : ℕ) :
    Iso (s.rotate n) (t.rotate n) := by
  refine ⟨by simpa only [List.map_rotate] using congrArg (fun l => l.rotate n) h.1, ?_⟩
  intro i j
  by_cases hi : i < s.length
  · by_cases hj : j < s.length
    · rw [same_rotate_iff n hi hj,
        same_rotate_iff n (h.length_eq ▸ hi) (h.length_eq ▸ hj)]
      simpa only [h.length_eq] using h.2 ((i + n) % s.length) ((j + n) % s.length)
    · constructor <;> intro hs
      · exact False.elim (hj (by simpa only [List.length_rotate] using hs.lt_right))
      · exact False.elim (hj (by simpa only [List.length_rotate, ← h.length_eq] using hs.lt_right))
  · constructor <;> intro hs
    · exact False.elim (hi (by simpa only [List.length_rotate] using hs.lt_left))
    · exact False.elim (hi (by simpa only [List.length_rotate, ← h.length_eq] using hs.lt_left))

theorem Valid.rotate {s : List (ℕ × α)} (h : Valid s) (n : ℕ) :
    Valid (s.rotate n) := by
  intro i hi
  have hi' : i < s.length := by simpa only [List.length_rotate] using hi
  let e := rotationIndex s.length n
  obtain ⟨j, hj, hu⟩ := h (e ⟨i, hi'⟩).val (e ⟨i, hi'⟩).isLt
  let q := e.symm ⟨j, hj.lt_right⟩
  have hq : (q.val + n) % s.length = j := by
    rw [← rotationIndex_val s.length n q]
    exact congrArg Fin.val (e.apply_symm_apply ⟨j, hj.lt_right⟩)
  refine ⟨q.val, ?_, ?_⟩
  · change Same (s.rotate n) i q.val
    rw [same_rotate_iff n hi' q.isLt, hq]
    simpa only [e, rotationIndex_val] using hj
  · intro k hk
    have hk' : k < s.length := by simpa only [List.length_rotate] using hk.lt_right
    have hs := (same_rotate_iff n hi' hk').mp hk
    have he : (e ⟨k, hk'⟩).val = j := hu _ (by
      simpa only [e, rotationIndex_val] using hs)
    have hfin : (⟨k, hk'⟩ : Fin s.length) = q := by
      apply e.injective
      apply Fin.ext
      simpa only [q, e.apply_symm_apply] using he
    exact congrArg Fin.val hfin

theorem Lettered.snd_eq_of_same {d : α → α} (hd : Function.Involutive d)
    {s : List (ℕ × α)} (h : Lettered d s) {i j : ℕ} (hs : Same s i j) :
    (s[j]'hs.lt_right).2 = d (s[i]'hs.lt_left).2 := by
  by_cases hij : i < j
  · simpa only [List.getElem?_eq_getElem hs.lt_right,
      List.getElem?_eq_getElem hs.lt_left, Option.map_some, Option.some.injEq,
      Function.comp_apply] using h i j hs hij
  · have hji : j < i := by have := hs.ne; omega
    have he : (s[i]'hs.lt_left).2 = d (s[j]'hs.lt_right).2 := by
      simpa only [List.getElem?_eq_getElem hs.lt_right,
        List.getElem?_eq_getElem hs.lt_left, Option.map_some, Option.some.injEq,
        Function.comp_apply] using h j i hs.symm hji
    rw [he, hd]

theorem Lettered.rotate {d : α → α} (hd : Function.Involutive d)
    {s : List (ℕ × α)} (h : Lettered d s) (n : ℕ) : Lettered d (s.rotate n) := by
  intro i j hs _
  have hi : i < s.length := by simpa only [List.length_rotate] using hs.lt_left
  have hj : j < s.length := by simpa only [List.length_rotate] using hs.lt_right
  have hp := (same_rotate_iff n hi hj).mp hs
  rw [List.getElem?_rotate hi, List.getElem?_rotate hj]
  simpa only [List.getElem?_eq_getElem hp.lt_left,
    List.getElem?_eq_getElem hp.lt_right, Option.map_some, Option.some.injEq,
    Function.comp_apply] using h.snd_eq_of_same hd hp

theorem rotate_undo (s : List α) (n : ℕ) :
    (s.rotate n).rotate (s.length - n % s.length) = s := by
  have h := (List.rotate_eq_iff (l := s) (l' := s.rotate n) (n := n)).mp rfl
  simpa only [List.length_rotate] using h.symm

theorem iso_rotate_iff (s t : List (ℕ × α)) (n : ℕ) :
    Iso (s.rotate n) (t.rotate n) ↔ Iso s t := by
  refine ⟨fun h => ?_, fun h => h.rotate n⟩
  have hlen : s.length = t.length := by simpa only [List.length_rotate] using h.length_eq
  have hh := h.rotate (s.length - n % s.length)
  rw [rotate_undo, hlen, rotate_undo] at hh
  exact hh

theorem valid_rotate_iff (s : List (ℕ × α)) (n : ℕ) :
    Valid (s.rotate n) ↔ Valid s := by
  refine ⟨fun h => ?_, fun h => h.rotate n⟩
  have hh := h.rotate (s.length - n % s.length)
  rwa [rotate_undo] at hh

theorem lettered_rotate_iff {d : α → α} (hd : Function.Involutive d)
    (s : List (ℕ × α)) (n : ℕ) : Lettered d (s.rotate n) ↔ Lettered d s := by
  refine ⟨fun h => ?_, fun h => h.rotate hd n⟩
  have hh := h.rotate hd (s.length - n % s.length)
  rwa [rotate_undo] at hh

end StringDiagrams.Chord

namespace OddMath.SKM.RightCapAttachment
open StringDiagrams StringDiagrams.Chord
variable {I : Type*}

theorem attach_pairing_rotate {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R) :
    Iso (pairing₂ (a ++ [x]) (attach b R))
      ((pairing₂ a R).rotate ((pairing₂ a R).length - 1)) := by
  obtain ⟨P, q, hp, hi⟩ := attach_pairing_iso hR
  simpa only [hp, List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.rotate_append_length_eq, List.singleton_append] using hi

theorem suffix_pairing_rotate {a b w : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ w) R) :
    Iso (pairing₂ (a ++ dualW w) (suffixMatching b w R))
      ((pairing₂ a R).rotate ((pairing₂ a R).length - w.length)) := by
  induction w generalizing a b R with
  | nil => simpa only [suffixMatching, dualW_nil, List.append_nil,
      List.length_nil, Nat.sub_zero, List.rotate_length] using Iso.refl (pairing₂ a R)
  | cons y w ih =>
    have hR' : IsMatching₂ a ((b ++ [y]) ++ w) R := by simpa using hR
    have hm : IsMatching₂ (a ++ dualW w) (b ++ [flipL (flipL y)])
        (suffixMatching (b ++ [y]) w R) := by
      simpa only [flipL_involutive y] using suffix_matching hR'
    have hi := ih hR'
    have ha := attach_pairing_rotate hm
    have hlen : (pairing₂ (a ++ dualW w) (suffixMatching (b ++ [y]) w R)).length =
        (pairing₂ a R).length := by simpa only [List.length_rotate] using hi.length_eq
    have hbound : w.length + 1 ≤ (pairing₂ a R).length := by
      have hh := congrArg List.length hR.pairing_properties.2.2
      simp only [List.length_map, List.length_append, length_dualW, List.length_cons] at hh
      omega
    have hx := ha.trans (hi.rotate
      ((pairing₂ (a ++ dualW w) (suffixMatching (b ++ [y]) w R)).length - 1))
    rw [hlen, List.rotate_rotate] at hx
    have he : (pairing₂ a R).length - w.length + ((pairing₂ a R).length - 1) =
        (pairing₂ a R).length + ((pairing₂ a R).length - (w.length + 1)) := by omega
    rw [he, ← List.rotate_rotate, List.rotate_length] at hx
    simpa only [suffixMatching, dualW_cons, List.append_assoc, List.length_cons] using hx

theorem suffix_pairing_iso_iff {a b w : List (Letter I)}
    {R S : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ w) R)
    (hS : IsMatching₂ a (b ++ w) S) :
    Iso (pairing₂ (a ++ dualW w) (suffixMatching b w R))
      (pairing₂ (a ++ dualW w) (suffixMatching b w S)) ↔
      Iso (pairing₂ a R) (pairing₂ a S) := by
  have hlen : (pairing₂ a R).length = (pairing₂ a S).length := by
    simpa only [List.length_map] using congrArg List.length
      (hR.pairing_properties.2.2.trans hS.pairing_properties.2.2.symm)
  have hr := suffix_pairing_rotate hR
  have hs := suffix_pairing_rotate hS
  rw [← hlen] at hs
  constructor
  · intro h
    exact (iso_rotate_iff _ _ _).mp (hr.symm.trans (h.trans hs))
  · intro h
    exact hr.trans ((h.rotate _).trans hs.symm)

/-- Reverse the cyclic boundary change, realize that pairing strictly, then
apply the literal suffix mate. The resulting mate need only be weakly reduced. -/
theorem exists_strict_suffix_preimage {a b w : List (Letter I)}
    {S : List (TMove (Letter I))} (hS : IsMatching₂ (a ++ dualW w) b S) :
    ∃ R, IsMatching₂ a (b ++ w) R ∧ StrictReduced₂ a R ∧
      Iso (pairing₂ (a ++ dualW w) (suffixMatching b w R))
        (pairing₂ (a ++ dualW w) S) := by
  let s := pairing₂ (a ++ dualW w) S
  obtain ⟨hv, hl, hs⟩ := hS.pairing_properties
  have hletters : (s.rotate w.length).map Prod.snd = dualW a ++ (b ++ w) := by
    rw [List.map_rotate]
    change ((pairing₂ (a ++ dualW w) S).map Prod.snd).rotate w.length = _
    rw [hs, dualW_append, dualW_dualW, List.append_assoc,
      List.rotate_append_length_eq]
    simp only [List.append_assoc]
  obtain ⟨R, hR, hred, hi⟩ := exists_strictReduced_matching
    (hv.rotate w.length) (hl.rotate flipL_involutive w.length) hletters
  have hlen : (pairing₂ a R).length = s.length := by
    simpa only [List.length_rotate] using hi.length_eq
  have hbound : w.length ≤ s.length := by
    have hh := congrArg List.length hs
    simp only [List.length_map, List.length_append, length_dualW] at hh
    change w.length ≤ (pairing₂ (a ++ dualW w) S).length
    omega
  refine ⟨R, hR, hred, ?_⟩
  have hh := (suffix_pairing_rotate hR).trans
    (hi.rotate ((pairing₂ a R).length - w.length))
  rw [hlen, List.rotate_rotate, Nat.add_sub_of_le hbound, List.rotate_length] at hh
  exact hh

end OddMath.SKM.RightCapAttachment

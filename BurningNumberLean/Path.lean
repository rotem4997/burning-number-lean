/-
Copyright 2026 Rotem Ashkenazi.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.Paper.BurningNumberConjecture

/-!
# The burning number of a path

Burning a graph: in round $i$ one new vertex is set on fire, and every burning vertex sets its
neighbours on fire in the next round. The burning number $b(G)$ is the least number of rounds
that burns every vertex. Bonato, Janssen and Roshanbin [BJR16] showed that the path $P_n$ on
$n \ge 1$ vertices has $b(P_n) = \lceil \sqrt n \rceil$, so the burning number conjecture
($b(G) \le \lceil \sqrt n \rceil$ for connected $G$) would be sharp. This file proves it.

The definitions `BurningNumberConjecture.IsBurningSequence` and
`BurningNumberConjecture.burningNumber` come from `FormalConjectures/Paper/BurningNumberConjecture.lean`
in [formal-conjectures](https://github.com/google-deepmind/formal-conjectures). The main theorem
`BurningNumberConjecture.Path.burningNumber_pathGraph` has exactly the type of
`burning_number_conjecture.variants.path` there.

## Proof

* In the path, $\mathrm{dist}(a, b) = \lvert a - b\rvert$ (`le_dist`, `dist_le`).
* Lower bound (`card_le_sq`): the fire lit in round $i$ of $k$ reaches only the
  $2(k - 1 - i) + 1$ vertices within distance $k - 1 - i$. So
  $n \le \sum_{i < k} (2(k - 1 - i) + 1) = k^2$.
* Upper bound (`exists_isBurningSequence`): if $n \le k^2$, cut the path into consecutive blocks
  of $2k - 1, 2k - 3, \ldots, 1$ vertices and light fire $i$ in the middle of block $i$.

[BJR16] A. Bonato, J. Janssen and E. Roshanbin, *How to burn a graph*, Internet Math. 12 (2016),
85–100, [arXiv:1507.06524](https://arxiv.org/abs/1507.06524).
-/

namespace BurningNumberConjecture.Path

open Finset SimpleGraph

/-- In the path graph, a walk from `a` to `b` has length at least `|a - b|`. -/
theorem le_length {n : ℕ} {a b : Fin n} (p : (pathGraph n).Walk a b) :
    (a : ℕ) ≤ b + p.length ∧ (b : ℕ) ≤ a + p.length := by
  induction p with
  | nil => simp
  | cons h q ih =>
    rw [pathGraph_adj] at h
    simp only [Walk.length_cons]
    omega

/-- In the path graph, `|a - b| ≤ dist a b`. -/
theorem le_dist {n : ℕ} (a b : Fin n) :
    (a : ℕ) ≤ b + (pathGraph n).dist a b ∧ (b : ℕ) ≤ a + (pathGraph n).dist a b := by
  obtain ⟨p, hp⟩ := (pathGraph_preconnected n a b).exists_walk_length_eq_dist
  rw [← hp]
  exact le_length p

/-- In the path graph, there is a walk from `a` to `b` of length `b - a` when `a ≤ b`. -/
theorem exists_walk {n : ℕ} : ∀ (d : ℕ) (a b : Fin n), (a : ℕ) + d = b →
    ∃ p : (pathGraph n).Walk a b, p.length = d := by
  intro d
  induction d with
  | zero =>
    intro a b h
    have : a = b := Fin.ext (by omega)
    subst this
    exact ⟨Walk.nil, rfl⟩
  | succ d ih =>
    intro a b h
    have hb : (a : ℕ) + 1 < n := by omega
    obtain ⟨p, hp⟩ := ih ⟨a + 1, hb⟩ b (by simp; omega)
    have hadj : (pathGraph n).Adj a ⟨a + 1, hb⟩ := by rw [pathGraph_adj]; simp
    exact ⟨Walk.cons hadj p, by simp [hp]⟩

/-- In the path graph, `dist a b ≤ |a - b|`. -/
theorem dist_le {n : ℕ} (a b : Fin n) :
    (pathGraph n).dist a b + min (a : ℕ) b ≤ max (a : ℕ) b := by
  rcases le_total (a : ℕ) b with h | h
  · obtain ⟨p, hp⟩ := exists_walk ((b : ℕ) - a) a b (by omega)
    have := SimpleGraph.dist_le p
    omega
  · obtain ⟨p, hp⟩ := exists_walk ((a : ℕ) - b) b a (by omega)
    have := SimpleGraph.dist_le p
    rw [SimpleGraph.dist_comm] at this
    omega

/-- `1 + 3 + ⋯ + (2k - 1) = k²`, summed from the largest term. -/
theorem sum_odd (k : ℕ) : ∑ t ∈ range k, (2 * (k - 1 - t) + 1) = k ^ 2 := by
  rw [Finset.sum_range_reflect (fun t => 2 * t + 1) k]
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-- **Lower bound.** A burning sequence of length `k` for the path on `n` vertices has
`n ≤ k²`: the `i`-th fire covers at most `2(k - 1 - i) + 1` vertices. -/
theorem card_le_sq {n k : ℕ} (x : Fin k → Fin n) (hx : IsBurningSequence (pathGraph n) x) :
    n ≤ k ^ 2 := by
  classical
  set B : Fin k → Finset (Fin n) :=
    fun i => univ.filter (fun v => (pathGraph n).dist (x i) v + (i : ℕ) < k)
  have hcover : (univ : Finset (Fin n)) ⊆ univ.biUnion B := by
    intro v _
    obtain ⟨i, -, hi⟩ := hx v
    exact mem_biUnion.2 ⟨i, mem_univ _, mem_filter.2 ⟨mem_univ _, hi⟩⟩
  have hB : ∀ i : Fin k, (B i).card ≤ 2 * (k - 1 - i) + 1 := by
    intro i
    have hsub : (B i).map Fin.valEmbedding ⊆
        Icc ((x i : ℕ) - (k - 1 - i)) ((x i : ℕ) + (k - 1 - i)) := by
      intro m hm
      obtain ⟨v, hv, rfl⟩ := mem_map.1 hm
      have hv' := (mem_filter.1 hv).2
      have := le_dist (x i) v
      simp only [Fin.valEmbedding_apply, mem_Icc]
      omega
    have := card_le_card hsub
    rw [card_map, Nat.card_Icc] at this
    omega
  have h1 := card_le_card hcover
  have h2 := card_biUnion_le (s := (univ : Finset (Fin k))) (t := B)
  have h3 : ∑ i : Fin k, (B i).card ≤ ∑ i : Fin k, (2 * (k - 1 - i) + 1) :=
    sum_le_sum fun i _ => hB i
  rw [Fin.sum_univ_eq_sum_range (fun i => 2 * (k - 1 - i) + 1), sum_odd] at h3
  rw [card_univ, Fintype.card_fin] at h1
  omega

/-- The left end of the `j`-th interval: `(2k - 1) + (2k - 3) + ⋯`, with `j` terms. -/
def start (k j : ℕ) : ℕ := ∑ t ∈ range j, (2 * (k - 1 - t) + 1)

theorem start_succ (k j : ℕ) : start k (j + 1) = start k j + (2 * (k - 1 - j) + 1) :=
  sum_range_succ _ _

/-- **Upper bound.** If `n ≤ k²` then the path on `n` vertices has a burning sequence of length
`k`: the `i`-th fire is lit in the middle of the `i`-th block of `2(k - 1 - i) + 1` vertices. -/
theorem exists_isBurningSequence {n k : ℕ} (hn : 1 ≤ n) (hk : n ≤ k ^ 2) :
    ∃ x : Fin k → Fin n, IsBurningSequence (pathGraph n) x := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk; omega
    · exact h
  refine ⟨fun i => ⟨min (start k i + (k - 1 - i)) (n - 1), by omega⟩, ?_⟩
  intro v
  have hkk : start k k = k ^ 2 := sum_odd k
  have hex : ∃ j, (v : ℕ) < start k (j + 1) :=
    ⟨k - 1, by rw [show k - 1 + 1 = k by omega, hkk]; omega⟩
  set i := Nat.find hex with hi_def
  have hi : (v : ℕ) < start k (i + 1) := Nat.find_spec hex
  have hik : i ≤ k - 1 := Nat.find_min' hex (by rw [show k - 1 + 1 = k by omega, hkk]; omega)
  have hlow : start k i ≤ v := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [h0]; simp [start]
    · have := Nat.find_min hex (show i - 1 < i by omega)
      rw [show i - 1 + 1 = i by omega] at this
      omega
  refine ⟨⟨i, by omega⟩, pathGraph_preconnected n _ _, ?_⟩
  have hd := dist_le (⟨min (start k i + (k - 1 - i)) (n - 1), by omega⟩ : Fin n) v
  have hs := start_succ k i
  simp only at hd ⊢
  omega

/-- **Bonato–Janssen–Roshanbin [BJR16].** The path on `n ≥ 1` vertices has burning number
`⌈√n⌉`. -/
theorem burningNumber_pathGraph (n : ℕ) (hn : 1 ≤ n) :
    burningNumber (pathGraph n) = ⌈Real.sqrt n⌉₊ := by
  set k := ⌈Real.sqrt n⌉₊ with hk_def
  have hk : n ≤ k ^ 2 := by
    have h1 : Real.sqrt n ≤ k := Nat.le_ceil _
    have h2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
    have h3 : (n : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [Real.sqrt_nonneg (n : ℝ)]
    exact_mod_cast h3
  have hne : {k | ∃ x : Fin k → Fin n, IsBurningSequence (pathGraph n) x}.Nonempty :=
    ⟨k, exists_isBurningSequence hn hk⟩
  apply le_antisymm
  · exact Nat.sInf_le (exists_isBurningSequence hn hk)
  · obtain ⟨x, hx⟩ := Nat.sInf_mem hne
    have hsq := card_le_sq x hx
    apply Nat.ceil_le.2
    calc Real.sqrt n ≤ Real.sqrt ((burningNumber (pathGraph n) : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by exact_mod_cast hsq)
      _ = burningNumber (pathGraph n) := Real.sqrt_sq (Nat.cast_nonneg _)

/-- The statement matches `burning_number_conjecture.variants.path` in formal-conjectures. -/
example : type_of% @burning_number_conjecture.variants.path := @burningNumber_pathGraph

end BurningNumberConjecture.Path

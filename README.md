# The burning number of a path, in Lean 4

A machine-checked proof that **the path on n vertices has burning number ⌈√n⌉**
(Bonato, Janssen and Roshanbin, 2016).

## The statement

Burning a graph works in rounds. In each round you set one new vertex on fire, and every vertex
already on fire spreads it to its neighbours. The burning number b(G) is the least number of
rounds needed to burn every vertex.

The burning number conjecture says that every connected graph on n vertices burns in at most
⌈√n⌉ rounds. It is still open. Paths show that the bound would be the best possible:

  **b(Pₙ) = ⌈√n⌉ for every n ≥ 1.**

## The proof

- In a path, the distance between vertices a and b is |a − b|.
- **Lower bound.** With k rounds, the fire lit in round i spreads for k − 1 − i more rounds. So it
  reaches at most 2(k − 1 − i) + 1 vertices. In total that is at most
  (2k − 1) + (2k − 3) + ⋯ + 1 = k² vertices, so n ≤ k².
- **Upper bound.** If n ≤ k², cut the path into consecutive blocks of 2k − 1, 2k − 3, …, 1
  vertices. In round i, light a fire in the middle of block i. It reaches exactly that block in
  time.

## Lean

- `BurningNumberLean/Path.lean`: the whole proof, about 190 lines, with only the standard axioms
  `propext`, `Classical.choice` and `Quot.sound`.
- `BurningNumberConjecture.Path.burningNumber_pathGraph`: the main theorem. It has exactly the type
  of `burning_number_conjecture.variants.path` in Google DeepMind's
  [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  (`FormalConjectures/Paper/BurningNumberConjecture.lean`), which is checked by
  `example : type_of% @burning_number_conjecture.variants.path := @burningNumber_pathGraph`.

```bash
lake exe cache get
lake build
```

## Reference

A. Bonato, J. Janssen and E. Roshanbin, *How to burn a graph*, Internet Math. 12 (2016), 85–100,
[arXiv:1507.06524](https://arxiv.org/abs/1507.06524).

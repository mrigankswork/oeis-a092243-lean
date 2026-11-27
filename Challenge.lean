/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Mrigank.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Algebra.BigOperators.Intervals

/-!
# OEIS A092243, conjecture 1 (challenge)

The definitions `primeGap`, `a` and the statement of `conjecture1` are copied verbatim (by
`scripts/gen_challenge.py`) from google-deepmind/formal-conjectures@9097e2f,
`FormalConjectures/OEIS/92243.lean`. Only the `@[category ...]` attribute is dropped (it comes from
`FormalConjecturesUtil` and has no logical content). The elaborated `primeGap`, `a` and the type of
`conjecture1` are identical (`Expr` dump, byte for byte) to upstream's.
-/

namespace OeisA92243

/-- The $n$-th prime gap $g(n) = p_n - p_{n-1}$ for $n \ge 1$,
where $p_i$ is the $i$-th prime (0-indexed). -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)

/-- Score at stage $n$ in "tug of war" between prime gap increases vs. prime gap decreases. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n ≤ 1 then 0
  else
    ∑ k ∈ Finset.Icc 2 n,
      ((primeGap k : ℤ) - (primeGap (k - 1) : ℤ)).sign

/--
Is the score $a(n) > 0$ for some $n > 250000$?-/
theorem conjecture1 : ∃ n > 250000, a n > 0 := by
  sorry

end OeisA92243

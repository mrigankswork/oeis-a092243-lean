#!/usr/bin/env python3
"""Generate Challenge.lean and Solution.lean from the upstream formal-conjectures file.

The definitions `primeGap`, `a` (with their docstrings) and the statement of `conjecture1` are
copied verbatim; only the `@[category ...]` attribute line (from FormalConjecturesUtil, no logical
content) is dropped. Identity of the elaborated terms with upstream's is checked separately by
dumping the `Expr`s in both environments (see the repository README).

Usage (from the repository root):
  python3 scripts/gen_challenge.py path/to/formal-conjectures/FormalConjectures/OEIS/92243.lean
"""
import pathlib
import sys

up = pathlib.Path(sys.argv[1]).read_text().split("\n")
start = up.index("/-- The $n$-th prime gap $g(n) = p_n - p_{n-1}$ for $n \\ge 1$,")
end = next(i for i in range(start, len(up)) if up[i].strip().endswith(".sign")) + 1
defs = "\n".join(up[start:end])
c1 = up.index("theorem conjecture1 : ∃ n > 250000, a n > 0 := by")
doc = c1 - 1
while not up[doc].startswith("/--"):
    doc -= 1
stmt = "\n".join(l for l in up[doc:c1 + 2] if not l.startswith("@[category"))
assert "noncomputable def primeGap" in defs and "noncomputable def a" in defs
assert stmt.rstrip().endswith("sorry") and stmt.count("theorem") == 1

LICENSE = """/-
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
"""
# Only what the definitions need (upstream imports all of Mathlib via FormalConjecturesUtil;
# the elaborated terms are the same, which the Expr dump check confirms). This keeps a full
# `lake build` small in memory.
IMPORTS = "module\n\npublic import Mathlib.Data.Nat.Prime.Nth\npublic import Mathlib.Algebra.BigOperators.Intervals\n"
NOTE = """The definitions `primeGap`, `a` and the statement of `conjecture1` are copied verbatim (by
`scripts/gen_challenge.py`) from google-deepmind/formal-conjectures@9097e2f,
`FormalConjectures/OEIS/92243.lean`. Only the `@[category ...]` attribute is dropped (it comes from
`FormalConjecturesUtil` and has no logical content). The elaborated `primeGap`, `a` and the type of
`conjecture1` are identical (`Expr` dump, byte for byte) to upstream's."""

challenge = LICENSE + IMPORTS + f"""
/-!
# OEIS A092243, conjecture 1 (challenge)

{NOTE}
-/

@[expose] public section

namespace OeisA92243

{defs}

{stmt}

end OeisA92243

end
"""

proof_doc = stmt.split("theorem")[0]
solution = LICENSE + IMPORTS + "public import OeisA92243.Bridge\n" + f"""
/-!
# OEIS A092243, conjecture 1 (solution)

{NOTE}

Proof: the witness is `n = 261150`, with `a 261150 = 1`. `OeisA92243.partialScore_261150`
(`OeisA92243/Bridge.lean`) turns the kernel computation `OeisA92243.certs_ok` into
`partialScore 261150 = 1`, and `partialScore` is `a`'s sum with `primeGap` unfolded.
No `native_decide`.
-/

@[expose] public section

namespace OeisA92243

{defs}

{proof_doc}theorem conjecture1 : ∃ n > 250000, a n > 0 := by
  refine ⟨261150, by norm_num, ?_⟩
  have h : a 261150 = 1 := by
    unfold a
    rw [ite_eq_right (show ¬ (261150 ≤ 1) by norm_num)]
    exact partialScore_261150
  rw [h]
  norm_num

end OeisA92243

end
"""
pathlib.Path("Challenge.lean").write_text(challenge)
pathlib.Path("Solution.lean").write_text(solution)
print("wrote Challenge.lean, Solution.lean")

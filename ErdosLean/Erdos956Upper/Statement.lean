import ErdosLean.Erdos956.Statement

/-!
# Erdős Problem 956 (JSP-000796): the Erdős–Pach upper bound — statement

Source: <https://www.erdosproblems.com/956>, catalogued as JSP-000796 in
<https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000796>.

All definitions (`E`, `setDist`, `translate`, `Admissible`, `unitPairs`, `h`) are reused verbatim
from `ErdosLean/Erdos956/Statement.lean` (written from scratch; formal-conjectures has no file for #956).

Upper bound: P. Erdős and J. Pach, *Variations on the theme of repeated distances*,
Combinatorica 10 (1990) 261–269: `h(n) = O(n^{4/3})`.  Together with the lower bound
`h(n) ≫ n^{4/3}` already proved in `ErdosLean/Erdos956/` this determines the order of magnitude
`h(n) = Θ(n^{4/3})`.

* `Erdos956UpperEventually` — the unconditional upper bound `h n ≤ K n^{4/3}` for all large `n`;
* `ErdosPachUpperBound` (from `ErdosLean/Erdos956/Statement.lean`) — the same bound for *all* `n`;
* `Erdos956Theta` — `h(n) = Θ(n^{4/3})`;
* `Erdos956FullAnswer` — the question as posed, the sharp lower bound, every exponent `c < 1/3`,
  the upper bound and the `Θ` statement, bundled.
-/

open Filter Asymptotics

namespace Erdos956

/-- The Erdős–Pach bound `h(n) ≤ K n^{4/3}` for all sufficiently large `n`. -/
def Erdos956UpperEventually : Prop :=
  ∃ K : ℝ, ∀ᶠ n : ℕ in atTop, (h n : ℝ) ≤ K * (n : ℝ) ^ ((4 : ℝ) / 3)

/-- The order of magnitude: `h(n) = Θ(n^{4/3})`. -/
def Erdos956Theta : Prop :=
  (fun n : ℕ => (h n : ℝ)) =Θ[atTop] fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3)

/-- The complete answer to Erdős #956. -/
def Erdos956FullAnswer : Prop :=
  Erdos956Statement ∧ Erdos956LowerBound ∧ Erdos956AllExponents ∧ ErdosPachUpperBound ∧
    Erdos956UpperEventually ∧ Erdos956Theta

end Erdos956

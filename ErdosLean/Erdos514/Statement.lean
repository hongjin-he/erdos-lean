import Mathlib

/-!
# Erdős Problem 514 (JSP-000412): statement

Source: <https://www.erdosproblems.com/514> (Erdős [Er61, p. 249], [Er82e]), catalogued as
JSP-000412 in
<https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000412>.

The catalogue entry ("Does every transcendental entire function have a path to infinity along
which its modulus grows faster than every polynomial?") is the first of the three questions
listed on erdosproblems.com:

> Let `f(z)` be an entire transcendental function. Does there exist a path `L` so that,
> for every `n`, `|f(z) / zⁿ| → ∞` as `z → ∞` along `L`?

The answer is **yes**. erdosproblems.com records that Boas (unpublished) proved this first
part. The existence of such a path is also implicit in J. L. Lewis, J. Rossi and
A. Weitsman, *On the growth of subharmonic functions along paths*, Ark. Mat. 22 (1984),
109–119, and follows directly from Jang-Mei Wu, *Length of paths for subharmonic functions*,
J. London Math. Soc. (2) 32 (1985), no. 3, 497–505, Theorem B, applied to `log⁺ |f|`
(as pointed out by P. Chojecki and N. Sothanaphan in the erdosproblems.com forum
thread for #514). The second and third questions on erdosproblems.com (length of the path,
growth relative to `M(r)`) are not part of JSP-000412 and are not formalized here.

The Lean proof in this directory does not formalize Wu's theorem; it is a self-contained
argument (Taylor shifts, tracts of superlevel sets, the maximum modulus principle and a
Carleman-type growth estimate), see `Main.lean`.

Formalisation choices.
* "entire transcendental": `f` is complex differentiable on all of `ℂ` and is not a
  polynomial function.
* "path to infinity": a continuous `γ : ℝ → ℂ` with `‖γ t‖ → ∞` as `t → +∞`
  (only the half-line `t → +∞` matters; `γ` on `(-∞, 0]` is irrelevant).
* "for every `n`, `|f(z)/zⁿ| → ∞` as `z → ∞` along `L`": for every `n : ℕ`,
  `‖f (γ t) / γ t ^ n‖ → ∞` as `t → +∞`. (Lean's convention `x / 0 = 0` is harmless here:
  `γ t ≠ 0` for all large `t`.)

As of 2026-09-19, `google-deepmind/formal-conjectures` has no file for Problem 514
(`FormalConjectures/ErdosProblems/514.lean` does not exist), so this statement was written
from the problem text.
-/

open Filter

namespace Erdos514

/-- `f` is a transcendental entire function: entire and not (the function of) a polynomial. -/
def IsTranscendentalEntire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z

/-- Erdős #514, first question (the JSP-000412 question), in its affirmative form:
every transcendental entire function has a path to infinity along which `|f(z)/zⁿ| → ∞`
for every `n`. -/
def Erdos514Statement : Prop :=
  ∀ f : ℂ → ℂ, IsTranscendentalEntire f →
    ∃ γ : ℝ → ℂ, Continuous γ ∧ Tendsto (fun t => ‖γ t‖) atTop atTop ∧
      ∀ n : ℕ, Tendsto (fun t => ‖f (γ t) / γ t ^ n‖) atTop atTop

end Erdos514

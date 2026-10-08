import Mathlib.Analysis.InnerProductSpace.Basic

/- Hypothetical rows used by the power-retry tests, compiled to record their
   real argument visibility, telescope identities and numeric literals. -/
namespace NumeralPowerFixture

axiom real_inner_mul_inner_le {F : Type} [SeminormedAddCommGroup F]
    [InnerProductSpace ℝ F] (x y : F) :
    inner ℝ x y * inner ℝ y x ≤ inner ℝ x x * inner ℝ y y

axiom mul_self_mul_self_le {a b : ℝ} :
    0 ≤ a → a ≤ b → a * (a * a) ≤ b * (b * b)

end NumeralPowerFixture

import Mathlib.Topology.Defs.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Notation


/-
1.1 The Normal Mapping

Let Ω be an open subset of ℝⁿ and u: Ω → ℝ.
-/
notation "ℝ" n => EuclideanSpace ℝ (Fin n)
notation "⟪" x ", " y "⟫" => inner x y

variable {n : ℕ} (hn : n ≥ 1)
variable {Ω : Set (ℝ n)} (hopen : IsOpen Ω)
variable (u : Ω → ℝ) (x₀ : Ω)

/--
Given x₀ ∈ Ω, a supporting hyperplane to the function
u at the point (x₀, u(x₀)) is an affine function
l(x) = u(x₀) + p (x - x₀) such that u(x) ≥ l(x) for all x ∈ Ω
-/
structure SupportingHyperplane where
  /-- Hyperplane normal -/
  p : ℝ n
  /-- Affine function l(x) -/
  l x := u x₀ + ⟪p , x - x₀⟫
  /-- u(x) ≥ l(x) for all x ∈ Ω, hense supporting -/
  hsupport : ∀ x, u x ≥ l x

/--
Definition 1.1.1. The normal mapping of u, or subdifferential
of u, is the set-valued function : ∂u : Ω → 𝒫(ℝⁿ) defined by
∂u(x₀) = {p : u(x) ≥ u(x₀) + p (x - x₀)}
-/
def NormalMapping := {p | ∀ x, u x ≥ u x₀ + ⟪p, (x : ℝ n) - x₀⟫}

/--
Given E ⊆ Ω, we define ∂u(E) = ∪(x ∈ E) ∂u(x)
-/
def NormalMappingSubset (h : E ⊆ Ω) : Set (ℝ n) := ⋃ x, ⋃ hx, NormalMapping u ⟨x, by exact h hx⟩

/-
Lemma 1.1.3. If Ω ⊆ ℝⁿ is open, u ∈ C(Ω) and K ⊆ Ω is compact
then ∂u(K) is compact
-/
lemma lemma_1_1_3
    (h₁ : Continuous u)
    (K : Set (ℝ n)) (h₂ : K ⊆ Ω) (h₃ : IsCompact K) :
    IsCompact (NormalMappingSubset u h₂) := by
  sorry

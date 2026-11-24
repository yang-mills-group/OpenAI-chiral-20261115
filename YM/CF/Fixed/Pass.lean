import YM.CF.Fixed.Fine

/-!
Part of the Gram argument of `82374866` § "Passing to separated Schwinger
data". This step is independent of the measure and is NOT by itself a
transfer. Kept entrywise to apply with a single common subsequence and actual
normalized local/reflected products. The hypotheses of these lemmas cannot
use a separate limit per entry of G.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Fixed
open Function Fock NormedSpace SU Lat Lattice Cube Finset Scroll MeasureTheory Tulip Filter
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Topology ComplexOrder
attribute [local instance] opCStarAlgebra

variable {I : Type*} {A : Type*} {l:Filter A} [l.NeBot] {G D:A→Matrix I I ℂ} {M:Matrix I I ℂ}

lemma hermitian_of_limits (L:∀ i j,Tendsto (fun n=>G n i j) l (𝓝 (M i j)))
    (H:∀ᶠ n in l, (G n).IsHermitian): M.IsHermitian := by
  ext i j
  exact tendsto_nhds_unique (((L j i).star).congr' (H.mono fun n h=>h.apply _ _)) (L i j)

lemma positive_of_limits [Fintype I] (L:∀ i j,Tendsto (fun n=>G n i j) l (𝓝 (M i j)))
    (H:∀ᶠ n in l,(G n).PosSemidef) : M.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hermitian_of_limits L (H.mono fun _ g=>g.isHermitian), fun x=> ?_⟩
  refine ge_of_tendsto (f:=fun n=>dotProduct (star x) ((G n).mulVec x)) ?_ (H.mono fun n h=>(Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2 _)
  unfold Matrix.mulVec dotProduct; exact tendsto_finsetSum _ fun i _=> tendsto_const_nhds.mul (tendsto_finsetSum _ fun j _=> (L i j).mul_const (x j))

/-- With an eventually PSD donor and convergent target, enough to establish
entrywise difference after both normalizations (or even this after-reflection-
plane shift). -/
lemma positive_of_matches [Fintype I]
    (L:∀ i j,Tendsto (fun n=>G n i j) l (𝓝 (M i j)))
    (e:∀ i j,Tendsto (fun n=>G n i j-D n i j) l (𝓝 0))
    (H:∀ᶠ n in l, (D n).PosSemidef) : M.PosSemidef := by
  apply positive_of_limits _ H
  intro i j
  convert (L i j).sub (e i j) using 1 <;> simp

end YM.CF.Fixed

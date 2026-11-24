import YM.CF.Drapes.Scept
import Mathlib.Analysis.Calculus.Deriv.Star
set_option linter.unusedVariables false
/-! Line holomorphy on same cap. Type of ambient independent complex variables. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Drapes
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Branch Finset Function Fock Filter
attribute [local instance] opCStarAlgebra
variable {I Y D G : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
/-! Total curves over open plane sets. Allows all continuous complex differentiable curves in the ambient variables. Includes line germs. -/
def Looks (X:Set D)(f:X→ℂ): Prop := ∀ (V:Set ℂ), IsOpen V → ∀ (γ:ℂ→X), DifferentiableOn ℂ (fun z=> ((γ z).val:D)) V → DifferentiableOn ℂ (f ∘ γ) V

def badge (X:Set D): License ↥X where
  valid:=Looks X
  plus:=fun H G V h γ e=> (H V h γ e).add (G V h γ e)
  con c V h γ e:= differentiableOn_const c
  mul:=fun H G V h γ e=> (H V h γ e).mul (G V h γ e)
  sumK f c hp H K V h γ e:= Complex.differentiableOn_tsum_of_summable_norm hp (fun i=>H i V h γ e) h (fun i z _=>K i (γ z)) -- check
lemma honors (X:Set D)(f:D→ℂ)(h:DifferentiableOn ℂ f X): Looks X (fun x=>f x.val):=fun V hv γ e=> h.comp e (fun i hi=>(γ i).property)
lemma realigns {X:Set D}{f:X→ℂ}(H:Looks X f)(funB:X→X)(g:∀ (V:Set ℂ),IsOpen V→∀ (γ:ℂ→X), DifferentiableOn ℂ (fun z=> ((γ z).val:D)) V → DifferentiableOn ℂ (fun z=> (funB (γ (star z))).val) (star ⁻¹' V)): Looks X fun x=> star (f (funB x)):=by
  intro V h γ e
  have he:= H (star ⁻¹' V) (h.preimage continuous_star) (fun z=>funB (γ (star z))) (g V h γ e)
  intro z hz
  have hb:= he.differentiableAt ((h.preimage continuous_star).mem_nhds (show star z∈ star ⁻¹' V by simpa))
  -- inspect Complex
  have hi := hb.star_conj
  simp only [Function.comp_def] at *
  change DifferentiableAt ℂ (fun x=> star (f (funB (γ (star (star x)))))) (star (star z)) at hi
  simp only [star_star] at hi; exact hi.differentiableWithinAt
end YM.CF.Drapes

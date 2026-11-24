import YM.CF.DPress.Analytic.Compass
import YM.CF.DPress.Analytic.Plumes
import YM.CF.Mew.Pot
import YM.CF.Scion.Vice
/- Holomorphic operations deterministically in parameter. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.DPress.Analytic
open Function NormedSpace Lattice RG Fock
open Lat Skye Scree Pastry Mew Scion Stilo Finset
open scoped ContDiff Topology NNReal BigOperators Classical Matrix MatrixOrder Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {I:Type}[LinearOrder I][Fintype I]{R:ℝ}{p:Set ℂ}
abbrev Holo{F:Type*}[NormedAddCommGroup F][NormedSpace ℂ F](p:Set ℂ)(f:ℂ→F):Prop:=DifferentiableOn ℂ f p
abbrev ValX (I:Type)[LinearOrder I][Fintype I] : Dough I →L[ℂ] FC I := LinearMap.toContinuousLinearMap
 { toFun := Subtype.val, map_add':= fun _ _ => rfl, map_smul':=fun _ _=>rfl }
lemma yields0 {f:ℂ→ Dough I}(p:Set ℂ) (h:Holo p (Subtype.val ∘ f)): Holo p f:=by
 obtain ⟨U,hU⟩:= LinearMap.exists_leftInverse_of_injective (ValX I).toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective); let V:= U.toContinuousLinearMap; have hp := V.differentiable.comp_differentiableOn h; exact hp.congr fun i v=> (DFunLike.congr_fun hU (f i)).symm -- tune
abbrev ΔIO(S:Type)[SemilatticeSup S][Fintype S][OrderBot S][DecidableEq S] (I:Type)[LinearOrder I][Fintype I] : (S→ Dough I) →L[ℂ] (S→ Dough I):= LinearMap.toContinuousLinearMap
 { toFun := reconL.symm, map_add':=fun _ _=>map_add .., map_smul':= fun c x=> by
    apply solve; intro a; rw [RingHom.id_apply]; change c • x a=view a (c • (reconL.symm x)); rw [show view a (c • (reconL.symm x))= c • (view a (reconL.symm x)) from ?_, recon]; unfold view; rw [Finset.smul_sum]; rfl }
lemma dough_exp : Differentiable ℂ (exp : Dough I→ Dough I):= by intro x; exact (exp_analytic (𝕂:=ℂ) x).differentiableAt
end YM.CF.DPress.Analytic

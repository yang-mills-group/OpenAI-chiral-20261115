import YM.CF.Rive.Bond
set_option autoImplicit false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Mew
open Function NormedSpace Filter Metric Finset MeasureTheory Lattice Wilson RG Forge Cube Fock Lat
open Skye Scree Jet Vow Tulip Scroll Spire Peaks Pastry Scion Stilo Palot Urn Hake
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {ι A n M: Type*}[LinearOrder n][Fintype n][LinearOrder M][Fintype M]
variable {Z:Type*}[Fintype ι][DecidableEq ι][Fintype A][DecidableEq A][Fintype Z][DecidableEq Z]

variable {J:n→A}{D:LeanV M→A}{X:ι→leaf A}{P:Finset ι}
lemma lift_holo {T:Type*}[LinearOrder T][Fintype T] {f:ℂ→ Dough T}{U':Set ℂ} (h:DifferentiableOn ℂ (fun i=>(f i).val) U'):DifferentiableOn ℂ f U':=by
 let g:=sheen (T:=T); have he: Injective g:= Subtype.coe_injective; obtain ⟨W,p⟩:= LinearMap.exists_leftInverse_of_injective (f:=g.toLinearMap) (LinearMap.ker_eq_bot.mpr he)
 let F:= W.toContinuousLinearMap; have hx:f= F∘ fun i=>(f i).val:=funext (fun i=>(DFunLike.congr_fun p (f i)).symm); conv=> arg 2; rw [hx];
 exact F.differentiable.comp_differentiableOn h
variable {J:n→A}{D:LeanV M→A}{X:ι→leaf A}{P:Finset ι}
section
variable (H: ℂ→ ModeW J D X P)(U:Set ℂ)
lemma tempo_holo {q:Crowd A} (h:DifferentiableOn ℂ (fun i=> (H i).voice) U)(f:∀ (z:ℂ), (H z).knots q=(H 0).knots q)(g:∀ (z:ℂ),(H z).rhythm q=(H 0).rhythm q)(p:DifferentiableOn ℂ (fun z=>(H z).diet q) U): DifferentiableOn ℂ (fun i=> tempo (H i) q) U:= by
 unfold Scion.tempo; split; swap; · exact differentiableOn_const _
 simp_rw [f,g]; let L:=LinearMap.toContinuousLinearMap ((issue ((H 0).knots q)).flip ((H 0).rhythm q)); exact (L.differentiable.comp_differentiableOn h).mul p
variable {θ E: Type*}[NormedRing E][NormedAlgebra ℂ E][NormedAlgebra ℝ E][FiniteDimensional ℂ E][FiniteDimensional ℝ E][SemilatticeSup θ][OrderBot θ][Fintype θ][DecidableEq θ]
lemma recon_smul (f:θ→E)(c:ℂ): reconL.symm (c • f)= c • reconL.symm f:=by
 funext i; refine proves fun j p=> ?_; rw [recon]; simp_rw [view, Pi.smul_apply, ←Finset.smul_sum];  exact congrArg (c •·) (recon f j).symm
abbrev recover : (θ→E)→L[ℂ](θ→E):= LinearMap.toContinuousLinearMap {toFun:= fun v=>reconL.symm v,map_add':=fun a b =>map_add ..,map_smul':=fun c f=> recon_smul f c}
lemma vigor_holo (h:∀ q:Crowd A, DifferentiableOn ℂ (fun i=> tempo (H i) q) U) (q:Crowd A): DifferentiableOn ℂ (fun i=> vigor (H i) q) U:= by
 apply lift_holo; simp_rw [vig_all]; exact ((ContinuousLinearMap.proj (R:=ℂ) q).differentiable.comp recover.differentiable).comp_differentiableOn (differentiableOn_pi.mpr h)
end
end YM.CF.Mew

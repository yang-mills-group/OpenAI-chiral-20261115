import YM.CF.DPress.Chess.Floor.Pane
import YM.CF.DPress.Chess.Floor.Shed
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt Sermon
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough ComplexOrder Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{ℓ d r:ℕ}{β u k:ℝ}{P:Loom n}
namespace Porch
open BPress
open Dial
variable (S:Support (More n)){F: Orbit n→ Phys n}
-- approximation for positivity after top release
lemma continuousExt (p:Envelope F)(u:∀ H: Fixed.Test n, Continuous H→Boss n S H→ 0 ≤ Fixed.functional F (peer W H * H)) {A:Fixed.Test n} (h:Boss n S A):0 ≤ Fixed.functional F (peer W A * A):=by
 obtain ⟨G,Cℓ,H,v,h⟩:= choices S A h; let g(i:ℕ) := peer W (G i)*G i; let K(Z:Fixed.Test n)(x:Orbit n) := WeightL (F x) (Z x.1); let P:=peer W A *A; let U:=city n; let V:=prior SU.group (More n);
 have hc:Tendsto (fun i=>∫ x,K (g i) x∂U) atTop (𝓝 (∫ x,K P x∂ U)):=by
   obtain ⟨Y,q⟩:=p.cost
   have he(i:ℕ): Envelope (g i):= Law.prodP (peer_env W ((Boss.window _ (⟨Cℓ,H _⟩)))) (Boss.window _ ⟨Cℓ,H _⟩)
   let R':= ‖mateK n‖*(Cℓ*Cℓ*Y); refine tendsto_integral_of_dominated_convergence (fun _=>R') (fun i=>(rent_C (Env.along (he i) measurable_fst) p).meas.aestronglyMeasurable) (integrable_const R') (fun i=> Eventually.of_forall (fun x=>?_)) ?_
   · let Z:= g i x.1; have hx: ‖Z‖≤ Cℓ*Cℓ:= (norm_mul_le (peer W (G i) x.1) (G i x.1)).trans (mul_le_mul ((penny W (H i)).cost _) ((H i).cost _) (norm_nonneg _) (H i).nonneg); change ‖inner ℂ (mateK n) (acts Z _)‖ ≤ R'; exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (((acts Z).le_opNorm _).trans (mul_le_mul ((Matrix.l2_opNorm_toEuclideanCLM _).trans_le hx) (q _) (norm_nonneg _) (mul_self_nonneg _))) (norm_nonneg _)) -- suff continuity uniform estimate.
   have hg: MeasurePreserving (Prod.fst:Orbit n→Pane n) U V:= measurePreserving_fst; filter_upwards [hg.quasiMeasurePreserving.ae h, ((W.trail n).comp hg).quasiMeasurePreserving.ae h] with x t v; exact ((WeightL _).continuous.tendsto (P x.1)).comp (((W.θ_c n).tendsto _|>.comp v).mul t)
 exact ge_of_tendsto' hc (fun i=> u (G i) (v i) ⟨Cℓ,H i⟩)
end Porch
end YM.CF.DPress.Chess

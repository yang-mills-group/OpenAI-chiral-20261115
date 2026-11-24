import YM.SU5.FiniteGaugeData.Drachma.Lima
import YM.CF.Reine.Aeon
import YM.SectorNext.VACUUM_NORMALIZATION.Laplace
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 16000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Drachma
open Function Finset Filter Matrix Lattice Wilson RG Precision Exterior Tree Laurent Bloch
open Pressure Pressure.Tube Stores AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching PatchReads
open CF.Newt CF.Neige CF.Char Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad Work.F03
open SectorNext.Vacuum.FlatTree Next.SectorChange.Rows Push.SectorMeasure
open scoped Topology ContDiff BigOperators Matrix Classical InnerProductSpace Kronecker Matrix.Norms.Frobenius
variable {c f:Side}{G:Gauge} {S:StepData c f} {T:Tube G S}{p:Clip} {a A σ C Λ x:ℝ} {P Q:Bed}
local notation "λ₀" => S.kernel.penalty
variable (F : Forest S.ratio)

-- temperature receipts, leading measure in probability Haar 
namespace Tame
open SectorNext.Vacuum CF.Appel CF.Reine
open Metric MeasureTheory
open scoped ENNReal
variable {R:ChartRatio G}
local notation "uΔ" => Fintype.card G.ColorIndex
lemma crank(G:Gauge): Fintype.card G.ColorIndex=Module.finrank ℝ G.Color:=by simp [Gauge.Color]
def coinV(R:ChartRatio G)(β:ℝ):= Real.log (Next.SectorChange.spare R β)
lemma pocketN{β:ℝ}(h:0<β): Next.SectorChange.spare R β=(Real.sqrt (2*Real.pi) / Real.sqrt β)^uΔ*R.scale:=by
 unfold Next.SectorChange.spare; have he:= coupling_pos h; rw [Real.sqrt_mul (by positivity),Real.sqrt_sq he.le, div_eq_mul_inv]; rfl -- tune
lemma pocketU{β:ℝ}(h:LocalRatio R)(he:0<β): coinV R β=Real.log R.scale +(uΔ:ℝ)*(Real.log (2*Real.pi)/2 - Real.log β/2):=by
 rw [coinV,pocketN he,Real.log_mul (by positivity) h.scale.ne', Real.log_pow,Real.log_div (by positivity) (by positivity),Real.log_sqrt he.le,Real.log_sqrt (by positivity)]; ring
lemma specs{η:ℝ}(h:LocalRatio R)(hp:0<η): Real.log (narrow R η)=Real.log R.scale+(uΔ:ℝ)/2 *(Real.log (2*Real.pi)-Real.log η):=by
 unfold narrow; rw [Real.log_mul h.scale.ne' (by positivity), Real.log_rpow (by positivity), show Real.pi/(η/2)=2*Real.pi/η by ring,Real.log_div (by positivity) hp.ne']; rw [crank] -- tune
lemma noiseTag{K:KernelChoices}(R:ChartRatio G)(h:LocalRatio R):
 ∀ ε>0, ∀ᶠ β:ℝ in atTop,∀ c f (S:StepData c f), S.kernel=K → |Real.log (S.penaltyZ β G) - (coinV R β-(uΔ:ℝ)/2* Real.log K.penalty)|≤ε:=by
 intro ε hp; let k:=K.penalty; have hk:0<k:=K.penalty_pos
 let T (β:ℝ):= Real.sqrt β; let U(β:ℝ):= T β^uΔ * linkZ G (k*(T β)^2); let q:=narrow R k
 have he:Tendsto U atTop (𝓝 q):=by unfold U; rw [crank G]; exact (first_asymptotic R h k hk).comp Real.tendsto_sqrt_atTop
 have hh:= he.log (narrow_pos R h k hk|>.ne'); filter_upwards [Metric.tendsto_nhds.mp hh ε hp,eventually_gt_atTop (0:ℝ)] with β hβ hp c f S hz
 let W:=S.penaltyZ β G; have hW:0<W:= S.penaltyZ_pos β; have hQ:0 < T β:=Real.sqrt_pos.mpr hp; have hs:T β ^2=β:=Real.sq_sqrt hp.le
 have hb:linkZ G (k*(T β)^2)=W:=by rw [hs]; unfold W linkZ StepData.penaltyZ; congr 1; ext v; unfold SectorNext.Vacuum.mouth StepData.penaltyWeight; rw [hz]; unfold k; ring_nf -- tune
 change dist (Real.log (U β)) (Real.log q) < ε at hβ; unfold U q at hβ; rw [hb,Real.log_mul (pow_pos hQ _).ne' hW.ne',Real.log_pow,show Real.log (T β)=_ from Real.log_sqrt hp.le, specs h hk, Real.dist_eq] at hβ; rw [pocketU h hp]; ring_nf at hβ ⊢; unfold W k at hβ; convert! hβ.le using 2; ring
lemma point_1(G:Gauge): Tendsto (CF.Appel.point G) atTop (𝓝 1):=by
 have hc: Monotone (fun r:ℝ=> closedBall (0:G.Color) r):=fun i j h=> closedBall_subset_closedBall h; have he:= tendsto_measure_iUnion_atTop (μ:=rice G) hc; rw [show (⋃ r:ℝ,closedBall (0:G.Color) r)= Set.univ from Set.eq_univ_of_forall fun x=> Set.mem_iUnion.mpr ⟨dist x 0,mem_closedBall.mpr le_rfl⟩, measure_univ] at he; exact ENNReal.toReal_one ▸ ((ENNReal.tendsto_toReal (by simp : (1:ℝ≥0∞)≠⊤)).comp he) -- tune
lemma fray_F (G:Gauge)(σ:ℝ)(hp:0<σ)(p:Clip)(C:ℝ): Tendsto (Toffee.fray p σ C) atTop (𝓝 0):=by
 have he:Tendsto (fun x=> Toffee.tar σ (till x)) atTop (𝓝 0):=by simpa only [Toffee.tar,pow_zero,one_mul] using radius_tail G 1 σ hp 0
 unfold Toffee.fray; simpa only [mul_zero] using (he.const_mul |C|).const_mul (Real.sqrt (Fintype.card PlaqAxes:ℝ)/Real.sqrt p.direct)
lemma report(G:Gauge): Tendsto (fun x=> Real.log (point G x)) atTop (𝓝 0):=by simpa only [Real.log_one] using (point_1 G).log (by norm_num)
end Tame
end YM.SU5.FiniteGaugeData.Drachma

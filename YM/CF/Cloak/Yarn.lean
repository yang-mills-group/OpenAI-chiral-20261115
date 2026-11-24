import YM.CF.Reine.Proof
import YM.CF.Rill.Oboe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cloak
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
open Forge Reine Rill
section bound
variable {E X:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x₀:E}{U:E→ Config G f}{u v C D:ℝ}{T:E→X}[NormedAddCommGroup X][NormedSpace ℝ X]
-- Shake measure unscaled stencil through n
abbrev Trow(U:E→ Config G f)(x₀:E)(v:ℝ)(n:ℕ):Prop:=∀ i:Bond f,Tender (fun t=>U t i) x₀ v n -- tune
lemma minus_h(h:Shake T x₀ D n)(P:X): Shake (fun t=>T t-P) x₀ D n:=by
 refine ⟨h.price,h.smooth.sub contDiffAt_const,fun i v g=>?_⟩
 rw [show (fun t=>T t-P)=T-(fun _=>P) from rfl, iteratedFDeriv_sub_apply (h.smooth.of_le (show (i:WithTop ℕ∞) ≤ ↑n from Nat.cast_le.mpr g)) contDiffAt_const, iteratedFDeriv_const_of_ne (Nat.ne_of_gt v),Pi.zero_apply,sub_zero]; exact h.bill i v g -- tune args
-- price square relative.G norm
-- χ scalar clamped.Jet.P. follows smooth.Turn Bore
attribute [local instance] Gauge.frobInner
local notation "m"=> SU.group.colorScale
lemma faint_w (s:ℝ)(p:0<s)(F:E→ SU.group.El)(h:Tender F x₀ (C*s) n)(hp:SU.group.chord (F x₀) ≤ s)(t:m ≤ C): Allows n (fun x=> SU.group.mat (F x)-1) x₀ (C*s):=by
 have hm:= SU.group.colorScale_pos; rw [Gauge.chord] at hp
 let H(x):= SU.group.mat (F x)-1; have hh:Shake H x₀ (C*s) n:=minus_h h 1; exact (max_self (C*s)) ▸ hh.paid (((div_le_iff₀ hm).mp hp).trans ((mul_le_mul_of_nonneg_left t p.le).trans_eq (mul_comm ..)))
lemma white (s:ℝ)(p:0<s)(F:E→SU.group.El)(h:Tender F x₀ (C*s) n)(hp:SU.group.chord (F x₀) ≤ s)(t:m ≤ C): Allows n (fun y=> (SU.group.chord (F y)/s)^2) x₀ (let x:=m⁻¹*C; 2^n*x*x):=by
 let H(x):= SU.group.mat (F x)-1; let g:=m⁻¹*s⁻¹; let V:=fun i=> g • H i; have hm:= SU.group.colorScale_pos
 have hh: Allows n V x₀ (m⁻¹*C):= ((faint_w s p F h hp t).smul g).mono (by rw [abs_of_pos (by positivity :0<g)]; unfold g; field_simp; rfl); have hx:= hh.bilinear (innerSL ℝ) hh (show ‖(innerSL ℝ : SU.group.Mat →L[ℝ] SU.group.Mat →L[ℝ] ℝ)‖ ≤1 from ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one fun i j=> by rw [one_mul]; exact abs_real_inner_le_norm i j); rw [mul_one] at hx; apply hx.germ; filter_upwards with x; change inner ℝ (V x) (V x)=_; simp only [real_inner_self_eq_norm_sq]; unfold V H; rw [norm_smul, Real.norm_of_nonneg (by positivity :0 ≤ g)]; unfold g; rw [Gauge.chord]; unfold Gauge.colorScale; ring
end bound
end YM.CF.Cloak

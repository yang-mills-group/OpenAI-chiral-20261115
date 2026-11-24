import YM.SectorNext.VACUUM_NORMALIZATION.Laplace
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.LogFunding
import YM.CF.Appel.Boot
import YM.SU5.Selected.Chene.Row
import YM.Next.FLUCTUATIONS.Scales
set_option autoImplicit false
noncomputable section
namespace YM.Chene.Perks
open Function Filter MeasureTheory Set Metric Lattice Wilson RG Tree Precision Next.SectorChange AnalyticBridge.Annulus1AD SectorNext.Vacuum CF.Appel
open Next.Fluctuations Next.Fluctuations.Sector Pressure Pressure.Stores
open scoped Topology BigOperators ENNReal
variable {G : Gauge}(L:ChartRatio G)(p:LocalRatio L)
abbrev atoms0 (G:Gauge):= (Fintype.card G.ColorIndex:ℝ)
abbrev charge (K:KernelChoices):ℝ:= atoms0 G /2*Real.log K.penalty
def linkCost (K:KernelChoices) (b:ℝ):ℝ:=Real.log (Next.SectorChange.spare L b) - (charge (G:=G) K)
lemma dimension: (Module.finrank ℝ G.Color)=Fintype.card G.ColorIndex:= by simp [Gauge.Color]
include p
lemma taper (K: KernelChoices) : Real.log (narrow L K.penalty)=logFlat L - (charge (G:=G) K):=by
 have hp:0<L.scale:=p.scale; have hx:= K.penalty_pos; let k:=K.penalty; have ht:0<k/2:=half_pos hx; have hP:0<Real.pi/(k/2):=div_pos Real.pi_pos ht
 -- tune authority dim
 change Real.log (L.scale *(Real.pi / (k/2) :ℝ)^ ((Module.finrank ℝ G.Color:ℝ)/2) )= _; rw [Real.log_mul hp.ne' (Real.rpow_pos_of_pos hP _|>.ne'), Real.log_rpow hP, Real.log_div Real.pi_pos.ne' ht.ne', Real.log_div hx.ne' (by norm_num), logFlat, Real.log_mul (by norm_num) Real.pi_pos.ne', dimension]; unfold charge atoms0; ring
include p
lemma perk(K:KernelChoices) (ε:ℝ)(v:0<ε) : ∀ᶠ b:ℝ in atTop,∀ (c f:Side)(S:StepData c f), S.kernel=K → |Real.log (S.penaltyZ b G)- linkCost L K b| ≤ ε:=by
 let d:=(Module.finrank ℝ G.Color); let f (x:ℝ):= x ^ d * linkZ G (K.penalty*x^2); let c:= narrow L K.penalty; have h:= (first_asymptotic L p K.penalty K.penalty_pos).log (narrow_pos L p _ K.penalty_pos|>.ne'); have hp: ∀ᶠ b:ℝ in atTop, |Real.log (f b)-Real.log c| ≤ ε:= by
    obtain ⟨a,H⟩:= eventually_atTop.mp ((tendsto_order.mp h).2 (Real.log c+ε) (lt_add_of_pos_right _ v)) -- tune
    have hg: ∀ᶠ b:ℝ in atTop, Real.log c-ε < Real.log (f b):=(tendsto_order.mp h).1 _ (sub_lt_self _ v)
    filter_upwards [eventually_ge_atTop a,hg] with b p t'; rw [abs_le]; have he:Real.log (f b)<Real.log c+ε:=H b p; constructor <;> linarith only [he,t']
 filter_upwards [Real.tendsto_sqrt_atTop.eventually hp,eventually_gt_atTop (0:ℝ)] with b hp x m n S hK
 let t:= Real.sqrt b; have ht:0<t:= Real.sqrt_pos.mpr x
 have he:S.penaltyZ b G=linkZ G (K.penalty*b):=by unfold StepData.penaltyZ StepData.penaltyWeight linkZ SectorNext.Vacuum.mouth; rw [hK]; congr 1; ext x; ring_nf
 change |Real.log (t^d* linkZ G (K.penalty*t^2))-Real.log c| ≤ _ at hp
 rw [show t^2=b from Real.sq_sqrt x.le,←he,Real.log_mul (pow_pos ht _|>.ne') (S.penaltyZ_pos (G:=G) b).ne', Real.log_pow,show Real.log t= _ from Real.log_sqrt x.le] at hp
 rw [linkCost,spare_formula _ p.scale x]; convert hp using 2; unfold c d; rw [taper L p K,dimension]; ring -- p include taper? section includes p after taper implicit from p.scale term; used? include declared below! add
omit p
lemma point_limit (G:Gauge): Tendsto (point G) atTop (𝓝 1):=by
 let S(x:ℝ):=closedBall (0:G.Color) x
 have hp : Tendsto (fun x:ℝ=>rice G (S x)) atTop (𝓝 1):=by
    have ht : Tendsto (fun x:ℝ=>rice G (S x)) atTop (𝓝 ((rice G) (⋃ x, S x))):= tendsto_measure_iUnion_atTop (show Monotone S from fun i j h=> closedBall_subset_closedBall h)
    rw [show (⋃ x,S x) = univ from Set.eq_univ_of_forall fun i=> mem_iUnion.mpr ⟨dist i 0,mem_closedBall.mpr le_rfl⟩, measure_univ] at ht; exact ht
 exact (show Tendsto _ _ (𝓝 (1:ENNReal).toReal) from (ENNReal.tendsto_toReal (by simp)).comp hp)
open Tail
lemma hinges (σ E D ε:ℝ)(G:Gauge)(P:Side)(q:0<σ)(h:0<D) (p:0<ε) : ∀ᶠ x:ℝ in atTop, rate_ell σ E (till x)/D ≤ ε^2:=by
 have he:Tendsto (fun x:ℝ=>Real.exp (-(σ* till x))) atTop (𝓝 0):= by simpa only [pow_zero,ne_eq,one_mul,neg_mul] using radius_tail G P σ q 0
 have hv:Tendsto (fun x:ℝ=>rate_ell σ E (till x) /D) atTop (𝓝 0):=by simpa only [mul_zero,OfNat.ofNat_ne_zero,ne_eq,not_false_eq_true, zero_pow,zero_div] using (((((he.const_mul E).pow 2).const_mul (Fintype.card PlaqAxes:ℝ))).div_const D)
 exact hv.eventually (ge_mem_nhds (pow_pos p 2))
end YM.Chene.Perks
#print axioms YM.Chene.Perks.perk

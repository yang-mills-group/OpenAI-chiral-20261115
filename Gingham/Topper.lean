import Gingham.Campus
import Velour.Wadding.Tapes
/-!
# Actual elected grids to the registered Eu readings (all ordered words)
Uses full pledges *inside* strict all-axis margin, on the original
Aprons with their true printing widths (and at P.advocate even at
unchanged axis). Uses WPermit per instrument, **not** stronger non-projected
strong* assumption. Consequently no continuity through missing-coordinate
clearances asserted by this acquisition.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe

namespace Spine.Gingham

open SatinRegistration YM.Velour

lemma flew {H:Hilbert}{f:ℕ→H.Op}{Y:H.Op}
    (h:Flying f Y) : Gleams H f Y := by
  obtain ⟨C,hc,t⟩:= SatinRegistration.ceiling (fun x=>(h.Cauchy x).1)
  exact ⟨⟨C,Eventually.of_forall t⟩,fun x=>(h x).1, fun x=>(h x).2⟩

/-! Grid Riemann purchase after projection to G. Use compact-position
continuity and bounded strong* (projected) at any fixed internal pad. -/
variable (P:Spine) (x:P.Spectrum0 3)(a:Axis)
local notation "ξ"=> P.advocate 3 x a
local notation "G"=> P.ManyF a ξ
local notation "S"=> P.seasons a ξ
local notation "Ω"=> P.heaven a ξ
local notation "T"=> (S).E
local notation "V"=> P.cartage a ξ

variable (d l r:ℝ)(F:SampleDose)(Qold:(P.ManyF a (P.advocate 3 x a)).Op)(t:ℕ)

def silkgrid : (G).Op :=
   ∑ k ∈ P.usedGrid t F, P.activation t F k • P.cloaked a ξ d l r Qold (P.meshPose t k)

lemma silkgrid_charge : ‖silkgrid P x a d l r F Qold t‖ ≤ P.package F t * ‖Qold‖ := by
  unfold silkgrid package
  rw [Finset.sum_mul]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i e=> ?_)
  rw [norm_smul]; exact mul_le_mul_of_nonneg_left (P.cloaked_le ..) (norm_nonneg _)

lemma silkgrid_constant (v:G) :
    Tendsto (fun t=>silkgrid P x a d l r F Qold t v) atTop (𝓝 (P.flounce a ξ d l r Qold F v)):=by
  let f(p:Vantage) := P.cloaked a ξ d l r Qold p v
  rw [P.flounce_act]
  refine (MacroGrid.rSum_limit P.macroStep P.macroStep_zero (fun p=>(F.val p:ℂ) • f p)
    ((Complex.continuous_ofReal.comp F.smooth.continuous).smul (P.cloaked_cont ..))
    P.macroStep_pos (dyed_compact f)).congr fun t=>?_
  let g (i:Cover):=(F.val (P.meshPose t i):ℂ) • f (P.meshPose t i)
  have h (i:Cover) (w:i∉P.usedGrid t F):g i=0:=by
    have e:F.val (P.meshPose t i)=0 := by
      by_contra q; exact w ((P.usedPose _ _ _).mpr (subset_closure q))
    unfold g; rw [e,Complex.ofReal_zero,zero_smul]
  refine (room_price (P.macroStep t) (P.macroStep_pos t) g _ h).2.trans ?_
  rw [Finset.smul_sum,silkgrid,_root_.sum_apply]
  refine Finset.sum_congr rfl fun i _=>?_
  rw [smul_apply,show Fintype.card Axis=4 by rfl]
  unfold g
  rw [← Complex.coe_smul ((P.macroStep t)^4), smul_smul]
  push_cast [activation]; rfl

private def wrap (v:G)(y:Vantage):G := T (r-y a-d).toNNReal (V (-y) v)
private lemma wrap_cont (v:G): Continuous (wrap P x a d r v):=vet_heat _ (by fun_prop)
   (P.caravan _ _ _ _ continuous_neg continuous_const)

private lemma silkgrid_drift (Y:(G).Op)(v:G) {e:ℝ}
    (b:∀y∈tsupport F.val,dist (Qold (wrap P x a d r v y)) (Y (wrap P x a d r v y))≤e) :
    dist (silkgrid P x a d l r F Qold t v) (silkgrid P x a d l r F Y t v) ≤ P.package F t * e:= by
  rw [dist_eq_norm]
  unfold silkgrid package
  rw [_root_.sum_apply,_root_.sum_apply,← Finset.sum_sub_distrib,Finset.sum_mul]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i hi=>?_)
  rw [smul_apply, smul_apply,←smul_sub,norm_smul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  simp only [cloaked,pad_val,mul_apply_eq_comp,←map_sub]
  refine le_trans ((V _).le_opNorm ..)
    ((mul_le_of_le_one_left (norm_nonneg _) (P.cart_pay _ _ _)).trans ?_)
  exact ((T _).le_opNorm ..).trans ((mul_le_of_le_one_left (norm_nonneg _) ((S).shrinks ..)).trans
     (le_trans (le_of_eq (dist_eq_norm (Qold _) _).symm) (b _ ((P.usedPose ..).mp hi))))

lemma silkgrid_drifts (Y:ℕ→(G).Op)(z:Flying Y Qold){m:ℕ→ℕ}(s:Tendsto m atTop atTop)
    (v:G):
    Tendsto (fun i=>silkgrid P x a d l r F (Y i) (m i) v) atTop (𝓝 (P.flounce a ξ d l r Qold F v)):=by
  refine ((silkgrid_constant P x a d l r F Qold v).comp s).congr_dist ?_
  apply Metric.tendsto_nhds.mpr
  let c:=F.l1+1
  have hp:0<c:=add_pos_of_nonneg_of_pos (integral_nonneg fun _=>norm_nonneg _) zero_lt_one
  intro ε e
  have h:∀ᶠ i in atTop,P.package F (m i)<c:=
    ((P.package_arrives F).comp s).eventually (gt_mem_nhds (lt_add_one _))
  filter_upwards [Gleams.uniform (flew z)
     (F.budget.image (wrap_cont P x a d r v)) (div_pos e hp),h] with i b p
  rw [Real.dist_0_eq_abs,abs_of_nonneg dist_nonneg,dist_comm]
  exact (silkgrid_drift P x a d l r F _ (m i) _ v (fun y t=>b _ ⟨y,t,rfl⟩)).trans_lt
    ((mul_lt_mul_of_pos_right p (div_pos e hp)).trans_eq (mul_div_cancel₀ ε hp.ne'))
lemma silkgrid_follows (Y:ℕ→(G).Op)(z:Flying Y Qold){m:ℕ→ℕ}(s:Tendsto m atTop atTop)
    {v:ℕ→G}{w:G}(q:Tendsto v atTop (𝓝 w)):
    Tendsto (fun i=>silkgrid P x a d l r F (Y i) (m i) (v i)) atTop (𝓝 (P.flounce a ξ d l r Qold F w)):=by
  obtain ⟨B,b⟩:=(flew z).bought
  obtain ⟨k,hk⟩ := b.exists
  have p:0≤B := (norm_nonneg _).trans hk
  have h:∀ᶠ i in atTop,P.package F (m i)<F.l1+1:=
    ((P.package_arrives F).comp s).eventually (gt_mem_nhds (lt_add_one _))
  have hp:0≤F.l1+1:=add_nonneg (integral_nonneg fun _=>norm_nonneg _) zero_le_one
  refine firmly _ (mul_nonneg hp p) ?_ (silkgrid_drifts P x a d l r F Qold Y z s w) q
  exact (b.and h).mono fun i u=> (silkgrid_charge ..).trans (mul_le_mul u.2.le u.1 (norm_nonneg _) hp)

end Spine.Gingham
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

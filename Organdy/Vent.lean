import Organdy.Expanse
import YM.SU5.Interaction.Kerosene.FuelDesk
import YM.CF.BPress.Scale
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Lor Py Py.Rate BScale Pressure
open BPress (NPL)
variable (R:Patch)(F H U:ℝ→ℝ)
local notation "Q" => SectorNext.Remainder.Scales.g SU.group R.L

lemma Qcost (p:NPL H) : 
    Quench R (fun x=> H x*(Q x)^2) :=
  Chill_v.trend (E:=H) p.vanish (by
    filter_upwards with x
    by_cases h:Q x=0; simp [h]; rw [mul_div_cancel_right₀ _ (pow_ne_zero _ h)])

lemma sightPrice (m:ℕ): BoreP fun x=> polySight (radiusB x) m:=by
 unfold polySight taxIns
 push_cast
 exact (BoreP.still _).grip
    ((BoreP.still _).grip (((BoreP.still _).grip BoreP.radius_c).self _))
def wintercoat (M L:ℕ)(F:ℝ→ℝ)(x:ℝ) :=
  polySight (radiusB x) M * (lashCrag 2 L * |F x|)
lemma shortCoat (M L:ℕ)(p:Chill_v F): Chill_v (wintercoat M L F):=
  (((p.trend (F:=fun i=>|F i|) (Eventually.of_forall fun i=> (abs_abs _).le)).cheap
    (lashCrag 2 L)).leanB (sightPrice M))
lemma longCoat (M L:ℕ)(v:Quench R F):Quench R (wintercoat M L F):=
   (v.normF.manyF _).bondF (sightPrice M)

lemma properSight (M B:ℕ) : 0 ≤ polySight B M := by
  unfold polySight taxIns Sour.fernL; positivity
lemma properWinter (M B:ℕ) (x:ℝ) :
    0≤ wintercoat M B F x:=
  mul_nonneg (properSight ..) (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
open SectorNext.Remainder
open Jade
/-- Old Force expense U, birth H, full F. -/
lemma buySleigh (p:Chill_v F)
    (plus:∀ᶠ x:ℝ in atTop,0≤F x)(u:Quench R U)(e:Quench R H):
    ∃ Γ, Quench R Γ ∧ ∀ᶠ x:ℝ in atTop,∀ p':BudgetPoint,
      p'.B=radiusB x→ U x < Γ x ∧ Stops p' (F x) (H x) (Γ x) :=by
  -- attain positivity even when zero purchases
  let z:=allotΨ R.L
  have hz:Chill_v z:=Chill_v.coin («Q»:=R) ((size_ψ _).low (by omega))
  let B(x):=(radiusB x:ℝ)
  let J(x):=(|U x|+B x* |H x| + z x*(Q x)^2)
  let Γ(x):=4*J x
  have hc:Quench R Γ:=(((u.normF.addL (e.normF.bondF BoreP.radius_c)).addL
    (Qcost _ _ ⟨hz⟩)).manyF _)
  let f(x):=spanV (radiusB x)
  have hy:Chill_v (fun x=>B x*(f x*Γ x)):=(hc.illum_Q.leanB span_bore).leanB BoreP.radius_c
  have h0:= (p.leanB span_bore).leanB BoreP.radius_c
  have δ:0 < (1:ℝ)/4:= by norm_num

  refine ⟨Γ,hc,?_⟩
  filter_upwards [(Scales.year SU.group R.L).eventually_gt_atTop 0,plus,
    hy.spine_a.eventually (ge_mem_nhds zero_lt_one), h0.spine_a.eventually (ge_mem_nhds δ),
    (h0.leanB BoreP.radius_c).spine_a.eventually (ge_mem_nhds δ),
    ((deg_chill _ (hc.illum_Q.cheap 100)).cheap 2).spine_a.eventually (ge_mem_nhds zero_lt_one),
    ((deg_chill _ hc.illum_Q).cheap 2).spine_a.eventually (ge_mem_nhds zero_lt_one),
    (hc.illum_Q.cheap 2).spine_a.eventually (ge_mem_nhds zero_lt_one)] with
    x t pf co lo d1 t1 t2 drop pp v
  change B x*(f x*Γ x) ≤ 1 at co
  change B x*(f x*F x)≤1/4 at lo
  change B x*(B x*(f x*F x))≤1/4 at d1

  have hQ:0<Q x:= Scales.gauge _ _ t
  have hs:0<z x:= pow_pos hQ _
  have hx:0<B x:=by unfold B; rw [←v]; exact Nat.cast_pos.mpr pp.B_pos
  have hg:|U x|+B x* |H x| < Γ x/4:=by
    unfold Γ J; linarith [mul_pos hs (sq_pos_of_pos hQ)]
  have hp:0≤ B x*|H x|:=by positivity
  refine ⟨by linarith [abs_nonneg (U x),le_abs_self (U x)],pf,by linarith [abs_nonneg (U x)],?_,?_,drop,?_,?_,?_,?_⟩
  all_goals simp only [rider,biscuit,v,inv_inv]
  · rw [le_div_iff₀ (by norm_num:(0:ℝ)<2),mul_comm]
    exact t1
  · rw [le_div_iff₀ (by norm_num:(0:ℝ)<2),mul_comm]
    exact t2
  · exact ((le_inv_mul_iff₀ hx).mpr co).trans_eq (mul_one _)
  · rw [div_eq_mul_one_div]; exact (le_inv_mul_iff₀ hx).mpr lo
  · rw [div_eq_mul_one_div]
    refine (le_inv_mul_iff₀ hx).mpr ?_
    change B x * (f x*B x* F x) ≤ 1/4
    nlinarith only [d1]
  rw [div_eq_mul_one_div,mul_assoc]
  refine (le_inv_mul_iff₀ hx).mpr ?_
  linarith [abs_nonneg (U x),mul_le_mul_of_nonneg_left (le_abs_self (H x)) hx.le]

end YM.CF.Organdy

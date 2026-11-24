import Bay.Glacier
import YM.SU5.Interaction.Kerosene.FuelDesk
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf
open Mew PowerSeries
open scoped YM.CF.Mew
variable {n:Side} {P:BudgetPoint}
open Roots Vow Vow.TreasuryFog Push.AbsoluteSums Trees

open Py Py.Rate Lor Py.Rate.BScale Push.Uniform
open Pressure SectorNext.Remainder Nor
open BPress (NPL PL)


abbrev radD (x:ℝ):ℝ:=radiusB x
abbrev weeB (x:ℝ):ℕ:= radiusB x
variable {u f:ℝ→ℝ}
lemma chill_iff :Chill_v f ↔ NPL f := ⟨fun p=>⟨p⟩,fun p=>p.vanish⟩

namespace Till
variable (L:Patch)
abbrev qL (L:Patch)(x:ℝ):ℝ:=Scales.g SU.group L.L x ^ 2
lemma cool_q (L:Patch):Chill_v (qL L):= Chill_v.coin (Q:=L)
  ((size_ψ L.L).low (by omega))
lemma warm_gt (L:Patch):∀ᶠ x in atTop, 0<qL L x:=
 ((Scales.year SU.group L.L).eventually_gt_atTop 0).mono (fun _ p=>pow_pos (Scales.gauge _ _ p) _)
lemma alloy (p:NPL f): Quench L (fun i=>f i * qL L i):=by
 apply Chill_v.trend (chill_iff.mpr p)
 filter_upwards [warm_gt L] with x h
 rw [mul_div_cancel_right₀ _ h.ne']
lemma forgeQ (p:Quench L f) : NPL (fun x=> f x/qL L x) := chill_iff.mp p

lemma purchaseInc (M:ℕ):BoreP fun x=> (M:ℝ)*countCost (incE (runway x) (weeB x)):=by
 have hv:BoreP (fun x=> (incE (runway x) (weeB x))⁻¹):=by
    simp_rw [incE,runway,inv_div,div_eq_mul_inv,inv_inv] -- tune
    exact (((BoreP.still _).grip BoreP.radius_c).join (BoreP.still _)).grip BoreP.radius_c
 have he:BoreP fun x=> Real.exp (incE (runway x) (weeB x)*2) :=
    (BoreP.still (Real.exp (2:ℝ))).tune (by
      filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x h
      rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]
      have h₁:runway x ≤ 1:=inv_le_one_of_one_le₀ (by exact_mod_cast h)
      have h₂:1 ≤ 6*(weeB x:ℝ)+2:=by linarith only [Nat.cast_nonneg (α:=ℝ) (weeB x)]
      apply Real.exp_monotone
      linarith only [div_le_one_of_le₀ (le_trans h₁ h₂) (zero_le_one.trans h₂)])
 simp_rw [countCost,div_eq_mul_inv,←inv_pow]
 exact (BoreP.still _).grip (((he.grip (BoreP.still _)).grip (hv.self _)).grip (BoreP.still _))

def spent (M:ℕ)(C:ℝ→ℝ)(x:ℝ):ℝ:=incT M (weeB x) (runway x) |C x|
lemma spentC {u:ℝ→ℝ}(p:NPL u)(M:ℕ):Chill_v (spent M u):=Chill_v.leanB
  (show Chill_v (fun x=>|u x|) from (chill_iff.mpr p).trend (Eventually.of_forall fun x=>by rw [abs_abs])) (purchaseInc _)
lemma spentH (p:NPL f)(M:ℕ):Quench L (spent M (fun x=> f x*qL L x)):= ((alloy L p).normF).bondF (purchaseInc _)
lemma spentPos (u:ℝ→ℝ)(M:ℕ)(x:ℝ)(p:0<runway x):0≤ spent M u x:=by
 have h:= count_pos (show 0< incE (runway x) (weeB x) from by unfold incE;positivity)
 exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) h.le) (abs_nonneg _)

section anchor
variable (F H:ℝ→ℝ)
abbrev barrier(L:Patch)(F H:ℝ→ℝ)(x:ℝ):ℝ:=8*(|F x|+ (radD x*|H x|)+qL L x*qL L x)
local notation "γ_" => barrier L F H
lemma barrierQ (p:Quench L F)(r:Quench L H) :Quench L γ_:=
 ((p.normF.addL (r.normF.bondF BoreP.radius_c)).addL (alloy L (chill_iff.mp (cool_q L)))).manyF _

lemma leftBarrier (x:ℝ)(t: 0 < qL L x)(s:0 < radD x):
 0 < γ_ x ∧ F x < γ_ x ∧ H x ≤ runway x*(γ_ x/8):=by
 have g:= show |F x|+ radD x*|H x|< γ_ x/8 from by unfold barrier;nlinarith only [mul_pos t t]
 have hz:= mul_nonneg s.le (abs_nonneg (H x))
 refine ⟨by linarith [abs_nonneg (F x)],by linarith [le_abs_self (F x),abs_nonneg (F x)],?_⟩
 apply (le_inv_mul_iff₀ s).mpr
 have h:=mul_le_mul_of_nonneg_left (le_abs_self (H x)) s.le
 linarith only [h,g,abs_nonneg (F x)]
end anchor
lemma coolEyes (g:ℝ→ℝ)(p:Quench L g):
 ∀ᶠ x in atTop,
 let b:=weeB x; let a:=runway x
 (0 < g x)→ degreePrice b (100*g x) a≤1/2 ∧ degreePrice b (g x) a < 1 ∧ θG b a (g x) ≤1 ∧ g x+Real.exp 1*θG b a (g x) ≤100*g x:=by
 have yu := (dollar_Q L _ p).illum_Q
 let a(i:ℝ):=runway i; let b(i:ℝ):=weeB i
 filter_upwards [(deg_chill _ (p.illum_Q)).spine_a.eventually (ge_mem_nhds
     (show (0:ℝ)<1/2 from by norm_num)),
   (deg_chill _ ((p.manyF 100).illum_Q)).spine_a.eventually
     (ge_mem_nhds (show (0:ℝ)<1/2 from by norm_num)),
   yu.spine_a.eventually (ge_mem_nhds zero_lt_one)] with x hp hf hu

 have e:=(show degreePrice (b x) (g x) (a x) ≤ 1/2 from hp)
 dsimp only
 intro w
 refine ⟨hf,lt_of_le_of_lt e (by norm_num),?_ ,?_⟩
 · rw [dollarT,pow_zero,mul_one] at hu;exact hu
 have r: (1-degreePrice (weeB x) (g x) (runway x))⁻¹ ≤ 2:=(inv_le_comm₀ (by
    change 0 < 1-degreePrice (b x) (g x) (a x);linarith only [e]) (by norm_num)).mpr (by
    change (2:ℝ)⁻¹ ≤ 1-degreePrice (b x) (g x) (a x); linarith only [e])
 have z:=mul_le_mul_of_nonneg_left r w.le
 have v:=mul_le_mul (Real.exp_one_lt_d9.le) z
     (mul_nonneg w.le (inv_nonneg.mpr (show 0 ≤ 1-degreePrice (b x) (g x) (a x) from by linarith only [e]))) (by norm_num)
 unfold θG
 change Real.exp 1*(g x*(1-degreePrice (weeB x) (g x) (runway x))⁻¹)≤ _*_ at v
 linarith only [w,v]


lemma churn (U:ℝ→ℝ)(c:Chill_v U):
 ∀ᶠ x in atTop, spanV (weeB x)*U x ≤ runway x /4 ∧
    giantG (weeB x) (runway x) (U x)≤ runway x/4:=by
 have h:=(c.leanB span_bore).leanB BoreP.radius_c
 filter_upwards [h.spine_a.eventually (ge_mem_nhds (show (0:ℝ)<1/4 by norm_num)),
   (h.leanB BoreP.radius_c).spine_a.eventually (ge_mem_nhds (show (0:ℝ)<1/4 by norm_num)),
   Work.E01.radiusB_tendsto.eventually_gt_atTop 0]
    with x s t p
 let b:=radD x
 change b*(spanV (weeB x)* U x)≤1/4 at s
 change b*(b*(spanV (weeB x)* U x))≤1/4 at t
 have hp: 0 < b:=Nat.cast_pos.mpr p
 have hq:runway x/4=b⁻¹*(1/4):=by change b⁻¹/_=_;ring

 constructor
 · rw [hq]
   exact (le_inv_mul_iff₀ hp).mpr s
 unfold giantG
 rw [hq]
 apply (le_inv_mul_iff₀ hp).mpr
 rw [show (runway x)⁻¹=b by change b⁻¹⁻¹=b; rw [inv_inv]]
 nlinarith only [t]

lemma crystals
 (F U H:ℝ→ℝ)(t:Quench L F)(r:Quench L H)(h:Chill_v U):
 ∀ᶠ x in atTop, 0<runway x ∧
 (0≤U x→ Glacier (weeB x) (runway x) (F x) (U x) (H x) (barrier L F H x)):=by
 let G:=barrier L F H
 have ht:Quench L G:=barrierQ _ _ _ t r
 filter_upwards [warm_gt L,Work.E01.radiusB_tendsto.eventually_ge_atTop 5,
    coolEyes _ _ ht,churn G ht.illum_Q,churn U h] with x y yp yu i k
 let b:=weeB x;let a:=runway x
 have hv: (5:ℝ) ≤ b:=Nat.cast_le.mpr yp -- tune
 have hw:0<radD x:=show 0 < (b:ℝ) from by linarith only [hv]
 have hp:0<a:=inv_pos.mpr hw
 have ha: 5*a ≤ 1:=show 5 * (radD x)⁻¹ ≤ 1 from by rw [←div_eq_mul_inv, div_le_one hw]; exact hv -- tune
 obtain ⟨w,e,s⟩:=leftBarrier L F H x y hw
 obtain ⟨m,n,o,p⟩:=yu w
 obtain ⟨f,j⟩:=k
 refine ⟨hp, fun q=> ⟨hp,ha,w,q,e,?_,?_,?_,m,n,o,p⟩⟩
 · rw [mul_comm]
   exact i.1.trans (div_le_self hp.le (by norm_num))
 · exact f.trans (div_le_self hp.le (by norm_num))

 · nlinarith only [s,mul_le_mul_of_nonneg_right j w.le,mul_le_mul_of_nonneg_right f w.le,
     mul_pos (show 0<runway x from hp) w]



abbrev markEG (γ:ℝ→ℝ)(x:ℝ):ℝ:=reserveT 2 6 (weeB x) (runway x) * θG (weeB x) (runway x) (γ x)
abbrev markFG (γ:ℝ→ℝ)(x:ℝ):ℝ:=reserveT 2 6 (weeB x) (runway x) * (γ x * 200)
lemma markEF (γ:ℝ→ℝ)(r:Quench L γ):Quench L (markEG γ)∧Quench L (markFG γ):=by
 have h:=dollar_Q L _ r
 unfold dollarT at h;simp only [pow_zero,mul_one] at h
 refine ⟨h.bondF (reserve_bond ..),?_⟩
 unfold markFG; simp_rw [mul_comm _ (200:ℝ)]
 exact (r.manyF _).bondF (reserve_bond ..)

-- receipt
def spells (L:Patch)(M:ℕ)(F D:ℝ→ℝ):=barrier L F (spent M (fun x=>D x*qL L x))
lemma epoch (F C D:ℝ→ℝ)(M:ℕ)(t:Quench L F)(u:NPL C)(k:NPL D):
 let U:=spent M C
 let H:=spent M (fun x=>D x*qL L x)
 let γ:=spells L M F D
 Chill_v U ∧ Quench L H ∧ Quench L γ ∧ Quench L (markEG γ)∧Quench L (markFG γ)∧

 ∀ᶠ x:ℝ in atTop,
   Glacier (weeB x) (runway x) (F x) (U x) (H x) (γ x):=by
 intro U H γ
 have y:=spentC u M
 have i:= spentH L k M
 have p:=barrierQ _ _ _ t i
 obtain ⟨r,s⟩:=markEF _ _ p
 refine ⟨y,i,p,r,s,(crystals _ _ _ _ t i y).mono (fun x u=>u.2 (spentPos C M x u.1))⟩
end Till
end YM.CF.Bay
#print axioms YM.CF.Bay.Till.epoch

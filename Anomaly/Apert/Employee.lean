import Anomaly.Apert.Consort
import Anomaly.Rack.Certify
import Anomaly.Apert.Cotton
import SatinThinSteps
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
variable {n : Side}


namespace LocalLimit
namespace Preparation
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell QuadClock Ione.Clock Moto Neon Taxi Lor
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) 

abbrev αPℓ : ℝ := max (duty_Q 6 2) (strive_E 6)
lemma costPos :0≤αPℓ:=(show 0 ≤ duty_Q 6 2 from by unfold duty_Q Jet.composeCost; positivity).trans (le_max_left ..)

def lunarF (k:BudgetPoint)(f:ℝ→ℝ)(x:ℝ):ℝ:= (1+strive_E k.order)*|f x|
abbrev estim_X(K:ℝ→ℝ):= (fun x=> (chi_f 6)*K x)
lemma bonus_r (k:BudgetPoint)(x:ℝ→ℝ)(v:ℝ) : x v ≤ lunarF k x v ∧ strive_E k.order*x v ≤ lunarF k x v:=by
  have he:= Turning.unitT k; unfold lunarF; rw [add_mul, one_mul]
  exact ⟨(le_abs_self _).trans (le_add_of_nonneg_right (mul_nonneg he (abs_nonneg _))), (mul_le_mul_of_nonneg_left (le_abs_self _) he).trans (le_add_of_nonneg_left (abs_nonneg _))⟩
lemma quench_x(R:Patch)(k:BudgetPoint)(x:ℝ→ℝ)(p:Quench R x) : Quench R (lunarF k x):= p.normF.manyF _

lemma spartan {κ:ℝ→ℝ}{r:Patch}{v t:ℝ→ℝ}(p: Chill_v κ)(w:Quench r t)(c:ℝ→ℝ)(τ:Quench r c)(k:ℕ)(D:Quench r v) : ∃ G :ℝ→ℝ, Quench r G ∧
    ∀ᶠ x:ℝ in atTop, ∃ C:ThresholdPool (radiusB x) (BScale.runway x) (inkScatter k (radiusB x) |κ x|) (estim_X t x) (inkScatter k (radiusB x) |c x|) (G x),
      let γ:= G x; let η:=BScale.runway x; let d:=(degreePrice (radiusB x) γ η); let b:=(k:ℝ) * |v x|; γ+Real.exp 1*(γ*(1-d)⁻¹+b)≤ 100*γ ∧ b+γ*(1-d)⁻¹ ≤ 1 ∧ 27*(k:ℝ) ≤ η * (radiusB x:ℝ)^2 := by
  -- increase Γ while retaining original pool inequalities. choose via K cost
  let Q:=estim_X t; let a(x:ℝ):=Q x; let E(x:ℝ):=(k:ℝ) * |v x|
  have he:Quench r (fun x=>|Q x|+E x) := (Quench.addL ((w.manyF (chi_f 6)).normF) (D.normF.manyF (k:ℝ)))
  obtain ⟨U,h,Y_⟩:= spanning r (billScatter k κ p) he (billScatter2 k _ τ)
  have hc:= (deg_chill _ h.illum_Q).spine_a.eventually (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num)); have ht:= h.illum_Q.spine_a.eventually (ge_mem_nhds (show (0:ℝ)<1/3 by norm_num));
  refine ⟨U,h,?_⟩; filter_upwards [Y_,hc,ht,Work.E01.radiusB_tendsto.eventually_ge_atTop (27*k)] with x v' z u hf
  have hz:0 ≤ E x:=mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  let η:=BScale.runway x; have hv:=v'.roof_limit; have hκ:=v'.κval
  have hA:=v'.start; rw [abs_of_nonneg (add_nonneg (abs_nonneg _) hz)] at hA
  have hg:= (le_add_of_nonneg_right hz : |Q x| ≤ _).trans_lt hA
  refine ⟨{ v' with start:=hg },?_⟩; intro γ η' d b
  have hb:0 < (radiusB x:ℝ):= inv_pos.mp hv.1
  change d≤ 1/2 at z
  have he:(1-d)⁻¹ ≤ 2 := (inv_anti₀ (by norm_num : (0:ℝ)<1/2) (show 1/2 ≤ 1-d by linarith)).trans_eq (by norm_num)
  have hy:b≤γ:=(le_add_of_nonneg_left (abs_nonneg _)).trans hA.le
  have hv':γ*(1-d)⁻¹ + b ≤ 3*γ :=by linarith only [hy,mul_le_mul_of_nonneg_left he hκ.le]
  refine ⟨?_,?_,?_⟩
  · nlinarith only [hκ,mul_le_mul_of_nonneg_left hv' ((Real.exp_pos 1).le), mul_le_mul_of_nonneg_right Real.exp_one_lt_d9.le hκ.le]
  · rw [add_comm]; exact hv'.trans (by linarith only [u])
  unfold η' BScale.runway; rw [pow_two,←mul_assoc,inv_mul_cancel₀ hb.ne',one_mul]; exact_mod_cast hf

local notation "p0"=>Y.meter.a 0
variable (Γ:ℝ)(k0:ℕ)
abbrev Xs(Ψ:ℝ→ℝ) := lunarF (Y.meter.a 0) Ψ
abbrev fees(F : ℝ→ℝ) := putTip 2 (lunarF p0 F)
abbrev stageC(H:ℝ→ℝ)(i:ℝ):= Extr_h P.R.L.val (Y.meter.a 0) Γ*fees Y H i
abbrev stageΛ(H:ℝ→ℝ)(i:ℝ):= αPℓ*(Δv (Y.meter.a 0) Γ*fees Y H i)
abbrev chargeC(H U:ℝ→ℝ)(i:ℝ):= 2*stageΛ Y Γ H i*k0+wakeL U i
abbrev chartPsi (H U:ℝ→ℝ)(i:ℝ):= wakeK k0 U i -- remove Y param?
lemma quenchingStage (H:ℝ→ℝ)(r:Quench P.R H)(U:ℝ→ℝ)(p:Quench P.R U):
    Quench P.R (fees Y H) ∧Quench P.R (stageC Y Γ H) ∧Quench P.R (stageΛ Y Γ H) ∧Quench P.R (chargeC Y Γ k0 H U)∧ Quench P.R (wakeK k0 U) := by
  have hp:Quench P.R (fees Y H) := (wakePrice k0 (lunarF p0 H) P.R (quench_x P.R p0 H r)).2.2.1
  have ht:Quench P.R (stageΛ Y Γ H):=(hp.manyF (Δv p0 Γ)).manyF _
  refine ⟨hp,hp.manyF _,ht,?_, (wakePrice k0 U P.R p).2.1⟩
  let v:= (ht.manyF (2:ℝ)).manyF (k0:ℝ); unfold chargeC; simp_rw [mul_comm (2*stageΛ Y Γ H _)]; exact v.addL (wakePrice k0 U P.R p).2.2.2.2

lemma supplyEmployment (H F:ℝ→ℝ) (s:Quench P.R H)(t:Chill_v F)(K:ℝ→ℝ)(v:Quench P.R K) :
    ∃ Z:ℝ→ℝ, Quench P.R Z ∧ ∀ᶠ x:ℝ in atTop, ∃ C:ThresholdPool (radiusB x) (BScale.runway x) (inkScatter k0 (radiusB x) |lunarF p0 F x|) (estim_X K x) (inkScatter k0 (radiusB x) |lunarF p0 H x|) (Z x),
      let γ:=Z x; let η:=BScale.runway x; let q:=degreePrice (radiusB x) γ η; let A:=(k0:ℝ)*(αPℓ * stageC Y Γ H x); γ+Real.exp 1*(γ*(1-q)⁻¹+A)≤100*γ ∧ A+γ*(1-q)⁻¹ ≤ 1 ∧ 27*k0 ≤ η*(radiusB x:ℝ)^2 := by
  have ht: Chill_v (lunarF p0 F):= (t.trend (F:=fun x=> |F x|) (Eventually.of_forall fun _=>by simp)).cheap _
  obtain ⟨G,v,h⟩:= spartan ht v _ (quench_x P.R p0 H s) k0 (((quenchingStage Y Γ k0 H s K v).2.1).manyF αPℓ)
  refine ⟨G,v,?_⟩; filter_upwards [h] with x p; obtain ⟨V,Hx⟩:= p; refine ⟨V,?_⟩; have hp:0 ≤ αPℓ*stageC Y Γ H x:=by
    refine mul_nonneg costPos (mul_nonneg ?_ ?_); unfold Extr_h; positivity; unfold fees putTip reserveT coin_n stilK BScale.runway; positivity
  dsimp only at Hx ⊢; rwa [abs_of_nonneg hp] at Hx
end Preparation
end LocalLimit
end YM.CF.Py.Rate

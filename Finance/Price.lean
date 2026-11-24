import Knotwise.Thrills
import Finance.Ace
import Compass.AlphaBase
import Compass.Arrays
import Compass.Hall
import Compass.Prime
import Compass.Starglass
import Compass.Spokes
import Compass.Poetry
import Compass.Reynolds
import Compass.Bullion
import YM.CF.Neon.Ten
import Compass.Hubs
import YM.CF.Ione.Jost
import Compass.Lode
import YM.CF.Brood.Tips
import YM.CF.Coal.Vice
import YM.CF.Moto.Band
import YM.CF.Moto.Kearn
import Compass.Jazz
import Compass.Needle
import Compass.Sloop
import YM.Push.LOCAL_SPLITTING.Orientation
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Compass
open Py
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Moto
open Vow Lilt Larch Bake Rue
open Prism Hove Oise
variable {Nq:Side}
open Ione
open scoped Mew
local notation "Ck"=> carriers Nq
open Neon
open Neon Moto Lattice.PlaqAxes
variable {g0 δ C ψ:ℝ}
open ThinGauge
lemma markStd(X:ℝ): ‖paintS (X:ℂ)‖ ≤|X|:=by
 rw [← mul_one (X:ℂ),←coat_scale]; exact (norm_smul (X:ℂ) (paintS 1)).le.trans ((by rw [Complex.norm_real,Real.norm_eq_abs]; exact mul_le_of_le_one_right (abs_nonneg _) normP))
-- error red. transfer.Canonical
variable {Q Q':BudgetPoint}{u r r' A b d:ℝ}(L0:Side)
local notation "x"=> (((L0.val:ℝ))⁻¹)
abbrev tint0 (L:Side)(B D:BudgetPoint):=Tune.qCorset B.threshold D.threshold (L.val:ℝ)
lemma κnax(h:ℝ)(v:r≥0)(w:0≤ψ)(p:|u| ≤ Real.exp 1)(f:ψ≤ x^5*r) (k:ℝ)(hz:(coat k).2=0)(hu:|k|≤r):
    κprobe naxR L0 h (A*r) ψ (u:ℂ) (coat k) ≤ (Real.exp 1 + A+2)*x^5*r:=by
 have hx:0<x:= by positivity
 unfold κprobe; simp only [Complex.norm_real,Real.norm_eq_abs, hz,Prod.fst_zero,Prod.snd_zero,norm_zero,mul_zero, zero_mul,add_zero]; unfold naxR; rw [add_zero,add_zero]
 have hh:=mul_le_mul p ((markStd k).trans hu) (norm_nonneg _) (Real.exp_pos _).le
 change _ +ψ ≤ _
 have ht:=mul_le_mul_of_nonneg_left (add_le_add_left hh (A*r)) (pow_nonneg hx.le 5); nlinarith only [ht,f,v,hx,mul_nonneg (pow_nonneg hx.le 5) v]
lemma κRate (hn:0≤r)(hA:0≤A)(h0:0≤ψ)(ph:ψ≤x^5*r)(k:ℝ)(hu: |u| ≤ Real.exp 1)(H:|k|≤r)(h:ℝ){z0 z1 z2:ℝ}(p:αPrice L0 h (A*r) ψ z0 z1 z2 (coat k) (coat b) Q Q' (u:ℂ)):
    |b - tint0 L0 Q Q'*u*k|≤ lowerCost z0 A*x^5*r:=by
 have z:(paintS (b:ℂ) - paintS ((tint0 L0 Q Q':ℝ)*u*k :ℂ)) p02 p02 = ((b - tint0 L0 Q Q'*u*k:ℝ):ℂ):=by simp [paintS]
 let k0:=κprobe naxR L0 h (A*r) ψ (u:ℂ) (coat k)
 have he:= p.red; rw [ζtap,smul_smul,show _ • ((coat k).1)=paintS ((tint0 L0 Q Q':ℝ)*u*k:ℂ) from coat_scale ..] at he
 have ht:0≤ k0:=by unfold k0 κprobe naxR; positivity
 have hx0:=κnax (A:=A) L0 h hn h0 hu ph k (by rfl) H
 calc
    _ = ‖(paintS (b:ℂ) - paintS ((tint0 L0 Q Q':ℝ)*u*k :ℂ)) p02 p02‖:=by rw [z,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ _ :=by refine ((norm_le_pi_norm _ _).trans ((norm_le_pi_norm _ _).trans he)).trans ?_
               calc
                _ ≤ |z0| *((Real.exp 1 + A +2)* x^5*r):= mul_le_mul (le_abs_self _) hx0 ht (abs_nonneg _)
                _ = _ := by unfold lowerCost; ring
lemma mint_R {q:ℝ} (p:ThinGauge.Open g0 δ C A x)(hv:0≤r)(hu:|u|≤Real.exp 1)(h':0≤ψ)(v:ψ≤x^5*r):
  let F:= fun t:ℝ=> κprobe mintR L0 q (A*r) ψ (u:ℂ) (coat t)
  C*(δ*F r)≤ yolk δ C*x^4*r ∧ C*(δ*F 0)≤ ThinGauge.shell δ C A*x^5*r:=by
 intro F; let y:=|u|
 have he(t:ℝ): F t=x^4*(|u| *‖paintS (t:ℂ)‖)+x^5*(A*r)+ψ:=by unfold F κprobe mintR; simp [coat,Real.norm_eq_abs]
 have hx:x≥0:=p.hm.le
 have ho:=markStd r
 have k: ‖paintS ((0:ℝ):ℂ)‖=0:=by rw [Complex.ofReal_zero,←zero_mul (1:ℂ),←coat_scale,zero_smul,norm_zero]
 have hF(k):0≤F k:=by rw [he]; have h:=p.asset; positivity
 rw [←mul_assoc,←mul_assoc,mul_comm C]; let d:=|δ*C|; have hd:δ*C≤d:= le_abs_self _
 have hb: x^5*(A*r) + ψ ≤ x^4*r:=by
    calc
     _ ≤ x^4*(x*(A+1))*r := by have ht:=v; nlinarith only [ht]
     _ ≤ _:=by
        nlinarith only [mul_le_mul_of_nonneg_left p.credit (mul_nonneg (pow_nonneg hx 4) hv)]
 have a(k):C*δ*F k≤d*F k:=mul_le_mul_of_nonneg_right ((mul_comm C δ).le.trans hd) (hF _)
 constructor
 · refine (mul_le_mul_of_nonneg_right hd (hF r)).trans ?_
   unfold ThinGauge.yolk; have hz:=mul_le_mul hu ho (norm_nonneg _) (by positivity)
   have hs:F r≤ (Real.exp 1+1)* x^4*r:=by rw [he,add_assoc]; rw [abs_of_nonneg hv] at hz; nlinarith only [hb,mul_le_mul_of_nonneg_left hz (pow_nonneg hx 4)]
   have hh:=mul_le_mul_of_nonneg_left (le_trans hs (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith :Real.exp 1+1≤Real.exp 1+2) (pow_nonneg hx _)) hv)) (abs_nonneg (δ*C)); apply hh.trans_eq; ring
 refine (mul_le_mul_of_nonneg_right hd (hF 0)).trans ?_; rw [he,k,mul_zero,mul_zero,zero_add]; unfold ThinGauge.shell d; nlinarith only [mul_le_mul_of_nonneg_left v (abs_nonneg (δ*C))]
end YM.CF.Compass

import SatinThinScroll
import SatinThinScale
import SatinThinPlaza
import YM.SU5.FiniteGaugeData.Marked.Journey.Grants

set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
-- Param Φ applied at P, KW
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
variable (flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)
attribute [-instance] instDecidableEqLex
variable {n:ℕ}{Pay ξC Γϕ A:ℝ}{Tξ:Hove.Grant P.K.j 2}
local notation "M"=> works_X (K:=P.K) Tξ n 6 5 HI Pay ξC Γϕ
local notation "T"=>hat P.R.L P.x
local notation "Φ"=> fun i=>allotΨ P.R.L (hat P.R.L P.x i)
variable (p:Panorama Y Tξ Pay ξC Γϕ n 2)(a:ChoiceCost (duty_Q 6 2*(works_X (K:=P.K) Tξ n 6 5 HI Pay ξC Γϕ).delta) (works_X (K:=P.K) Tξ n 6 5 HI Pay ξC Γϕ).g0 A P.R.L)
def Acting (ν:ℕ)(U:ℝ):Prop:=∀ᶠ i:ℕ in atTop,∀ k:ℕ, (Y.voyage i).kick ≤ k→ ν < Y.uv k→
 Putting P.V P.U (RootBook Y i k ν) (RootBook Y i k (ν+1)) (apt (Y.ir i) P.block P.R.L ν) (Stem Y i k ν) ((Y.voyage i).CapeT ν) ((Y.voyage i).CapeT (ν+1)) (((Y.voyage i).X (Y.uv k)).wave ν).val Chi.canonical P.J.d (Φ (ν+1)) (Φ ν) U P.h
include p a flag in
lemma ascending_cost : ∀ᶠ ν:ℕ in atTop,Acting Y ν A:=by
 obtain ⟨Z,W,V1,Kf,h,v⟩:=p.scene; let D:= M; let L:= P.R.L; let Tξ:= hat L P.x
 filter_upwards [v,(turnover P).eventually (attain_step P.R h (duty_Q 6 2*D.delta) D.g0 A a),(turnover P).eventually (colors_more P.R Γϕ (16*A))] with s p' e c
 filter_upwards [p'] with i p k S he
 specialize p k he; let V:= (Y.voyage i).X (Y.uv k); let G:= V.pull
 let X:= RootBook Y i k; have hX(v:ℕ)(w:v≤Y.uv k): (X v).p=Y.meter.a v:= (G.owns v w).width.symm
 obtain ⟨X0,Kx,Hr,Jx⟩:= flag i (Y.uv k)
 let Yb:= X0.clocks s; have hc:= Yb.leaf_mono (T (s+1)) (hat_mono (by omega)); have hB:=Yb.leaf; let s₀:=dleaf P.R.L (T s); have hk:0 ≤ s₀:=by linarith only [hB]; -- tune
 let q:= allotΨ P.R.L (T s); let r:= allotΨ P.R.L (T (s+1))
 let sQ:=X s; have hf := e sQ.p ((congrArg BudgetPoint.B (hX s he.le)).trans (Y.meter.boot s).2.1)
 have hh:L=L:=rfl; have hv:(X s).p.order=6:= (congrArg BudgetPoint.order (hX s he.le)).trans (Y.meter.boot s).2.2.2.2; have hy:(X s).p.power=2:= (congrArg BudgetPoint.power (hX s he.le)).trans (Y.meter.boot s).2.2.2.1
 rw [←hat_step, ←hv,←hy] at hf -- would rewrite in works via D? inspect. hat_step binder args; note 6 in other occurrences expand via reducible? check
 let E₁:= V.pull.note (s+1) he; have hψ:= (mul_le_mul_of_nonneg_left hf.span (mul_nonneg (by norm_num) (zero_le_one.trans a.root))).trans c; let S_:= (fullness Y i k S).cap_grant; obtain ⟨gL⟩:= S_.grant s he
 exact wheel_fast _ _ _ _ _ _ _ _ _ _ hf E₁.tone (E₁.vest (3*s₀) _ (3*s₀) (by linarith only [hc,hB]) (by linarith only [hc,hB]) (by positivity)) hψ (add_le_add_right hψ _) gL (S_.aligned s he) (S_.branch s he) (S_:=p)
#print axioms ascending_cost
end YM.CF.Py.Rate.LocalLimit.Preparation

import YM.CF.Pig.Sail
import YM.CF.Yaw.Lotus
import YM.CF.Yaw.Park
import YM.CF.Yaw.Fancy
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Wray
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
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
-- currency for direct stencil subsidy. every card paid. Acquire L before resonance ψ.Share.H flag.
abbrev stake{n:Type*}[LinearOrder n](d:ℝ)(i:Finset n):= d^i.card
section sum
variable{X:Type}[LinearOrder X][Fintype X]{C:Raid X}{u:ℝ}
lemma joined(x:Finset X)(K:ℝ):joinV C (Pi.single x K)= C x*K:=by simp [joinV,Pi.single_apply,mul_ite]
lemma stokes(p:0≤d): Turner (stake (n:=X) d):=⟨fun i=>pow_nonneg p _,by simp [stake],fun i j h=> by rw [stake,card_union_of_disjoint h,pow_add]⟩
lemma subsidY(V:Raid X)(a:ℝ):joinV C (a • V)=a*joinV C V:=by simp [joinV,mul_sum,mul_left_comm]
variable {U:Toll X}
lemma stars (a:ℝ)(d:ℝ)(k:ℕ): joinV (stake d) (Iva.cull k U a)=steel k a+ d^2*steel k (Branch.ledgerV U):=by
 rw [Iva.cull,joinVadd (B:=stake d),naked,joined]; simp_rw [Iva.thumb,Hake.joinVsum,Iva.ank,joined]; simp only [stake,card_empty,pow_zero,one_mul]; congr 1; have hp(i j:X): (pinT i j).card=2:=by simp [pinT]; -- tune decidable LeanV order
 simp_rw [hp]; unfold Branch.ledgerV steel; simp_rw [Finset.mul_sum]
lemma bareS {K:Type} : Yaw.loadH (PetalP.bud K) u=1:=by simp [PetalP.bud,Yaw.loadH]
lemma coin_up(X0:ℝ)(E:Stake.Isle)(κ:ℕ)(P:Side)(y:ℝ)(w:ℕ)(h:0 ≤ X0)(p:0 ≤ A)(ht:0 ≤ E.r1): 1 ≤ Coin_ X0 (population*(A*followV [] P)) (population*E.r1) y κ w:=by
 have hu:= Vpos [] P; have hv:0 ≤ lip w:=by unfold lip; positivity
 have hK:0≤ population:= by unfold population; positivity
 unfold Coin_; apply le_add_of_nonneg_right; positivity
-- REAL witness F(sizes) irrespective other currencies.Quot before.
lemma coupons (a d ν:ℝ)(s k:ℕ)(F:ℝ)(g:0< F) :∃ N:ℕ,∀ P:Side,N ≤ P.val → ∀ E:Stake.Isle,∀ᶠ H:ℝ in atTop,Coin_ (d*H) (population*(ν*followV [] P)) (population*E.r1) a s k ≤ F*H:=by -- parameter choose arbitrary F>0 instead.
 have hp0:0< F:= g; let B:= 2*Real.exp (a*(Yaw.χ s:ℝ))*lip k*d*(population*ν); let η K:=Real.sqrt (K:ℝ)/(K:ℝ)^2 -- K:ℝ
 have hx: Tendsto η atTop (𝓝 0):=by
    apply (tendsto_rpow_neg_atTop (show (0:ℝ)<3/2 by norm_num)).congr' (f₂:=η); filter_upwards [eventually_gt_atTop (0:ℝ)] with x t; unfold η; rw [Real.sqrt_eq_rpow]; nth_rw 1 [show -(3/2:ℝ)=(1/2:ℝ)- (↑(2:ℕ):ℝ) from by norm_num]; rw [Real.rpow_sub t,Real.rpow_natCast] -- tune
 have he:Tendsto (fun i:ℕ=>B*η i) atTop (𝓝 0):=by simpa using ((hx.comp (tendsto_natCast_atTop_atTop)).const_mul B) -- tune
 obtain ⟨N,q₁⟩:= eventually_atTop.mp (he.eventually (gt_mem_nhds hp0)); refine ⟨N,fun P p E=>?_⟩; let v:= B*η P.val; have hy:0< F-v:=sub_pos.mpr (q₁ P.val p); let C₀:= (1+4*(Real.exp (a*Yaw.χ s)*lip k*(population*E.r1)+1)); filter_upwards [eventually_ge_atTop (C₀/(F-v))] with x t; have hc: Coin_ (d*x) (population*(ν*followV [] P)) (population*E.r1) a s k = C₀ + v*x:=by unfold Coin_ C₀ v B η followV; simp only [List.length_nil]; ring
 rw [hc]; linarith [(div_le_iff₀ hy).mp t]
end sum
end YM.CF.Wray

import YM.CF.Vp929.Canon.Galley
import YM.CF.Vp929.Budget.Offset
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
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

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
/- If beta differs between two representations, gauge response null together with genuine positive kineticC gives contradiction. Uses same Lease Guard but budgets can differ. -/
set_option quotPrecheck false
open Cycle929 Larch Bake Salt Trees Push.BetaTransport
variable {K : Teller SU.group} {R : Patch} {L:ChartRatio SU.group}{V: Grace K R L}{d:ℝ}
variable {α:Side} {m B:Side}{U: Grasp V.U B d} {σ:ℝ}
local notation "Ω"=> mid m B
variable {Q Q':BudgetPoint}{h h' c C σ a b β β' :ℝ}{η:Clip}
local notation "xΘ"=> transverse (s:=Ω) σ
local notation "λt"=> AnalyticBridge.VerifiedReset.line
local notation "Ip"=> K.j
variable {R':PathData SU.group}{E F:Corr (mid m B)}{I:Interest (mid m B)}{A:Scree.Loom (mid m B)} {v v':ℂ}
local notation "X"=> construct Q R' η I β E v
local notation "Y"=> construct Q' R' η I β' F v'
local notation "Lx"=> Kp
open QuiltB
variable (Z:∀ x:Orbit (mid m B),FleetS Q.threshold x.1→ FleetS Q'.threshold x.1 → denZ (construct Q R' η I β E v) U A x = denZ (construct Q' R' η I β' F v') U A x)(p:∀ x,Guard (A x) d) (q: U.roundZ ≤ (mid m B).val)
include Z p q
local notation "Kp"=> Push.BetaTransport.kinetic
local notation "lp"=> Lx
local notation "Υ"=> Pane Ω
lemma verv_equal (x:Pane (mid m B))(g:pingS Q.threshold univ x)(g':pingS Q'.threshold univ x) : (Pastry.pane (exponentL Q E.1 x)).re-(Pastry.pane (exponentL Q' F.1 x)).re=(β-β')*Kp R' η Q x+(v'.re-v.re):=by
 let u:Orbit Ω:=(x,Classical.arbitrary (Ids Ω)); have hv:= congrArg (fun y=> ‖inner ℂ (changeM (m:=m) U (A u) I.M) y‖) (Z u (home_fleet g) (home_fleet g'))
 rw [sea_read U R' η A I E v β u (homeFlag g) q (p u),sea_read U R' η A I F v' β' u (homeFlag g') q (p u)] at hv; dsimp only [u] at hv; simp only [Complex.norm_exp,Real.exp_eq_exp,Complex.add_re,Complex.sub_re,Complex.ofReal_re] at hv
 obtain ⟨a,h,-⟩:= UVNext.CouplingReset.unmasked_precision R' η (homeFlag g); obtain ⟨t,f,-⟩:= UVNext.CouplingReset.unmasked_precision R' η (homeFlag g'); rw [channels_split x β, channels_split x β', t.trans a.symm, h,f] at hv; linarith only [hv]
omit Z p q
private lemma gauge_holo (x:tangD α)(P:BudgetPoint)(A:RegBudget α) (hQ:IncX Utrue A P h a)(g:1 ≤ h): ContDiffAt ℝ (↑(2:ℕ):WithTop ℕ∞) (fun z:ℝ=> (Pastry.pane (exponentL P A (λt x z))).re) 0:=by
 obtain ⟨s,z,e⟩:=hQ.weight; exact (ContDiffAt.sum (s:=univ) fun i _=>rind (z i) g x).congr_of_eventuallyEq (exponent_track x P A)
include Z p q
lemma vervP (σ:ℝ)(h₀:IncX Utrue E.1 Q h a)(h₁:IncX Utrue F.1 Q' h' b)(t:1≤h)(t':1≤h') (g₀:gaugeTest σ E.1 Q=0)(g₁:gaugeTest σ F.1 Q'=0)(hp:0<kineticC (mid m B) R' η Q σ) (u:ContDiffAt ℝ 2 (Kp R' η Q ∘ λt (transverse (s:=mid m B) σ)) 0) : β=β':=by
 let i:=transverse (s:=Ω) σ; let M(z:ℝ):=(Pastry.pane (exponentL Q E.1 (λt i z))).re; let M'(z:ℝ):=(Pastry.pane (exponentL Q' F.1 (λt i z))).re; let A:= Kp R' η Q ∘ λt i
 have e:M-M'=ᶠ[𝓝 0] (β-β') • A + (fun _=>v'.re-v.re):=by filter_upwards [homeS i Q,homeS i Q'] with x u u'; exact verv_equal Z p q _ u u'
 have z:= e.iteratedDeriv_eq (n:=2); have hA:ContDiffAt ℝ (↑(2:ℕ):WithTop ℕ∞) A 0:=by norm_num; exact u
 rw [iteratedDeriv_sub (show ContDiffAt ℝ (↑(2:ℕ):WithTop ℕ∞) M 0 from gauge_holo _ _ _ h₀ t) (show ContDiffAt ℝ (↑(2:ℕ):WithTop ℕ∞) M' 0 from gauge_holo _ _ _ h₁ t'),iteratedDeriv_add (show ContDiffAt ℝ (↑(2:ℕ):WithTop ℕ∞) ((β-β') • A) 0 from hA.const_smul (β-β')) contDiffAt_const,iteratedDeriv_const_smul hA,iteratedDeriv_const,if_neg (by decide : (2:ℕ)≠0), add_zero] at z
 let s:=sites Ω; have hs:0<s:= lt_of_lt_of_le zero_lt_one (sites_pos _); change s⁻¹*iteratedDeriv 2 M 0=0 at g₀; change s⁻¹*iteratedDeriv 2 M' 0=0 at g₁; rw [Or.resolve_left (mul_eq_zero.mp g₀) (inv_pos.mpr hs).ne', Or.resolve_left (mul_eq_zero.mp g₁) (inv_pos.mpr hs).ne',sub_zero] at z
 exact sub_eq_zero.mp ((mul_eq_zero.mp z.symm).resolve_right (fun k=> by change 0<s⁻¹*iteratedDeriv 2 A 0 at hp; rw [k,mul_zero] at hp; exact lt_irrefl _ hp))
end Test
end YM.CF.Py.Rate

import SatinThinPremier
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
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance
variable (i k:ℕ) {P' V: Side} {f r v m a:ℕ}
local notation "L"=>P.R.L
local notation "B"=> P.block
local notation "D"=> P.K.j
local notation "VO"=> Y.voyage i
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
/- Actual-path Lease of Parliament: convoy and roots. Any number of supports. No stencils in cutoff budgets before size. -/
-- arithmetic delivery & Versions
local notation "XP" s:max=> RootBook Y i k s
local notation:max "S" s:max=> (VO).CapeT s
/- Parliament finances. -/
variable {I:Type} [Fintype I] [LinearOrder I]
local notation:max "Rn" s:max=> slotFee P s
local notation "Ξ"=> Article I
local notation "Υ"=> Key (Article I)
local notation "ΞM"=>List (Article I)
-- first downward power. `Loyalty` reports exact density on the SAME sharp tape.
variable (o:I→Site (side Y i f))
local notation "Ƶ" s:max=> morning Y i k s
local notation "Πξ" p:max=>upRoot Y i p
local notation "Ξν" s:max =>nightSet Y i s (I:=I)
local notation "ΞV" s:max=> rideSet Y i s (I:=I)
local notation:max "flightY" p:max=>convoy Y i k p
local notation "µ" s:max=> city (Ω s)
local notation:max "R="=> zoomC P.R.L
variable {Z A:ℝ}
lemma down_C {B':ℝ}(pr:f<v)(Q:Consulate Y i k (show f+1 ≤ v from pr) A B')(v0:Credentials Y i k A f v): ∃ b:ℝ, Consulate Y i k (p:=pr.le) A b ∧ |b| ≤ zoomC P.R.L*|B'|:=by
 obtain ⟨Z,W⟩:= Q.emit; obtain ⟨g,A'⟩:= (v0.hues f le_rfl pr).gives
 let U:= warpLine g Z P.R.L A (Rn (f+1)) (Rn f); have H:=v0.vacant Y i k (show f≤f+1 from Nat.le_succ _) pr
 refine ⟨U.ticket * B', ⟨?_, ⟨hatchTopic P.R.L g Z A (Rn (f+1)) (Rn f),fun I _ _ o p=>?_ ⟩⟩,(abs_mul _ _).trans_le (mul_le_mul_of_nonneg_right U.lid (abs_nonneg _))⟩
 · rw [show v-f=(v-(f+1))+1 from by omega]; exact premier_L P.R.L _ B' U Q.aims
 obtain ⟨E,F,x,t,u⟩:= W I (heel (Vale.apt (Y.ir i) P.block P.R.L f) ∘ o) (sprint_B Y i k f (pr.trans_le v0.caps) v0.go o p);
 obtain ⟨E',F',z,a,b⟩:= @A' I _ _ Z o E F p (loosen_tabs x H.le (zero_le_one.trans v0.cost)); exact ⟨E',F',z,a,tribal _ _ _ _ pr u ⟨v0.pays,pr.trans_le v0.caps⟩ b p⟩
lemma capital_theta (p:f≤v) (x:Credentials Y i k A f v) :
    ∃ b:ℕ→ℝ,(∀ r, f≤r→∀ u:r≤v,Consulate Y i k u A (b r)) ∧
      ∀ (rk : ℕ), f ≤ rk → rk < v → |b rk| ≤ zoomC P.R.L*|b (rk+1)|:=by
 induction p using Nat.decreasingInduction with
 | self=> refine ⟨fun _=>1,fun t h w=>?_ , fun t h u=>False.elim ((lt_irrefl _) (h.trans_lt u))⟩; obtain rfl : t=v := le_antisymm w h; exact launch_card Y i k _ x
 | of_succ f p ih=>
   obtain ⟨b,h,t⟩:=ih (x.part Y i k (Nat.le_succ _) p le_rfl)
   obtain ⟨w,u,p'⟩:=down_C Y i k p (h _ le_rfl p) x; let b₀:= Function.update b f w
   have e(j:ℕ)(k:f<j): b₀ j=b j:= update_of_ne k.ne' ..; have hx: b₀ f=w:= update_self ..
   refine ⟨b₀, fun r w0 u1=>?_, fun r w0 t0=>?_⟩
   · obtain tr|rfl:=lt_or_eq_of_le w0
     · rw [e r tr]; exact h _ tr u1
     rw [hx]; exact u
   have hw: b₀ (r+1)=b (r+1):=e _ (by omega); rw [hw]; obtain t'|rfl:=lt_or_eq_of_le w0
   · rw [e r t']; exact t r t' t0
   rw [hx]; exact p'
#print axioms capital_theta
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation

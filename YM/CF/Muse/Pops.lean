import YM.CF.Muse.Post
import YM.CF.Muse.Stake
set_option autoImplicit false
set_option maxHeartbeats 890000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Wray Prism Font
local notation "B_"=> (More N)
local notation "S₁"=> (Domain N B)
local notation "dN"=> Directions SU.group (More N)
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Haro Feu Feu.Corset Nor
variable {ε δ vC C:ℝ}(Xc:SkyC k C)
open Footprint
local notation "Jr"=> preCost
local notation "tV"=> (More (mid P B))
local notation "Qd"=> (Roc (mid P B))
-- proof billing when any h.Issue on large.Support
lemma gatherP{I J A:Type*}[DecidableEq J][DecidableEq A][Fintype I][Fintype J](x:I→J)(f:J→A)(o:A)(F:I→ℝ)(d:ℝ)(h:∀ j:J,(∑ i:I with x i=j,F i)≤ d) : (∑ i:I with f (x i)=o,F i) ≤ ((Finset.univ.filter fun i:J=> f i=o).card:ℝ)*d:=by
 let B:= Finset.univ.filter fun i:J=> f i=o; let L:= Finset.univ.filter fun i:I=> f (x i)=o
 have ht(p:J)(q:p∈ B): (∑ i∈ L with x i=p,F i)= ∑ i:I with x i=p,F i:=by refine sum_congr ?_ (fun i _=>rfl); ext i; simp only [mem_filter,L,mem_univ,true_and]; exact ⟨fun i=>i.2,fun h=>⟨h.symm ▸ (mem_filter.mp q).2,h⟩⟩
 have hu:(∑ i∈B,∑ j∈L with x j=i,F j)= ∑ j∈L,F j:=Finset.sum_fiberwise_of_maps_to (s:=L) (t:=B) (g:=x) (fun i p=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2⟩) _
 change (∑ i∈L,F i) ≤ (B.card:ℝ)*d; rw [←hu]; exact (sum_le_sum (fun i p=>(ht i p).trans_le (h i))).trans_eq (by rw [Finset.sum_const,nsmul_eq_mul])
lemma realmP (θ:Seat (mid N B))(W:Qd → ℝ)(u:ℝ)(h:0 ≤u)(hw:∀ x:Seat (mid P B),(∑ i:Roc (mid P B) with i.1.val.1=x,W i)≤u): (∑ i:Roc (mid P B) with S.ratio.parent i.1.val.1=θ,W i) ≤ ((S.patch.L.val:ℝ)^4)*u:=by
 let f:= S.ratio.parent; let V:= Site (Domain P B); let J:= Finset.univ.filter fun i: V=>f i=θ
 have hx:J.card ≤ S.patch.L.val^4:=by
    have h:= Footprint.crowd S.ratio ({θ}:Support (Domain N B)); simp only [mem_singleton,card_singleton,one_mul] at h; exact h
 exact (gatherP (fun i:Qd=> i.1.val.1) f θ W u hw).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hx) h)
lemma gripK (Q:Side):((Q.val:ℝ)^4*gritY Q.val)= (Q.val:ℝ)⁻¹:=by unfold gritY; field_simp -- ring
end YM.CF.Oath

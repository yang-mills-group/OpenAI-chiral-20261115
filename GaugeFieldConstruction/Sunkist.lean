import GaugeFieldConstruction.Dryspell
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
-- sweep weight.TIO. openc slice.S.inverse. erosion
open Levier Thera Urn Nacre Salt

namespace SliceRoof
variable {N:Side}{d e a b:ℝ}
open Laic Moire
def dry_E (H:Elm N Unit d e b):Prop:=∀ S: Support (More N),∀ x, x.val=Tulip.profile (1:Pane N) → H.F S () x=0
lemma dry_loop (H:Elm N Unit d e b)(v:dry_E H):dry_E (loopF H true):=by
 intro S x h
 change (_:ℂ) • (∑ s:Sweep N,(H.Utar s true).F S () x)=_
 rw [Finset.sum_eq_zero,smul_zero]; intro i _
 rw [H.wren i true S () 1 x h, v]
 · cases h0: (i⁻¹:Sweep N).charge <;> cases h1:detX (i⁻¹:Sweep N).s <;>simp [realR,bolt,hitL,Thera.jazz,windX,h0,h1]
 rw [real_box i d 1 x h, show flashA i (1: Pane N)=1 from ?_]
 funext e; simp[flashA,stir,Lattice.pull,Step.read] -- tune
lemma sides_S(a b r s:ℝ)(hr:0≤ r)(hs:0≤ s)(va:0<a)(vb:0<b):∃ e>(0:ℝ),∃ a0>(0:ℝ),∃ C>(0:ℝ),∀ (n:Side)(d:ℝ),0<d→ d≤ e→∀ P:Aim n,P.toll a b r s→ Reef.Cry P→∃ F:Elm n Unit d a0 C, NearL F (fun _=> Moire.bloom P)∧groupShape F∧dry_E F:=by
 obtain ⟨A,x,f,g,Y⟩:= Moire.dry_warm 1 (by omega) hr va; obtain ⟨B,y,h,k,W⟩:=Moire.dry_warm 2 (by omega) hs vb
 let D:=min A B; have hd:0<D:=lt_min f h; refine ⟨D,hd,D,hd,Tenant.quota^2*(x+y),?_,fun N d w t P l p=>?_⟩
 · have he:0<Tenant.quota:= by unfold Tenant.quota; positivity
   positivity
 let E:=bloom P; have he:DryPulse D (x+y) E d:= ((Dry_down _ _ (Y N P.x l.1) _ w (t.trans (min_le_left ..))).dry_erase (min_le_left ..) le_rfl).plus ((Dry_down _ _ (W N P.y l.2) _ w (t.trans (min_le_right ..))).dry_erase (min_le_right ..) le_rfl)
 obtain ⟨F,C,u,n,hX,yT⟩:=he
 let Z:Elm N Unit d D (x+y):=⟨fun Y _=>F Y,C,fun S=>⟨fun _=>u S,fun _=>continuous_const⟩,n⟩
 exact ⟨loopF Z true,port_k Z _ true (fun _ x _ _ _=>hX x) (fun i _ x _=> prism_x i.charge (castX i) P l p x (spinU i.charge i.s) (spinZ i.charge i.s)),fun i=>fla i Z true,dry_loop Z yT⟩
#print axioms sides_S
end SliceRoof
end YM.CF.Sour
end

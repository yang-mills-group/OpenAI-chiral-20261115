import GaugeFieldConstruction.PhysA
import YM.CF.Vale.Sail
import GaugeFieldConstruction.Plush
import GaugeFieldConstruction.Uber
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
open Sour Sour.SliceRoof
set_option maxHeartbeats 240000
variable (I:Type)[LinearOrder I][Fintype I]
open SeasonH
-- raw Lattice supports.Z cut zeta
namespace MintB
open Fren
open Rue Py.Rate.Pitching.Focus.CoeffArc Py.Rate.Pitching.Focus
-- sum all.E representation
open Rue SeasonH Sault
open NormedSpace Py.Rate.Pitching.Focus.Stockpile
variable {K:Pressure.Teller SU.group}{P:RG.Patch}{m C0:Side}{b:ℝ}{C: Pricing K.j P.L P.odd_side (Vault.Thread K.j)}{D:Grasp C C0 b}
-- unnecessary extra.Level premise $ΓBoard.Properties.
open Dial Vale Vale.Grace
local notation "Λ"=>mid m C0
variable (D)(A:GramM (mid m C0))(θ:Loom (mid m C0)) (Vx:Orbit (mid m C0))(H:Key I→ RegBudget (mid m C0))(X0:List I)(B:I→ Torches (mid m C0))(X:I→ Seat (mid m C0))
local notation "G"=> A.p
lemma Neo_Ψ {P Q:BudgetPoint}(X:RegBudget n)(h:P.threshold=Q.threshold)(A:Pane n): exponentL P X A= exponentL Q X A:=by unfold exponentL; rw [h]
variable (k:ℝ)(m0:ℕ)(e:ℝ)(hp:Roof (mid m C0) k e m0 θ)(t:e≤ b)(v:A.p.threshold≤k)(w:A.F=0)(hQ:A.slip=0)(s:A.K=0)(h:A.J=vanilla _)(tD:D.roundZ≤(mid m C0).val)(vD:Pearl D)
def BookGram (z:Key I):GramM Λ:={ A with F:=A.F+H z}
include hp t v w hQ s h tD
lemma den_empty (p: flags A.p.threshold Vx.1=∅):
 let W:= Complex.exp (A.betaL θ Vx); let X:=spar K.j babyM Vx.1; let q:= changeM (m:=m) D Vx.1 babyM
 denZ A D θ Vx= W • q ∧∀ z:Key I,denZ (BookGram I A H z) D θ Vx=W • acts (tank X (exp (exponentL A.p (H z) Vx.1))) q:=by
 intro W X q; have he: θ Vx=Vx.1:= Ledger.roof_elem hp Vx.2 Vx.1 p v; have ht: IsStarProjection X:=by unfold X; rw [←he]; exact (D.broadness _ tD _).projection _ ((hp.paid _).shrink t) -- K binder specialized?
 let H': Roof Λ k b m0 θ:={ hp with paid:= fun X=>(hp.paid X).shrink t }
 have hT: relV D A.J (θ Vx)=q:=by rw [he,h]; exact Vale.curtain D m0 θ H' tD _
 have hP: spar K.j A.J.M (θ Vx)=X:=by rw [he,h]; rfl
 refine ⟨?_,fun z=> ?_⟩
 · unfold denZ; rw [GramM.board,w,hQ, Vale.still_Footprint, fuel_one _ _ _ p, add_zero, exp_zero,mul_one,hP,hT, tank_eq _ _ ht, map_one,act_one] -- tune
 let Y0:=BookGram I A H z; unfold denZ; change W • acts (tank _ (Y0.board _)) (relV D A.J (θ Vx))=_; rw [hT]; have hC: Y0.board Vx=exp (exponentL A.p (H z) Vx.1):=by unfold GramM.board Y0 BookGram; simp only; rw [w,hQ,zero_add,still_Footprint, fuel_one _ _ _ p,add_zero,mul_one]
 rw [hC,show (BookGram I A H z).J=A.J from rfl,hP]
lemma den_fail (p: flags A.p.threshold Vx.1 ≠ ∅): denZ A D θ Vx=0 ∧ ∀ z:Key I,denZ (BookGram I A H z) D θ Vx=0:=by
 let X:= spar K.j A.J.M (θ Vx); have ht:IsStarProjection X:=(D.broadness _ tD _).projection _ ((hp.paid _).shrink t)
 have hw:tank X 0=0:=by rw [tank_eq _ _ ht,map_zero]
 have hv(A':GramM Λ)(h:A'.K=A.K)(k:A'.p=A.p)(W:A'.J=A.J):denZ A' D θ Vx=0:=by
    unfold denZ GramM.board; rw [h,k,W,s,still_force _ Vx p,mul_zero]; change _ • acts (tank X 0) _=_; rw [hw,act_zero,smul_zero]
 exact ⟨hv A rfl rfl rfl, fun z=> hv _ rfl rfl rfl⟩
variable (U:Fork (mid m C0) I) (M:I→Boke (mid m C0) I)(L:ℕ)(vp:Fort (Py.KeyUp A.p) U)(r':ℝ)
variable (sM: stampK M X0)(pM:∀ i,CostP X (Py.KeyUp A.p) (M i))(tΓ:r'=Γ0 (Py.KeyUp A.p))(h₁:∀ i,∃ P a b d h C,Bouquet I i P b a h d (B i) X (M i) C)
include sM pM tΓ h₁ vD vp
lemma Evaluation_X4 (Q0:∀x:Key I,flags A.p.threshold Vx.1=∅→ cryH U Finset.univ x Vx.1= rayP (spar K.j babyM Vx.1))(v_f:Rue.FleetS A.p.threshold Vx.1)(hE:H=registerT I X L (Py.KeyUp A.p) (Keeps U r' M X0)): Kin X (fun z=>denZ (BookGram I A H z) D θ Vx) (fun z=>acts (brewK (fun i=>Ion (B i) Vx.1) X0 z) (denZ A D θ Vx)):=by
 by_cases W: flags A.p.threshold Vx.1≠∅
 · obtain ⟨u,T⟩:=den_fail I D A θ Vx H k m0 e hp t v w hQ s h tD W; simp_rw [u,T,map_zero]; exact Kin.refl X (zeroR _)
 replace W:= Classical.not_not.mp W; obtain ⟨u,T⟩:=den_empty I D A θ Vx H k m0 e hp t v w hQ s h tD W
 have he: θ Vx=Vx.1:= Ledger.roof_elem hp Vx.2 Vx.1 W v; have hx: Guard Vx.1 b:=he ▸ (hp.paid Vx).shrink t; let P:=Py.KeyUp A.p; let X':= spar K.j babyM Vx.1; let η:=changeM D Vx.1 babyM; have hy:IsStarProjection X':=(D.broadness _ tD _).projection _ hx; have hη: Sea X' η:=Spire.sea_g tD _ hx _
 let Y:= Keeps U r' M X0; have he(Z): pingS P.threshold Z Vx.1:= (shoreK _ Vx.1 v_f Z).1 (by unfold Healthy; rw [W]; simp)
 have hZ:=cash_D I X P L Vx.1 he Y (show CostP X P Y from (by unfold Y; rw [tΓ]; exact FiscalK X P U vp M X0 fun i _=>pM i)) (deepH r' U M X0 sM)
 have ho : Kin X (fun z=>acts (tank X' (exp (exponentL P (H z) Vx.1))) η) (fun z=>acts (brewK (fun i=>Ion (B i) Vx.1) X0 z) η):=by
    apply Kin.trans _ (phys_B I X Vx.1 M U r' vp.size X' hy η hη B h₁ X0 sM fun z=> Q0 z W)
    let L:= (seeF η).comp (seeFC (nursery X' hy)); rw [hE]; exact hZ.expT.map L
 let A₀:=Complex.exp (A.betaL θ Vx); simp_rw [u,T,map_smul]; exact ho.map (A₀ • ContinuousLinearMap.id ℂ _)
#print axioms Evaluation_X4
end MintB
end MastTin
end YM.CF.XGarden
end

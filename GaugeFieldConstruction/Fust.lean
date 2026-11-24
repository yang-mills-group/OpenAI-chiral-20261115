import GaugeFieldConstruction.Flamenco
set_option autoImplicit false
set_option maxHeartbeats 48000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
variable (x:Cover)(w:300<n.val)
namespace BluffV
open Cauchy
local instance : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance : Module ℂ ↥P14:= PackP.S.toModule
local instance : Module ℂ ↥P25:= PackM.S.toModule
open TableF.Lenten.Loden Phys
abbrev SpaceH:= Bool × S3
-- sort by bump.
abbrev boltSk (i:SpaceH):ℕ:= if i.1 then 3+i.2.val else i.2.val
def SummitH:= { p: SpaceH×SpaceH // boltSk p.1≤ boltSk p.2}
deriving Fintype, DecidableEq
def CornerH := Unit ⊕ SpaceH ⊕ SummitH
deriving Fintype, DecidableEq
def lotH(i: SpaceH):FactIx:=(i.1,i.2.castSucc)
abbrev tollH(x:Spair):= (x.1.1.2,x.2.1.2)
def SlipP (b:Bool)(a:S3)(x:MI×MI):MI×MI:= if b then (x.1,bump a x.2) else (bump a x.1, x.2)
def SlipS (i:SpaceH):= SlipP i.1 i.2
def choiceH: CornerH→ MI× MI
 | Sum.inl _=> (0,0)
 | Sum.inr (Sum.inl i)=>SlipS i (0,0)
 | Sum.inr (Sum.inr i)=> SlipS i.val.1 (SlipS i.val.2 (0,0))
theorem no_pulls : Injective choiceH:=by unfold Injective; decide +revert +kernel -- tune big? kernel memory?
-- $κ$ Price linear.
def fondτ (u:Tagφ)(x:MI): Mode:= ((u.1,x),u.2)
def pick_l (u v:Tagφ)(m: MI× MI):Spair:= (fondτ u m.1,fondτ v m.2)
def Sail(b:Bool)(a:S3)(x:Mode):Mode:= ((x.1.1,bump a x.1.2),x.2)
lemma fogC (i:Tagφ):primeF i=ket (fondτ i 0):= Phys.heights i.2 _ -- tune
lemma weldK (b:Bool)(a:S3)(x:Mode):Phys.stride b a.castSucc (ket x)= ket (Sail b a x):=by
 rw [Phys.stride, ← Cauchy.takes x.1 x.2,Cauchy.first,Cspace,Cshift,on_ket]; exact Cauchy.takes ..
lemma tollX (i:SpaceH)(a b:Tagφ)(u:MI×MI): sunX (lotH i) (ket (pick_l a b u))= ket (pick_l a b (SlipS i u)):=by
 unfold sunX rayK lotH; unfold pick_l; rw [←Cauchy.takes]; split
 · rw [Cauchy.second,weldK,Cauchy.takes]; unfold SlipS SlipP; split; rfl; contradiction
 rw [Cauchy.first,weldK,Cauchy.takes]; unfold SlipS SlipP; split; contradiction; rfl
abbrev PHPane:= ↥P03 × ↥P14 × ↥P25
def lineup : PHPane →ₗ[ℂ] J Spair:= heelY.coprod (μPhi4.coprod μPhi5)
lemma lineupH (x y z) : lineup (x,y,z)= heelY x+(μPhi4 y+μPhi5 z):=by unfold lineup; rw [LinearMap.coprod_apply]; congr 1
def Debye (i:CornerH):P03→ₗ[ℂ] PHPane:=by
 cases i with
 | inl _=> exact LinearMap.inl ℂ _ _
 | inr j=> cases j with
           | inl x=> exact (LinearMap.inr ℂ _ _).comp ((LinearMap.inl ℂ _ _).comp (tipSpike (lotH x)))
           | inr y=> exact (LinearMap.inr ℂ _ _).comp ((LinearMap.inr ℂ _ _).comp (tipPeak (lotH y.val.1) (lotH y.val.2)))
local notation "JX" => J Spair
def carolΦ (i: MI×MI)(A:P03): JX:=∑ p:Tagφ,∑ q:Tagφ,(skim_L false true A.val p q) • ket (pick_l p q i)
lemma podsL (A:P03): heelY A=carolΦ (0,0) A:=by unfold heelY goldΦ carolΦ; rw [LinearMap.comp_apply]; change ∑ i:Tagφ,∑ j:Tagφ,A.val (fisc false i) (fisc true j) • wedgeCR i j= _; apply sum_congr rfl; intro a _; refine sum_congr rfl fun j _=>?_ ; change _= A.val _ _ • ket (pick_l _ _ (0,0)); unfold wedgeCR; rw [fogC,fogC,Cauchy.takes]; try rfl
lemma carol_g(A:P03)(x:SpaceH)(u): sunX (lotH x) (carolΦ u A)= carolΦ (SlipS x u) A:=by unfold carolΦ; simp_rw [map_sum,map_smul,tollX]
lemma EarnD(i:CornerH)(A:P03): lineup (Debye i A)=carolΦ (choiceH i) A:=by
 cases i with
 | inl d=> rw [show Debye (Sum.inl d) A=(A,0,0) from rfl,lineupH,map_zero,map_zero,add_zero,add_zero]; exact podsL ..
 | inr d=> cases d with
           | inl d=> rw [show Debye (Sum.inr (Sum.inl d)) A=(0,spikeV (lotH d) A,0) from rfl,lineupH,map_zero,map_zero,add_zero,zero_add,scaleG,podsL,carol_g]; rfl
           | inr d=> rw [show Debye (Sum.inr (Sum.inr d)) A=(0,0,peakV (lotH d.val.1) (lotH d.val.2) A) from rfl,lineupH,map_zero,map_zero,zero_add,zero_add,scaleK,podsL,carol_g,carol_g]; try rfl
lemma songs(a b p q:Tagφ)(x y:MI×MI): pick_l a b x=pick_l p q y↔ a=p ∧ b=q∧ x=y:=by
 refine ⟨fun e=>?_,by rintro ⟨rfl,rfl,rfl⟩; rfl⟩; let F₁(i:Mode):Tagφ:=(i.1.1,i.2); exact ⟨congrArg (fun i=> F₁ i.1) e,congrArg (fun i=> F₁ i.2) e,congrArg tollH e⟩ -- tune
set_option maxHeartbeats 200000 in
lemma bondΘ (A:P03)(i j:CornerH)(p q:Tagφ): test (pick_l p q (choiceH i)) (lineup (Debye j A))= if i=j then skim_L false true A.val p q else 0:=by
 rw [EarnD]; unfold carolΦ; simp_rw [map_sum,map_smul]; let m:= test (pick_l p q (choiceH i)); have he(x y): m (ket (pick_l x y (choiceH j)))= if x=p ∧ y=q∧ i=j then 1 else 0:=by
    change Finsupp.single (pick_l x y (choiceH j)) (1:ℂ) _=_; rw [Finsupp.single_apply]; split_ifs with h e g <;> first|rfl|skip -- tune ket notation
    · exact (e ((fun ⟨v,k,a⟩=>⟨v,k,no_pulls a.symm⟩) ((songs ..).1 h))).elim
    exact (h ((songs ..).2 ⟨g.1,g.2.1, congrArg choiceH g.2.2.symm⟩)).elim
 rw [sum_eq_single p]; swap; · intro x _ g; apply sum_eq_zero; intro v _; rw [show test _ _=_ from he x v,if_neg (fun p=>g p.1),smul_zero]
 swap; · simp
 rw [sum_eq_single q]; swap; · intro t _ g; rw [show test _ _=_ from he p t, if_neg (fun p=> g p.2.1), smul_zero]
 swap; · simp
 rw [show test _ _=_ from he p q]; split_ifs <;> simp_all -- tune
-- Traffic stream kernel measure
lemma WalkS_ (P:CornerH→P03) (h: lineup (∑ p:CornerH,Debye p (P p))=0):P=0:=by
 funext i; change P i =0; apply paintU; rw [Submodule.coe_zero,map_zero]; ext x y; have he: test (pick_l x y (choiceH i)) (lineup (∑ p:CornerH,Debye p (P p)))=0:=by rw [h,map_zero]
 rw [map_sum, map_sum] at he; simp_rw [bondΘ] at he; simpa using he
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end

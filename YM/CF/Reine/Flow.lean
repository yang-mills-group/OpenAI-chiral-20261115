import YM.CF.Reine.Core
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Reine
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti Cay Slate Forge Bloch Exterior
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {s:Signed}
section
open scoped Classical
-- kernel comparison on coarse config in one frame channel
local notation "B₀"=>radiusB x
local notation "r₀"=>Stores.till x
local notation "t₀"=>fiery G x S.patch.L
local notation "E₀"=>temp x
open Vol
open Atala
variable (x:ℝ)(M: Monk G S)(F:Forest S.ratio)(V:Config G c)(U:Config G f)(q:Chi)(A:Stores S)(k:S.Choices)
private lemma wink_u {ι α:Type}[Fintype α][DecidableEq α](W:Finset ι)(B:ι→ Finset α)(H: Set.PairwiseDisjoint (W:Set ι) B)(f:α→ℝ): (∏ i:α,f i)=(∏ i∈W,∏ x∈B i,f x)*(∏ i∈(W.biUnion B)ᶜ,f i):=by rw [← prod_biUnion H,prod_mul_prod_compl]
local notation "Y₀"=>M.V
local notation "a₀"=> M.key
local notation "m₀"=> M.park
-- full X sets compute exactly near exposures
lemma allP (t m:ℕ): A.dome m= (blip S A t).biUnion fun i=> i.val.dome m:=by ext; rw [mem_biUnion]; exact totalX ..
lemma bindZ {α:Type}[Fintype α][DecidableEq α](F:α→ Support c)(t m:ℕ) : univ.filter (fun i=> ¬Disjoint (F i) (A.dome m))=(blip S A t).biUnion fun k=>univ.filter fun i=> ¬Disjoint (F i) (k.val.dome m):=by
 ext i; rw [mem_filter,mem_biUnion,allP A t]; simp_rw [mem_filter,mem_univ,true_and,Finset.not_disjoint_iff,mem_biUnion]; aesop -- tune simp exists
lemma reachP (i:Cell f){O:Stores S}{t r:ℕ}(p:i∈nearFace S (O.dome t))(h:t+10 ≤ r): S.ratio.parent i.1∈O.dome r:=by obtain ⟨w,z,W⟩:=Finset.not_disjoint_iff.mp ((mem_filter.mp p).2); obtain ⟨j,u,rfl⟩:=mem_image.mp z; exact dome_u W (by have he:=Work.E01.sep_touched i _ u; have ht:=Work.E04.parent_separation S.ratio i.1 j; rw [separation_comm (S.ratio.parent j)]; omega)
lemma reachNn (i:Bond c){O:Stores S}{t r:ℕ}(p:i∈nearNoise (O.dome t))(h:t+10 ≤ r): i.1∈ O.dome r:=by obtain ⟨w,z,W⟩:= Finset.not_disjoint_iff.mp ((mem_filter.mp p).2); exact dome_u W (by have hx:=price_pin i z (mem_insert_self ..); omega)
lemma careW (w:ℝ)(D H t:ℕ)(h:H+10≤t)(p:D≤H) : let t'(Y:Stores S):= Y.dome D; let e(Y:Stores S):=nearFace S (Y.dome H); let u(Y:Stores S):=nearNoise (t' Y);
 let f(i j l):=receipts q A x w i j l U V k
 f univ univ univ=(∏ i∈blip S A t,f (t' i.val) (e i.val) (u i.val))* f (t' A)ᶜ (e A)ᶜ (u A)ᶜ:=by
 intro P E I f'; let S':=blip S A t; have hr{α:Type}(X:Hos S t→ Finset α)(Y:α→ Site c)(h:∀ i j,j∈X i→Y j∈i.val.dome t):Set.PairwiseDisjoint (S': Set _) X:=fun i v j w t=>Finset.disjoint_left.mpr fun z a b=> disjoint_left.mp (stem_d S A v w t) (h _ _ a) (h _ _ b) -- tune implicit h
 have he:E A=S'.biUnion (fun i=>E i.val):= bindZ A (startPos S) t H; have hv:I A=S'.biUnion (fun i=>I i.val):= bindZ A pinPos t D
 have hE:= wink_u S' (fun i=> E i.val) (hr _ (fun y:Cell f=>S.ratio.parent y.1) (fun z i a=>reachP i a h)); have hI:= wink_u S' (fun i=>I i.val) (hr _ Prod.fst (fun z i a=> reachNn i a (by omega))); have hp:= wink_u S' (fun i=>P i.val) (hr _ id (fun i j a=> farther (by omega:t≥ D) (show j∈ i.val.dome D from a)))
 unfold f' receipts profilesHere prayersHere; simp_rw [prod_mul_distrib]; rw [hE,hI (tokenB A q x w U V k),hI (AnalyticBridge.Annulus1AD.bond k U),hp (AnalyticBridge.Annulus1AD.frame k U),hp (AnalyticBridge.Annulus1AD.flag x A V)]; rw [←he, ←hv, ←show P A= S'.biUnion _ from allP A t D]; unfold S'; ring
end
end YM.CF.Reine

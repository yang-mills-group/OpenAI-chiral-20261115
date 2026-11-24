import YM.CF.Reine.Tape
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
private lemma wink_uC {ι α:Type}[Fintype α][DecidableEq α](W:Finset ι)(B:ι→ Finset α)(H: Set.PairwiseDisjoint (W:Set ι) B)(f:α→ℝ): (∏ i:α,f i)=(∏ i∈W,∏ x∈B i,f x)*(∏ i∈(W.biUnion B)ᶜ,f i):=by rw [← prod_biUnion H,prod_mul_prod_compl]
local notation "Y₀"=>M.V
local notation "a₀"=> M.key
local notation "m₀"=> M.park

def fund(A:Stores S)(x w a:ℝ)(q:Chi)(V:Config G c)(U:Config G f)(k:S.Choices)(N:Support c)(F:Finset (Cell f))(B:Finset (Bond c)):= (∏ i∈F,tokenF A q x U i)*(∏ i∈B, tidal A x w a q U V k i)*((∏ i∈N,litF A x k U i)*(∏ i∈B,litB A x k U i))
lemma shareB (w v:ℝ)(D H t:ℕ)(h:H+10≤t)(p:D≤H) : let t'(Y:Stores S):= Y.dome D; let e(Y:Stores S):=nearFace S (Y.dome H); let u(Y:Stores S):=nearNoise (t' Y);
 let f(i j l):=fund A x w v q V U k i j l
 f univ univ univ=(∏ i∈blip S A t,f (t' i.val) (e i.val) (u i.val))* f (t' A)ᶜ (e A)ᶜ (u A)ᶜ:=by
 intro P E I f'; let S':=blip S A t; have hr{α:Type}(X:Hos S t→ Finset α)(Y:α→ Site c)(h:∀ i j,j∈X i→Y j∈i.val.dome t):Set.PairwiseDisjoint (S': Set _) X:=fun i v j w t=>Finset.disjoint_left.mpr fun z a b=> disjoint_left.mp (stem_d S A v w t) (h _ _ a) (h _ _ b) -- tune implicit h
 have he:E A=S'.biUnion (fun i=>E i.val):= bindZ A (startPos S) t H; have hv:I A=S'.biUnion (fun i=>I i.val):= bindZ A pinPos t D
 have hE:= wink_uC S' (fun i=> E i.val) (hr _ (fun y:Cell f=>S.ratio.parent y.1) (fun z i a=>reachP i a h)); have hI:= wink_uC S' (fun i=>I i.val) (hr _ Prod.fst (fun z i a=> reachNn i a (by omega))); have hp:= wink_uC S' (fun i=>P i.val) (hr _ id (fun i j a=> farther (by omega:t≥ D) (show j∈ i.val.dome D from a)))
 unfold f' fund; simp_rw [prod_mul_distrib]; rw [hE,hI (tidal A x w v q U V k),hI (litB A x k U),hp (litF A x k U)]; rw [←he, ←hv, ←show P A= S'.biUnion _ from allP A t D]; unfold S'; ring
variable {A k V U}
abbrev price0(F:Patch):ℝ:= (Fintype.card F.FrameTag:ℝ)
abbrev price1(F:Patch):ℝ:= (Fintype.card F.Points:ℝ)
-- explicit accounting for unweighted Tag roots.
def trig (d:ℕ)(A:Stores S):= price0 S.patch ^(A.dome d).card*price1 S.patch ^(nearNoise (A.dome d)).card
def moist (q:Chi)(A:Stores S)(k:S.Choices)(U:Config G f)(V:Config G c)(x w a:ℝ)(d D:ℕ):= (∏ i∈(nearFace S (A.dome D))ᶜ,tokenF A q x U i)*(∏ i∈(nearNoise (A.dome d))ᶜ, tidal A x w a q U V k i)
def cred0 (T:StepData c f):ℝ:= price0 T.patch ^ Fintype.card (Site c)*price1 T.patch ^Fintype.card (Bond c)
lemma trimF(a w:ℝ)(e D:ℕ)(hp:10*radiusB x ≤ e): cred0 S* fund A x w a q V U k (A.dome e)ᶜ (nearFace S (A.dome D))ᶜ (nearNoise (A.dome e))ᶜ=trig e A * moist q A k U V x w a e D :=by
 let P:Site c→ℝ:=fun _=>price0 S.patch; let Q: Bond c→ℝ:=fun _=>price1 S.patch; have ht: 0< price0 S.patch:=Nat.cast_pos.mpr Fintype.card_pos; have hv:0< price1 S.patch:=Nat.cast_pos.mpr Fintype.card_pos
 let N:=A.dome e; let F:=nearNoise N; have he(i:Site c)(p:i∈ Nᶜ):P i*litF A x k U i=1:=Eq.trans (congrArg (P i *·) (if_neg fun x=> Finset.mem_compl.mp p ((Corona.halo_mono (by omega) (Finset.Subset.refl _)) x))) (mul_inv_cancel₀ ht.ne')
 have hh(i:Bond c)(p:i∈ Fᶜ):Q i * litB A x k U i=1:=Eq.trans (congrArg (Q i *·) (if_neg (fun x=> Finset.mem_compl.mp p (keen i.1 i _ ((Corona.halo_mono (by unfold onS at x; omega) (Finset.Subset.refl _)) ((show onS A _ i from x) (show i.1∈_ from (mem_insert_self ..)))) (mem_insert_self ..))))) (mul_inv_cancel₀ hv.ne')
 have hP(U:Support c):(∏ i∈U,P i)=price0 S.patch ^ U.card:= Finset.prod_const ..; have hQ(U: Finset (Bond c)):(∏ i∈U,Q i)=price1 S.patch ^ U.card:= Finset.prod_const ..; unfold fund trig moist; rw [show cred0 S=(∏ i,P i)*(∏ i,Q i) from by rw [hP,hQ]; rfl]; rw [← prod_mul_prod_compl N P,← prod_mul_prod_compl F Q]; change (_* (∏ i∈Nᶜ,P i)*(_* (∏ i∈Fᶜ,Q i)))*_ = _
 generalize h: (∏ i∈(nearFace S (A.dome D))ᶜ,tokenF A q x U i)*(∏ i∈(nearNoise (A.dome e))ᶜ,tidal A x w a q U V k i)=u
 have hp:(∏ i∈Nᶜ,P i)*(∏ i∈Nᶜ,litF A x k U i)=1:=by rw [← prod_mul_distrib]; exact prod_eq_one he; -- tune
 have h' :(∏ i∈Fᶜ,Q i)*(∏ i∈Fᶜ,litB A x k U i)=1:=by rw [← prod_mul_distrib]; exact prod_eq_one hh;
 rw [hP N,hQ F]; nth_rw 2 [← one_mul u]; rw [←hp]; nth_rw 2 [← one_mul u]; rw [←h']; unfold F N; ring -- tune N F
end
end YM.CF.Reine

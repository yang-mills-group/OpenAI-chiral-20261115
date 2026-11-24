import YM.CF.Reine.Tint
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
lemma luxe : cred0 S= Fintype.card S.Choices:=by unfold cred0 price0 price1 StepData.Choices StepData.SitesChoice StepData.BondChoice; simp only [Fintype.card_prod,Fintype.card_fun,Nat.cast_mul,Nat.cast_pow]
lemma drive_w (u r:ℕ)(h:u+10 ≤ r):trig u A=∏ i∈blip S A r,trig u i.val:=by
 let W:=blip S A r; let P(t:Hos S r):=t.val.dome u; have hz:A.dome u=W.biUnion P:=allP A r u; have ht:nearNoise (A.dome u) =W.biUnion fun i=>nearNoise (P i):=bindZ A pinPos r u
 have he:Set.PairwiseDisjoint (W:Set (Hos S r)) P:=fun i y j k v=> Disjoint.mono (Corona.halo_mono (by omega:u≤r) (Finset.Subset.refl _)) (Corona.halo_mono (by omega:u ≤ r) (Finset.Subset.refl _)) (stem_d S A y k v)
 have hr:Set.PairwiseDisjoint (W:Set (Hos S r)) (fun i=>nearNoise (P i)):=fun i z j t v=> Finset.disjoint_left.mpr fun a l p=>Finset.disjoint_left.mp (stem_d S A z t v) (reachNn a l h) (reachNn a p h)
 simp_rw [trig,prod_mul_distrib]; rw [ht,hz,card_biUnion he,card_biUnion hr,Finset.prod_pow_eq_pow_sum,Finset.prod_pow_eq_pow_sum]
lemma givenZ (s:ℕ)(h:10*radiusB x+2 ≤ s)(a:ℝ)(p:a≠0): a ^ Fintype.card (Active A x F)= a^ Fintype.card F.Free * ∏ i∈blip S A s,a⁻¹^ Fintype.card (Frozen i.val x F):=by
 let P:= blip S A s; let B:=10*radiusB x; let C (O:Stores S):=univ.filter (fun i:F.Free=> chill O x F i)
 have he : C A=P.biUnion fun i=> C i.val:=by
    ext i; rw [mem_biUnion]; simp_rw [C,mem_filter,mem_univ,true_and]; unfold Next.SectorChange.chill; constructor; rintro (l|l)
    · obtain ⟨t,g,v⟩:= (totalX s _).mp l; exact ⟨t,g, Or.inl v⟩
    next => obtain ⟨t,g,v⟩:= (totalX s _).mp l; exact ⟨t,g,Or.inr v⟩
    rintro ⟨k,u,z⟩; exact z.imp (fun i=>(pack S k u).inside B i) fun i=>(pack S k u).inside B i
 have hf:Fintype.card F.Free=Fintype.card (Frozen A x F)+Fintype.card (Active A x F):=by rw [← Fintype.card_congr (Equiv.sumCompl (chill A x F)), Fintype.card_sum]
 have hr:Set.PairwiseDisjoint (P:Set (Hos S s)) (fun i=>C i.val):=fun i y j k v=> Finset.disjoint_left.mpr fun t p u=> v (split_w S A t.val t.val B y k ((mem_filter.mp p).2) ((mem_filter.mp u).2) (by simpa [B] using h))
 have hz(O:Stores S): (C O).card=Fintype.card (Frozen O x F):= by unfold C; symm; exact Fintype.card_subtype _
 rw [hf,pow_add,←hz, he,card_biUnion hr,Finset.prod_pow_eq_pow_sum]; change _= (_*_)* a⁻¹^ (∑ i∈P, Fintype.card (Frozen i.val x F)); simp_rw [hz]; rw [inv_pow,mul_comm (_*_),←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ p),one_mul]
lemma mold_u (r j:ℕ) (s w:ℝ)(hp:shovel S.patch+10≤ radiusB x)(u:(j+110)*radiusB x+10 ≤ r) (p:Volo S n s b C m) (ht:FuelG ℝ (fun _=>U) 0 n C)(hv:A.flags=RG.flags (temp x) V)(hf:0<fiery G x S.patch.L)(hx:fiery G x S.patch.L ≤ s/2) : let M(t):=(j+t)*radiusB x
 (Fintype.card S.Choices:ℝ)*receipts q A x w univ univ univ U V k=(∏ i∈blip S A r,(trig (M 100) i.val*cohoT A x w s q V U k (obv x j 100 i.val) (obv x j 110 i.val)))* moist q A k U V x w s (M 100) (M 110):=by
 intro M; rw [←luxe]; have he := grim x V U q A k s w p ht hv hp hf hx -- tune args
 rw [he,cohoT,Esti.total,full_F,near_full]; change cred0 S*fund A x w s q V U k univ univ univ=_; have hz: M 100 ≤ M 110:= Nat.mul_le_mul_right _ (by omega); have hH:=shareB x V U q A k w s (M 100) (M 110) r u hz; dsimp only at hH; rw [hH,mul_left_comm, trimF x q s w (M 100) (M 110) (Nat.mul_le_mul_right _ (by omega)),←mul_assoc,drive_w A (M 100) r (by change M 110+10≤r at u; omega), ← prod_mul_distrib]; refine congrArg (fun i=>i*moist q A k U V x w s (M 100) (M 110)) (prod_congr rfl fun i _=>mul_comm _ _)
end
end YM.CF.Reine

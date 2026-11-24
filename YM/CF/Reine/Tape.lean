import YM.CF.Reine.Flow
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
lemma band (d:ℝ) (J:ChartRatio G)(X:LogArray G (Active A x F))(b r:ℕ)(h:b+10 ≤ r) : let f(O:Stores S):=locals A O x F b; capsule x A F q d J univ X=(∏ i∈blip S A r,capsule x A F q d J (f i.val) X)*capsule x A F q d J (f A)ᶜ X:=by
 intro f; let U:= blip S A r; have hp:f A=U.biUnion fun i=> f i.val:=by
    have Z(i:Active A x F)(O:Stores S): i∈ f O ↔ tastes S i.val.val (O.dome b):=by show _; simp [f,locals,witnesses,tastes]
    ext i; rw [mem_biUnion,Z]; constructor
    · intro k; rcases k with k|k
      · obtain ⟨v,p,t⟩:= (totalX r _).1 k; exact ⟨_,p,(Z i v.val).mpr (Or.inl t)⟩
      obtain ⟨v,p,t⟩:= (totalX r _).1 k; exact ⟨_,p,(Z i v.val).mpr (Or.inr t)⟩
    rintro ⟨v,p,t⟩; exact Or.imp (fun x=>(pack S v p).inside b x) (fun x=>(pack S v p).inside b x) ((Z ..).mp t) -- tune no named b
 have hr : Set.PairwiseDisjoint (U:Set (Hos S r)) fun i=> f i.val:= by intro i t j p w; exact Finset.disjoint_left.mpr fun k l v=>w (split_w S A k.val.val _ _ t p (mem_filter.mp l).2 (mem_filter.mp v).2 (by simp [show b+2≤r from by omega]))
 unfold capsule; simp_rw [prod_mul_distrib,hp]; change _= ((∏ i∈U,_) * _) * _; rw [← prod_biUnion hr,← prod_biUnion hr,mul_mul_mul_comm,prod_mul_prod_compl,prod_mul_prod_compl] -- tune
-- replace entire probabilities via masses using total U ... neighbourhood ON Tax. alternative rest directly quote defaults.
lemma near_full : nearNoise (univ:Support c)=univ:=by ext; unfold nearNoise; refine mem_filter.trans ?_; refine ⟨And.left,fun p=> ⟨p,?_⟩⟩; intro h; exact disjoint_left.mp h (mem_insert_self ..) (mem_univ _)
lemma full_F : nearFace S univ=univ:=by ext i; unfold nearFace; exact mem_filter.trans ⟨And.left,fun p=>⟨p,fun h=>disjoint_left.mp h (mem_image_of_mem S.ratio.parent (Work.E01.base_touched i)) (mem_univ _)⟩⟩
lemma parcel(t:Support c)(l:ℕ):∃ A:Stores S,t⊆ A.dome l:=⟨⟨∅,∅,t⟩,fun x p=>halo_spec.mpr ⟨x,mem_union_right _ p,by simp⟩⟩ -- tune namespace S implicit? goal S implicit from conclusion
lemma grim (s w:ℝ)(p:Volo S n s b C m)(ht:FuelG ℝ (fun _=>U) 0 n C)(hp:A.flags=RG.flags (temp x) V)(h:shovel S.patch+10≤radiusB x)(he:0<fiery G x S.patch.L)(hv:fiery G x S.patch.L ≤ s/2) : receipts q A x w univ univ univ U V k= cohoT A x w s q V U k univ univ:=by
 obtain ⟨o,t⟩:= parcel (S:=S) (univ : Support c) 0; have hz:o.dome 0=univ:=Finset.Subset.antisymm (subset_univ _) t
 have ht' := works_b (r:=0) A q k (fun _:ℝ=>U) 0 ht o univ (subset_univ (o.dome (0+shovel S.patch))) le_rfl h he hv p w V hp; simp_rw [hz,full_F,near_full] at ht'; exact ht'.symm
end
end YM.CF.Reine

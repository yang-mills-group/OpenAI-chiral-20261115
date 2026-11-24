import YM.CF.Rill.Fair
import YM.CF.Atala.Zork
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Cube Lat Atala
attribute [local instance] opCStarAlgebra
lemma virgP(A:Stores S)(U V:Config G f)(D:ℕ)(Y:Support c)(hA:A.dome (D+12)⊆Y)(h:∀ i:Bond f,S.ratio.parent i.1∈Y→ S.ratio.parent i.1∉A.dome D→ V i=U i)(X:Finset (Hos S r))(u:X⊆ blip S A r)(W: Support f)(p:∀ i∈W,∀ j∈W, separation i j ≤ 8)(ht:D+30≤r): Agrees W (valve S U V X D) U ∨ Agrees W (valve S U V X D) V:=by
 by_cases g:∃ i:Bond f,i.1∈W∧ ∃ O∈X,tastes S i (O.val.dome D); swap
 · exact Or.inl (fun i e t=> if_neg fun v=>g ⟨_,e,v⟩)
 obtain ⟨i,l,k,t,v⟩:=g; refine Or.inr fun j q r'=>?_ 
 unfold valve; split; rfl
 next hz=>
    have hp:S.ratio.parent i.1∈A.dome (D+1):= (Corona.halo_mono le_rfl (show k.val.place ⊆ A.place from fun i p=>by rw [← bloomE S A r]; exact mem_biUnion.mpr ⟨k,u t,p⟩)) (driftK S i v); refine (h j (hA (dome_u hp (by have hg:= Work.E04.parent_separation S.ratio i.1 j.1; have hh:=p _ l _ q; omega))) (fun w=> hz ?_)).symm -- tune
    obtain ⟨y,w,z⟩:=halo_spec.mp w; rw [← bloomE S A r] at w; obtain ⟨a,b,d⟩:=mem_biUnion.mp w; have hg:tastes S j (a.val.dome D):=Or.inl (halo_spec.mpr ⟨_,d,z⟩); have he:= split_w S A i j D (u t) b v hg (by have he:=p _ l _ q; omega); exact ⟨k,t,he.symm ▸hg⟩
lemma safeT (A:Stores S)(U V:Config G f)(D:ℕ)(Y:Support c)(hA:A.dome (D+12)⊆Y)(h:∀ i:Bond f,S.ratio.parent i.1∈Y→ S.ratio.parent i.1∉A.dome D→ V i=U i)(X:Finset (Hos S r))(u:X⊆ blip S A r)(ht:D+30≤r)(p:Guard U e)(hv:Guard V e): Guard (valve S U V X D) e:=by
 let P:=valve S U V X D; have h(H:Type)[DecidableEq H][Fintype H](B:SU.E→* UNI H)(z:PlaqBound B U e)(v:PlaqBound B V e): PlaqBound B P e :=by
    intro a i j k; let l:=square i j; let W:Support f:= (visits a l).toFinset
    have hg(C:Config G f)(p:Agrees W P C): travel P a l=travel C a l:= travel_local a l _ _ (fun i t j=>p i (List.mem_toFinset.mpr t) (List.mem_toFinset.mpr j)); -- tune
    rcases virgP A U V D Y hA h X u W (fun i g j t=>by have he:=view_g a l i j (List.mem_toFinset.mp g) (List.mem_toFinset.mp t); exact he) ht with q|q
    · rw [show travel P a (square i j)=_ from hg _ q]; exact z a i j k
    rw [show travel P a (square i j)=_ from hg _ q]; exact v a i j k
 exact ⟨h _ _ p.1 hv.1,h _ _ p.2 hv.2⟩ -- duplicate
end YM.CF.Rill

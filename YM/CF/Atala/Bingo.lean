import YM.CF.Atala.Court
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Atala
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
open CF.Forge
variable (S)
lemma bloomE (A:Stores S)(t:ℕ): (blip S A t).biUnion (fun i=> i.val.place)=A.place:=by
 nth_rw 2 [←stem_t S A t]; rw [place_plots]; unfold Pear; rw [vase_c,biUnion_biUnion]; exact Finset.biUnion_congr rfl fun i _=>by rw [place_plots]
abbrev tastes(i:Bond f)(P: Support c):Prop:= S.ratio.parent i.1∈P ∨ S.ratio.parent (i.1+Lattice.step i.2)∈P
def valve (x y: Config G f)(A:Finset (Hos S r))(D:ℕ): Config G f:= fun i=> if ∃ j∈A,tastes S i (j.val.dome D) then y i else x i
lemma valve_c(A:Stores S)(U V:Config G f)(r D:ℕ)(h:∀ i:Bond f,S.ratio.parent i.1 ∉ A.dome D → V i=U i):valve S U V (blip S A r) D=V:=by
 funext i; unfold valve; split; rfl; next p=>
   exact (h i (fun v=>p (by
     obtain ⟨z,h,k⟩:=halo_spec.mp v; rw [←bloomE S A r] at h; obtain ⟨j,p,l⟩:=mem_biUnion.mp h; exact ⟨j,p, Or.inl (halo_spec.mpr ⟨_,l,k⟩)⟩))).symm
lemma driftK {O:Stores S}{d:ℕ}(i:Bond f)(p:tastes S i (O.dome d)): S.ratio.parent i.1 ∈ O.dome (d+1):=by
 unfold tastes at p; rcases p with v|v; · exact (Corona.halo_mono (by omega : d≤d+1) (Subset.refl _)) v
 exact dome_u v (by have h:=Work.E03.parent_step S i.1 i.2; rw [separation_comm] at h; omega)
lemma split_w(A:Stores S)(x y:Bond f)(D:ℕ){O O':Hos S r}(p:O∈blip S A r)(hp:O'∈blip S A r)(t:tastes S x (O.val.dome D))(k:tastes S y (O'.val.dome D))(h:separation x.1 y.1 +D+2≤r): O=O':=by
 have hx:= Work.E04.parent_separation S.ratio x.1 y.1; by_contra g; apply disjoint_left.mp (stem_d S A (show O∈ ((blip S A r):Set _) from p) hp g) (dome_u (driftK _ _ t) (by omega : D+1+separation (S.ratio.parent x.1) (S.ratio.parent y.1)≤ r)); exact (Corona.halo_mono (by omega : D+1 ≤ r) (Subset.refl _)) (driftK _ _ k)
lemma virgin(A: Stores S)(U V:Config G f)(D:ℕ)(h:∀ i:Bond f,S.ratio.parent i.1 ∉ A.dome D → V i=U i)(X: Finset (Hos S r))(hp:X⊆ blip S A r)(W:Support f)(p:∀ i∈ W,∀ j∈W, separation i j +D+2≤ r): Agrees W (valve S U V X D) U ∨ Agrees W (valve S U V X D) V:=by
 let P(i:Bond f):Prop:=∃ j∈X,tastes S i (j.val.dome D)
 by_cases g:∃ i:Bond f,i.1∈ W∧P i; swap
 · exact Or.inl (fun i e t=> if_neg fun v=>g ⟨_,e,v⟩)
 obtain ⟨i,l,k,t,u⟩:=g; refine Or.inr fun j p' q=>?_ ; by_cases v:P j; exact if_pos v; change (if _ then _ else _)= _; rw [if_neg v]; exact (h _ (fun w=> v (by
   obtain ⟨y,w,z⟩:=halo_spec.mp w; rw [← bloomE S A r] at w; obtain ⟨a,b,d⟩:=mem_biUnion.mp w; have ht:tastes S j (a.val.dome D):= Or.inl (halo_spec.mpr ⟨_,d,z⟩); have he:= split_w S A i j D (hp t) b u ht (p _ l _ p'); exact ⟨k,t,(he.symm ▸ ht)⟩ ))).symm
lemma port_nest(X: Finset (Hos S r))(O:Hos S r)(U V:Config G f)(D:ℕ)(h:D+1≤r): Agrees ((danceL S O.val r)ᶜ:Support f) (valve S U V X D) (valve S U V (insert O X) D):=by
 intro i g p; have hv:¬ tastes S i (O.val.dome D):=fun v=> (Finset.mem_compl.mp g) (dance_cover S O.val ((Corona.halo_mono h (Subset.refl _)) (driftK _ _ v)))
 simp [valve,hv] -- duplicity
open Cube Lat
-- separate file matrix
end YM.CF.Atala

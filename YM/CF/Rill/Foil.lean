import YM.CF.Rill.Latch
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Atala Cube
variable {S: StepData (More c) (More f)} {E F Y:Support (More c)}{M:Monk G S}{T:Tube G S}{A:Loom c}{A':Loom f}{U:Config G (More f)}{k:ℕ}
abbrev proxP(S:StepData c f) (m:Stores S)(n:ℕ):= Passage S (m.dome n)
lemma flue(p:halo (k+30) Y ⊆ E)(h: M.key.dome (5*radiusB x)⊆ E)(hx:1000≤radiusB x)(hk:k≤radiusB x): IceK A' (Passage S Y) (Passage S E) (proxP S M.key (5*radiusB x)) (Passage S M.key.place) k e:=by
 refine ⟨fun i v=>mem_filter.mpr ⟨mem_univ _, p ((Corona.halo_mono (show k+10+1≤k+30 from by omega) (Subset.refl _)) ((mem_filter.mp (parent_hK _ v)).2))⟩,fun i t=>mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp t).2⟩,fun i t=>?_⟩
 exact mem_filter.mpr ⟨mem_univ _,(Corona.halo_mono (by omega : 2*k+20+1 ≤5*radiusB x) (Subset.refl _)) ((mem_filter.mp (parent_hK _ t)).2)⟩
-- at motion throughout where sees.Direct constant(U) for frozen
lemma forke(P Q:HomeL (More c) (More f))(p:P.2.1=Q.2.1)(hy:100≤radiusB x): Agrees (halo 12 (proxP S M.key (5*radiusB x))) (legL M T x q d l P) (legL M T x q d l Q):=by -- need threshold
 intro i u v; have hp:= (mem_filter.mp (parent_hK (S:=S) (M.key.dome _) u)).2
 by_cases h:i∈ M.park.trunks; · exact (tipS (M:=monkD M P) _ h).trans (tipS (M:=monkD M Q) i h).symm
 let y:M.park.Free:=⟨i,h⟩; have hh:chill M.key x M.park y:=by
    apply Or.inl; change S.ratio.parent i.1∈ M.key.dome (10*radiusB x); obtain ⟨s,v,g⟩:=halo_spec.mp hp; exact Atala.dome_u v (by omega)
 let t:Frozen M.key x M.park:=⟨y,hh⟩; suffices ∀ P:HomeL (More c) (More f), legL M T x q d l P i=P.2.1 i by rw [this,this,p] -- tune
 intro P; let V:=monkD M P; exact (held_physical x V.key V.park V.V (V.bush x) (V.fuel x T q d l P.2.2.1) t)
lemma footJ (Y:Support (More c))(h:halo (k+10) Y⊆ E)(p:M.key.dome (4*radiusB x)⊆ E)(hx:1000≤radiusB x)(hk:k ≤ radiusB x): IceK A Y E (halo (4*radiusB x) M.key.flags) M.key.flags k e:=by
 exact ⟨h,Subset.trans (Corona.halo_mono le_rfl (fun i v=> mem_union_right _ v)) p, Corona.halo_mono (by omega) (Subset.refl _)⟩
def unrest(C: Finset (Seat c))(i:ℕ): Finset (Bond (More c)):= univ.filter fun b=>Disjoint (ends b) (halo (5*i) C)
lemma padP(p:RG.BudgetPoint)(X:Support (More c))(V: Directions G (More c)):openG p X V=wakeB (unrest X p.B) V:=by funext i; unfold openG; rw [steadyB]; simp [unrest]
lemma calmP{m:ℕ}(U: Orbit c)(h:1000≤radiusB x)(p:radiusB x≤ m)(z:Directions G (More c)): Agrees (halo 12 (halo (4*radiusB x) M.key.flags)) U.1 (gyrate (unrest M.key.flags m) U.1 z):=by
 intro i s t; obtain ⟨q,v,w⟩:=halo_spec.mp s; obtain ⟨a,v,l⟩:=halo_spec.mp v; have hx:i∉ unrest M.key.flags m:=fun k=> disjoint_left.mp ((mem_filter.mp k).2) (mem_insert_self i.1 _) (halo_spec.mpr ⟨a,v,(separation_triangle a q i.1).trans (by omega)⟩); unfold gyrate Function.comp increment; rw [steadyB, if_neg hx]; simp
end YM.CF.Rill

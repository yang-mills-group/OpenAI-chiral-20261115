import YM.CF.Eire.Rail
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Eire
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(u:S.ratio=Rush.ratio G) (z:Odd G.count.val)(e:ℝ)(g:0<e)(X: Meter TailB G e)(V: Meter Grave G e)
variable {T:Tube SU.group S}{x s e b' w t a b d β:ℝ}{r k l k':ℕ}{U:Scree.Loom (mid N B)}{C:Scree.Loom (mid P B)}{M K:Monk SU.group S}{q q':Chi}
local notation "bay"=> Stilo.bay
-- synthesis geometry.W.Body flag. Need NOT assume Flag match except on bay. family ALL placements generated from token ink.
variable {ι:Type}[Fintype ι][DecidableEq ι]
lemma fonts (P Q:Finset (Kite S r))(L W:Support (Domain N B))(d:Disjoint L W)(h:∀ i∈Q,stem S i.1⊆ W)(Z:Mark S)(v:¬Disjoint (spotting S Z) L): Z∈plots (cook S P)↔Z∈ plots (cook S (P∪Q)):=by
 rw [wears,wears,union_biUnion,mem_union]; have hx: ¬ Z∈ Q.biUnion (fun i=> plots i.1.val):=by
    intro a; obtain ⟨i,t,u⟩:=mem_biUnion.mp a; have hz: spotting S Z⊆ stem S i.1:=by rw [stem,palm_v]; exact fun x k=> mem_biUnion.mpr ⟨Z,u,halo_subset _ _ k⟩ -- Z s attrib
    exact v (Disjoint.mono_left (hz.trans (h i t)) d.symm)
 tauto
lemma meet_l (X:Finset (Kite S r))(P: Site (Domain N B)): P∈ (cook S X).place ↔ ∃ i∈X,P∈i.1.val.place:=by rw [place_plots,wears,biUnion_biUnion]; simp_rw [place_plots]; exact mem_biUnion
abbrev trot(U: Monk SU.group S)(A:Stores S):= {U with key:=A}
lemma burn_r (M:Monk SU.group S)(P Q:Finset (Kite S r))(L W:Support (Domain N B))(d:Disjoint L W)(h:∀ i∈Q,stem S i.1⊆W) : Duo SU.group S (trot S M (cook S P)) (trot S M (cook S (P∪Q))) L:=by
 let Y:= cook S P; let Z:= cook S (P∪Q)
 have ht(i:Site (Domain N B))(t:i∈L): i∈ Y.place ↔ i∈Z.place:=by
    rw [show i∈Y.place↔_ from meet_l ..,show i∈Z.place↔_ from meet_l ..]; refine ⟨fun ⟨i,v,l⟩=>⟨i,mem_union_left _ v,l⟩, fun ⟨i,v,u⟩=>⟨i,(mem_union.mp v).resolve_right (fun l=>Finset.disjoint_left.mp d t (h _ l (halo_subset _ _ u))),u⟩⟩ -- tune
 refine ⟨⟨ht,fun _ _=> rfl,fun _ _=> rfl,fun _ _=> Iff.rfl, fun _ _ _=>rfl,fun _ _=> rfl,fun _ _=>rfl⟩,fun z g=>?_,fun z g=>?_,fun z g=>?_⟩
 · have ht:=fonts S P Q L W d h (.inl (.inl z)) g; simpa only [vase_a S,inl_mem_disjSum] using ht
 · have ht:=fonts S P Q L W d h (.inl (.inr z)) g; simpa only [vase_a S, inr_mem_disjSum,inl_mem_disjSum] using ht
 have ht:= fonts S P Q L W d h (.inr z) (fun l=> Finset.disjoint_left.mp l (mem_singleton_self _) g); simpa only [vase_a S,inr_mem_disjSum] using ht
open Atala
local notation "B0"=>radiusB x
-- horizon assumption is just Bell on FULL physical slice centered all Stores, even mismatched. supplied via Vital and size p, grants unmasked. derived local Pose.
lemma peal(M:Monk SU.group S) (X: Finset (Kite S r))(Ω:Ride S)(h:pureK S X)(p:(flags (temp x) M.V)∩bay Ω=(cook S X).flags)(u:1000≤ radiusB x)(v:∀ i∈ X,Lattice.halo ((l+90)*radiusB x) (Eire.frameP S i)⊆ bay Ω)(g:0<a)(j:a<b)(w:t<s)(hr:Ready T x) (k:∀ Y:Stores S,Y.flags=flags (temp x) M.V → Bell S (trot S M Y) x T q d l β t a): let A:=trot S M (cook S X); PaneL A (erosion ((l+70)*radiusB x) (bay Ω)) x s b (A.sent x T q d l β):=by
 intro A; let Y:= cook S X; let P:=cusp Y x M.V; let L:=bay Ω; have hx:L∩flags (temp x) M.V= Y.flags:=by rw [←show _=Y.flags from p]; rw [inter_comm]
 have ht:=cusp_d Y (M:=A) rfl hx M.V; exact uplift ht.toBeat hr ht.view hx.le (k P rfl) w j g u (erosion_c ..)
end YM.CF.Eire

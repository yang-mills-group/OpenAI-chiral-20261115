import YM.CF.Eire.Waxes
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Eire
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
variable {N A B:Side}(G:Ratio (mid N B) (mid A B))(S:StepData (Domain N B) (Domain A B)){x:ℝ}{k r j l M:ℕ}
variable {ι:Type}[Fintype ι][DecidableEq ι](X:ι→ leaf (Site (Domain N B)))
abbrev Roc(N:Side) := Hub N × Bool
abbrev Rust(N:Side):=Roc N ⊕ Force N
def rustL(N:Side) (x: Rust N): Hub N:= Sum.elim Prod.fst (fun p=>p.val.1) x
abbrev Folk (r:ℕ)(ι:Type):= Kite S r⊕ Rust (mid A B) ⊕ ι
abbrev Troupe(r:ℕ)(ι:Type):=Finset (Folk S r ι)
def Jig (k:ℕ) (Y: Kite S r): leaf (Site (Domain N B)):= ⟨halo k (frameP S Y), (stem_p S Y.1).mono ((frame_s ..).trans (halo_subset ..))⟩
def port (Y:Rust (mid A B)):= hatY S (inspected (rustL (mid A B) Y).val.2)
lemma heldY(Y: Hub (mid A B)):(Y.val.2).Nonempty:=⟨Y.val.1,Y.property⟩
def pore (k:ℕ)(Y:Rust (mid A B)):leaf (Site (Domain N B)):=⟨halo k (port S Y), (((heldY (B:=B) _).mono subset_union_left).image _).mono (halo_subset ..)⟩
def BranchX (k:ℕ): Folk S r ι→ leaf (Site (Domain N B)) := Sum.elim (Jig S k) (Sum.elim (pore S k) X)
abbrev penn (P:Troupe S r ι): Stores S:= cook S P.toLeft
def rendL (T:Finset (Force (mid A B))):= T.biUnion fun i=> i.val.2
def earn (V:Config SU.group (Domain A B))(t:ℝ)(P: Troupe S r ι):Prop:= let R:= P.toRight.toLeft.toRight; rendL R= brushK (penn S P) V t ∧ Set.PairwiseDisjoint (R:Set (Force (mid A B))) fun i=>i.val.1.val.2
local notation "bay"=> Stilo.bay
variable {P Q:Troupe S r ι} {H R:Crowd (Site (Domain N B))}(p:Palot.fits (BranchX S X k) P H)
include p
lemma lodX (i:Folk S r ι)(h:i∈ P) : (BranchX S X k i).val ⊆ bay H:=by exact Subset.trans (by exact Eq.le (bay_beam _).symm) (bay_m (p i h))
lemma litG(i:Kite S r)(h:i∈ P.toLeft): stem S i.1⊆ bay H:= ((frame_s S i).trans (halo_subset k _)).trans (lodX S X p (Sum.inl i) (mem_toLeft.mp h)) -- implicit r unification
lemma litL(i:Kite S r)(h:i∈ P.toLeft): i.1.val.flags ⊆ bay H:= by refine Subset.trans (show _⊆ i.1.val.place from subset_union_right) ((halo_subset _ _).trans (litG S X p i h)) -- tune
lemma litF (i: Rust (mid A B))(h:i∈ P.toRight.toLeft): (rustL _ i).val.2 ⊆ Passage S (bay H):=by
 intro j t; exact mem_filter.mpr ⟨mem_univ _, lodX S X p _ (mem_toRight.mp (mem_toLeft.mp h)) (halo_subset k _ (mem_image_of_mem S.ratio.parent (mem_union_left _ t)))⟩ -- tune
lemma pli (h:Palot.fits (BranchX S X k) Q R)(d:Disjoint (bay H) (bay R)) : Disjoint P Q:=Finset.disjoint_left.mpr fun _ t v=> fits_i (p _ t) (h _ v) d
lemma pli_s(h:Palot.fits (BranchX S X k) Q R)(d:Disjoint (bay H) (bay R)): pureK S (P∪Q).toLeft ↔ pureK S P.toLeft∧pureK S Q.toLeft:=by
 rw [toLeft_union]; exact gloss fun i v j t _=>Disjoint.mono (litG S X p i v) (litG S X h j t) d
lemma rend_p : rendL (P.toRight.toLeft.toRight)⊆ Passage S (bay H):= biUnion_subset.mpr fun i h=> i.property.2.trans (litF S X p _ (mem_toRight.mp h))
lemma rend_s(U:Config SU.group (Domain A B))(t:ℝ): brushK (penn S P) U t⊆ Passage S (bay H):=by
 intro i g; have hv:=wornB (t:=t) U P.toLeft g -- tune
 obtain ⟨j,t,v⟩:=mem_biUnion.mp ((mem_filter.mp hv).2); exact mem_filter.mpr ⟨mem_univ _, litG S X p j t v⟩
omit p
lemma passage_g{H R:Support (Domain N B)}(d:Disjoint H R):Disjoint (Passage S H) (Passage S R):=Finset.disjoint_left.mpr fun i t g=> Finset.disjoint_left.mp d (mem_filter.mp t).2 (mem_filter.mp g).2
include p
lemma rend_r(h:Palot.fits (BranchX S X k) Q R)(d:Disjoint (bay H) (bay R))(U:Config SU.group (Domain A B))(t:ℝ): earn S U t (P∪Q) ↔ earn S U t P ∧ earn S U t Q:=by
 simp only [earn,toRight_union,toLeft_union]; have hl:= passage_g S d
 have hh:brushK (penn S (P∪Q)) U t=brushK (penn S P) U t∪brushK (penn S Q) U t:=by simp only [penn,toLeft_union,wornG,union_biUnion] -- tune
 rw [hh,show rendL (P.toRight.toLeft.toRight∪Q.toRight.toLeft.toRight)= rendL P.toRight.toLeft.toRight∪rendL Q.toRight.toLeft.toRight from union_biUnion,gem hl (rend_p S X p) (rend_s S X p U t) (rend_p S X h) (rend_s S X h U t),gloss]; tauto
 exact fun i v j t _=> Disjoint.mono (litF S X p _ (mem_toRight.mp v)) (litF S X h _ (mem_toRight.mp t)) hl
omit p
def capG (F:Support (Domain N B))(V:Config SU.group (Domain A B))(t:ℝ)(P:Troupe S r ι)(H:Crowd (Site (Domain N B))):Prop:= pureK S P.toLeft ∧ earn S V t P ∧ F∩bay H=(penn S P).flags
include p
lemma bottom : (penn S P).flags⊆ bay H:=by unfold penn; rw [flags_g]; exact biUnion_subset.mpr fun i t=>litL S X p i t
lemma earn_s (h:Palot.fits (BranchX S X k) Q R)(d:Disjoint (bay H) (bay R))(t:ℝ)(U:Config SU.group (Domain A B))(F:Support (Domain N B)):
 capG S F U t (P∪Q) (H⊔R) ↔ capG S F U t P H ∧ capG S F U t Q R:=by
 have hx: F ∩ bay (H⊔R)=F∩bay H ∪ F∩bay R:=by rw [bay_hat d, inter_union_distrib_left] -- tune
 have he: (penn S (P∪Q)).flags=(penn S P).flags ∪ (penn S Q).flags:=by simp only [penn,toLeft_union,flags_g,union_biUnion]
 unfold capG; rw [hx,he,gem d inter_subset_right (bottom S X p) inter_subset_right (bottom S X h), rend_r S X p h d, pli_s S X p h d]; tauto
end YM.CF.Eire

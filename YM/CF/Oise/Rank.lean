import YM.CF.Oise.Mark
import YM.CF.Stake.Loom
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oise
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
section
open Scroll Yaw Phase Acorn Spire Eire
variable {ι U':Type}[MeasurableSpace ι]
local instance (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
variable {N P B L:Side}{k j r:ℕ}{e D a b c d t w:ℝ}{J:Pride (mid P B)}{Y:Tints P B e}{ho: Odd L.val}{A':Pricing j L ho (Thread j)}{P':Grasp A' B e}{U:∀ S:Support (Domain P B),Lend P B e S}{Z:Aim (mid P B)}{Z0:Male}
local notation "ϰ"=> (mid P B)
variable{S: StepData (Domain N B) (Domain P B)}(X:Hos S r)
local notation "R'"=> (danceL S X.val r)
local notation "ψ"=> gau (mid P B) × Castle P B e (danceL S X.val r)
variable (v:Dyes D e J k Y a b)(p:Vista P' Z0 Z U k t d c w)
open Plume
local instance seqM : MeasurableSpace (List (Hos S r)):= ⊤
local instance : MeasurableSingletonClass (List (Hos S r)):=⟨fun _=>trivial⟩
lemma pair_m {I X:Type}[Countable I][MeasurableSpace X](U:X→I→ I →Prop)(p:∀ i j,MeasurableSet {x| U x i j})(L:List I) : MeasurableSet {x| List.Pairwise (U x) L}:=by
 induction L with| nil=> simp| cons i L h=> simp_rw [List.pairwise_cons, Set.setOf_and,Set.setOf_forall]; exact MeasurableSet.inter (MeasurableSet.iInter fun i=> MeasurableSet.iInter fun _=>p _ _) h
lemma walks_m : Measurable (@Plume.walksK N P B S r):=by
 let V:= Ids (mid P B); have hp(x:Hos S r): Measurable fun j:V=> deed j x:=by
    unfold Plume.deed; dsimp only
    exact atlas_m _ (fun (U:V) i=> priorP U i) ((mastM _).comp (measurable_pi_lambda _ fun i=> (measurable_pi_apply _).fst)) (fun i=> (measurable_pi_apply _).fst)
 let U(i:V):= suitsG (deed i: Hos S r→ℝ); have h(i j:Hos S r):MeasurableSet {x:V|U x i j}:=by
    unfold U suitsG sue; simp_rw [Prod.Lex.toLex_le_toLex,Set.setOf_or, Set.setOf_and]; exact (measurableSet_lt (hp _) (hp _)).union ((measurableSet_eq_fun (hp _) (hp _)).inter (by simp)) -- tune measurable Const
 apply measurable_to_countable; intro wf; let x:= walksK (S:=S) (r:=r) wf; have p: x.Nodup∧x.toFinset=univ:=⟨sort_nodup ..,sort_toFinset ..⟩; change MeasurableSet (walksK ⁻¹' ({x}: Set (List (Hos S r))))
 let H:= {x':V | x.Pairwise (U x')}; rw [show (@Plume.walksK N P B S r) ⁻¹' {x}= H from ?_]; exact pair_m U h x
 ext i; change walksK i=x↔ List.Pairwise (U i) x; refine ⟨fun q=> q ▸ (show List.Pairwise (U i) (walksK i) from pairwise_sort .. ),fun k=> List.Perm.eq_of_pairwise' (pairwise_sort ..) (show List.Pairwise (suitsG (Plume.deed i)) x from k) ?_⟩ -- tune
 exact List.perm_of_nodup_nodup_toFinset_eq (sort_nodup ..) p.1 ((sort_toFinset ..).trans p.2.symm)
-- synt PAINT measurable with unreadable U outside P.Proof
variable{G:Ratio (mid N B) (mid P B)}
include p v
lemma pointM(F:Finset (Kite S r))(W:ι→ Arch G e)(T:ι→ Ids ϰ)(V:ι→ Arch G e)(m h:ℕ)(H:Ride S)(pV: Measurable V)(pT:Measurable T)(hP:∀ x:ι,CrownB G S e (W x) (V x) m H)(hv:∀ x:ι,HullK S h F (W x).val.1.1 (W x).val.2 e)(t':∀ i∈F,halo m (Eire.frameP S i)⊆ Stilo.bay H) : Measurable fun i:ι=> Eire.paint S h U Y (W i).val.1.1 (W i).val.2 (T i) F (walksK (T i)):=by -- k clashes with order.H support.change m
 refine atlas_m _ (fun i j=> Eire.paint S h U Y (W i).val.1.1 (W i).val.2 (T i) F j) (walks_m.comp pT) ?_
 intro Z; induction Z with| nil=> exact measurable_const| cons x y ih=>
  simp_rw [Eire.paint]; apply Measurable.mul _ ih; unfold rankG; split; swap; · exact measurable_const
  refine Finset.measurable_sum _ fun j u=>?_
 -- tune induction layout
  let L:= j.2.1 ∪ j.2.2; let Ξ:= danceL S j.1.val r; let Bw(i:ι):= Eire.printG S h (W i).val.1.1 (W i).val.2 (clipM S F y) j.1
  let C (i:ι): Castle P B e Ξ:= ⟨Bw i,pays_l S h _ _ F (hv i) _ inter_subset_left j.1 (mem_image_of_mem _ (mem_filter.mp u).1)⟩ -- B shadow
  have hx:halo m (hatY S L)⊆Stilo.bay H:=(chilling le_rfl (show (hatY S L)⊆ Eire.frameP S j from by refine Subset.trans (image_subset_image ?_) subset_union_right; rw [union_assoc]; exact subset_union_right)).trans (t' j (mem_filter.mp u).1)
  rw [show (fun i:ι=>postM S h U Y (W i).val.1.1 (W i).val.2 (T i) (clipM S F y) j)=(fun i=> Scion.stock e Ξ Y U (C i) (T i) j.2) from funext fun i=> dif_pos (C i).property]
  refine lawn_m j.1 v p C T j.2 ?_ pT; intro x1 j' u; let p':Measurable fun i=>(V i).val:=measurable_subtype_coe.comp pV
  have a : j'.1∈ L:=u (mem_insert_self ..); have b : _+Lattice.step j'.2∈ L:=u (mem_insert_of_mem (mem_singleton_self _)); have hg(F':Finset (Hos S r)):Measurable fun i=> valve S (W i).val.1.1 (W i).val.2 F' h j':=by
    unfold valve; split
    · rw [funext (fun i:ι=> ((hP i).hears L hx).2.2 j' a b)]; exact (measurable_pi_apply j').comp p'.snd
    rw [funext (fun i:ι=> ((hP i).hears L hx).1 j' a b)]; exact (measurable_pi_apply j').comp p'.fst.fst
  cases x1<;> exact hg _
end
end YM.CF.Oise

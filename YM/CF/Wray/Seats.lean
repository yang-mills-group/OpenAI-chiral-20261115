import YM.CF.Wray.Shop
import YM.CF.Wray.Tree
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Wray
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Iva Eire Font Push.AbsoluteSums.Footprint
local notation "VF"=> Sat S
local notation "dS"=>Site (Domain N B)
local notation "bS"=> Bond (Domain P B)
abbrev roost (i: Sat S): Site (Domain N B):= match i with
| .inl i=> S.ratio.parent i.1
| .inr (.inl j)=> j.1
| .inr (.inr i)=> S.ratio.parent i.1
-- width relative.L footprint
lemma domeB(i: Sat S)(n:ℕ): (domeQ n i).val ⊆ halo (n+3) {roost i}:=by
 have ht(i:Site (Domain P B))(j)(p:separation i j≤ 2):separation (S.ratio.parent i) (S.ratio.parent j) ≤ 3:= (Nat.le_of_mul_le_mul_left ((Corona.foreshorten S.ratio i j).trans (show separation i j+S.ratio.count.val≤S.ratio.count.val*3 by have h:0 < S.ratio.count.val:=S.ratio.count.property; omega)) S.ratio.count.property)
 have hk{u:dS}{Y:Support (Domain N B)}(p:∀ i∈Y,separation u i ≤ 3): halo n Y⊆halo (n+3) {u}:=by intro z h; obtain ⟨u',v,t⟩:=halo_spec.mp h; exact halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle u u' z).trans (by have hp:= p u' v; omega)⟩ -- tune
 rcases i with i|i|i
 · apply hk; intro j p; obtain ⟨l,h,rfl⟩:= mem_image.mp p; exact ht _ _ (Work.E01.sep_touched i _ h)
 · apply hk; intro j p; rcases mem_insert.mp p with p|p; exact p ▸ (separation_self _).le.trans (Nat.zero_le _); rw [mem_singleton.mp p]; exact (Work.E01.sep_step_le ..).trans (by omega)
 apply hk; intro j p; obtain ⟨a,v,rfl⟩:= mem_image.mp p; refine ht _ _ ?_; rcases mem_insert.mp v with v|v; · rw [v,separation_self]; decide
 rw [mem_singleton.mp v]; exact (Work.E01.sep_step_le ..).trans (by omega)
lemma uprise{U:Muster G S x d T}(i: Sat S)(n:ℕ): (vast (k:=n) U (.inl i)).val ⊆ halo ((U.loft+U.post+200)*radiusB x+24) {roost i}:= by
 intro j p; let K:= (U.loft+U.post+200)*radiusB x; change j∈ halo 20 (halo 1 (domeQ K i).val) at p; obtain ⟨a,t,h⟩:=halo_spec.mp p; obtain ⟨l,w,z⟩:= halo_spec.mp t; obtain ⟨g,u,v⟩:=halo_spec.mp (domeB i _ w); have hp:= separation_triangle l a j; exact halo_spec.mpr ⟨g,u,(separation_triangle g l j).trans (by change _≤ K+24; omega)⟩
abbrev seatL (P:Patch):= P.L.val^4* Fintype.card PlaqAxes+(Fintype.card Axis+P.L.val^4*Fintype.card Axis)
lemma pile(V: Support (Domain N B)): ((univ:Finset (Sat S)).filter fun i=> roost i∈V).card ≤ V.card*seatL S.patch:=by
 let p:= univ.filter fun i=> S.ratio.parent i∈V; let L:=V ×ˢ (univ:Finset Axis); let D:= p ×ˢ (univ : Finset Axis); let F:= p ×ˢ (univ:Finset PlaqAxes); have he:p.card ≤ V.card*S.patch.L.val^4:= crowd _ _
 have hh: ((univ:Finset (Sat S)).filter fun i=> roost i∈V)= F.disjSum (L.disjSum D):=by ext i; rcases i with i|i|i ; all_goals simp [F,L,D,p,roost]; -- tune Lattice.Face.P
 rw [hh, card_disjSum,card_disjSum]; unfold F L D seatL; simp_rw [card_product,card_univ, mul_add,←mul_assoc]; gcongr
abbrev vision(b:ℕ)(i: VF): Finset (Bond (Domain P B)):= univ.filter fun j=> Next.SectorChange.points S j⊆ (domeQ b i).val
lemma puff_v(n:ℕ)(i: VF): (vision n i).card ≤ ratioB S (n+3):=by
 apply le_trans _ (Muster.iconic (roost i) (n+3)); apply card_le_card; intro j t; have h:S.ratio.parent j.1∈(domeQ n i).val:= (mem_filter.mp t).2 (Set.mem_insert ..); obtain ⟨z,v,p⟩:= halo_spec.mp (domeB i n h); exact mem_filter.mpr ⟨mem_univ _,((mem_singleton.mp v) ▸ p)⟩ -- tune
abbrev spanI(P: Patch)(n:ℕ):=((n+n+7)^4*seatL P)+1
lemma scoop(j:bS)(n:ℕ): ((univ:Finset VF).filter (fun i=> j∈vision n i)).card ≤ spanI S.patch n:=by
 let z:= S.ratio.parent j.1; let V:= halo (n+3) {z}; have hx: V.card ≤ (n+n+7)^4:= (Corona.halo_size {z} (n+3)).trans_eq (by rw [card_singleton,one_mul]; ring) -- V target unknown
 apply le_trans _ ((pile (S:=S) V).trans ((Nat.mul_le_mul_right _ hx).trans (by unfold spanI; omega : (n+n+7)^4*seatL S.patch ≤ spanI S.patch n)))
 apply card_le_card; intro i v; have h:z∈ (domeQ n i).val:= (mem_filter.mp ((mem_filter.mp v).2)).2 (Set.mem_insert ..); obtain ⟨u,p,y⟩:= halo_spec.mp (domeB i n h); exact mem_filter.mpr ⟨mem_univ _,halo_spec.mpr ⟨_,mem_singleton_self z, (by rw [separation_comm,←mem_singleton.mp p]; exact y)⟩⟩
lemma pulseS {y:Directions SU.group (Domain P B)}{ρ:ℝ}{L: Finset (Sat S)}(u:0 ≤ ρ)(h:∀ i∈L,Bravo n i y ρ): let Y:=vision (S:=S) n; ρ^2*L.card ≤ spanI S.patch n * ∑ i∈ L.biUnion Y,‖y i‖^2:=by
 intro Y; let f(i:bS):= ‖y i‖^2; have hf(i:bS):0 ≤ f i:=sq_nonneg _; let V:= L.biUnion Y
 have hp(i:VF)(v:i∈L): ρ^2≤ ∑ j∈Y i,f j:=by obtain ⟨j,t,w⟩:=h i v; have hh:j∈Y i:= mem_filter.mpr ⟨mem_univ _,t⟩; exact (pow_le_pow_left₀ u w.le _).trans (single_le_sum (fun j _=>hf j) hh)
 have he:(∑ i∈L,(ρ^2:ℝ))=ρ^2*L.card:=by simp [mul_comm]
 rw [← he]; apply le_trans (sum_le_sum hp); rw [sum_congr rfl (g:=fun i=> ∑ j∈V, if j∈ Y i then f j else 0) ?_, sum_comm,mul_sum]; swap; · intro i v; rw [←sum_filter,filter_mem_eq_inter, inter_eq_right.mpr (fun i' w=>mem_biUnion.mpr ⟨i,v,w⟩)]
 apply sum_le_sum; intro i _; rw [←sum_filter, sum_const]; simp only [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ((card_le_card (filter_subset_filter _ (subset_univ _))).trans (scoop (S:=S) i n))) (hf i)
end YM.CF.Wray

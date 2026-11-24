import YM.CF.Oise.Epoch
import YM.CF.Nor.Nas
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade
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
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
variable{r:ℕ}
local notation "XK"=> (Kite S r)
local notation "Q"=> liftK (r:=r) S
open Plume
lemma lit_g(A:Ids (mid P B))(C:Finset (Kite S r)) : ∃ L':List (Kite S r),L'.Nodup ∧ L'.toFinset=C ∧ (pureK S C→(walksK A).filter (fun j=>j∈ Q C)=L'.map Prod.fst):=by
 by_cases h:pureK S C; swap; · exact ⟨C.toList,C.nodup_toList,by simp,fun p=>(h p).elim⟩
 let L:List (Hos S r):=(walksK A).filter (fun j=> j∈ Q C); have he(i:Hos S r): i∈L↔i∈Q C:=by simp [L,Plume.walksK]
 have hp(i:Hos S r)(p:i∈L): ∃ j:Support (Domain P B)×Support (Domain P B), (i,j)∈C:=by obtain ⟨j,l,x⟩:=mem_image.mp ((he i).mp p); exact ⟨j.2,x ▸ l⟩ -- cast dependent?
 classical
 choose! d D using hp
 let Y(i:Hos S r):= ((i,d i):Kite S r)
 refine ⟨L.map Y,List.Nodup.map (fun _ _ p=>congrArg Prod.fst p) (((Plume.scoreQ _).1).filter _), ?_,fun _=> ?_⟩ -- tune Implicit
 · apply Finset.ext; intro i; rw [List.mem_toFinset,List.mem_map]; constructor
   · intro ⟨a',v,x⟩; exact x ▸ (show Y a'∈ C from D a' v)
   intro p; have hv:= (he i.1).mpr (mem_image_of_mem _ p); exact ⟨i.1,hv, proud_p S C h (D i.1 hv) p rfl⟩
 simp [Y,L,Function.comp_def]
lemma weave_a(A:Ids (mid P B))(i:Troupe S r (Words S)):∃ (J:List (Kite S r))(K': List (Rust (mid P B)))(L': List (Words S)),J.Nodup∧ K'.Nodup ∧ L'.Nodup∧(weave_g J K' L').toFinset=i∧(pureK S J.toFinset → (walksK A).filter (fun j=>j∈ liftK S J.toFinset)=J.map Prod.fst):=by
 obtain ⟨L,p,v,h⟩:=lit_g A i.toLeft; let A':=i.toRight.toLeft; let Z:=i.toRight.toRight
 refine ⟨L,A'.toList,Z.toList,p,A'.nodup_toList,Z.nodup_toList,?_,by rw [v]; exact h⟩
 ext j; rcases j with i' |j'|j' -- let syntax
 · rw [←mem_toLeft,left_i, v,mem_toLeft];
 · rw [←mem_toRight,←mem_toLeft,left_v]; simp [A']
 rw [←mem_toRight,←mem_toRight,right_v]; simp [Z]
lemma weave_u (J:List XK)(K': List (Rust (mid P B)))(L':List (Words S))(p:J.Nodup)(h:K'.Nodup)(v:L'.Nodup): (weave_g J K' L').Nodup:=by
 rw [←Multiset.coe_nodup]; refine Multiset.toFinset_card_eq_card_iff_nodup.mp ?_; let N:=weave_g J K' L'; change (weave_g J K' L').toFinset.card=N.length; rw [←card_toLeft_add_card_toRight,left_i,List.toFinset_card_of_nodup p,←card_toLeft_add_card_toRight, left_v,right_v,List.toFinset_card_of_nodup h,List.toFinset_card_of_nodup v]; simp [N,weave_g]
-- palettes profile as finite subtype.Range actually.
local notation "A0"=> Ids (mid P B)
local notation "CK"=> (Hos S r→Sweep (mid P B))
def arcX (A:A0): CK × List (Hos S r):=(fun i=>Hive.chip (danceL S i.val r) A,walksK A)
-- note tuple parser.
abbrev sparksT(A:Sweep N):=A
abbrev Sil (S:StepData (Domain N B) (Domain P B))(r:ℕ):= Set.range (@arcX N P B S r)
local notation "Φ"=> (Sil S r)
local instance :MeasurableSpace (List (Hos S r)):= ⊤
local instance :MeasurableSingletonClass (List (Hos S r)):=⟨fun _=> trivial⟩
def era (A:A0):↥(Sil S r):=⟨arcX A,⟨A,rfl⟩⟩
lemma sill_m : Measurable (@era N P B S r):=by
 apply Measurable.subtype_mk; exact Measurable.prodMk (measurable_pi_lambda _ fun i=> Oise.chip_m _) Oise.walks_m
lemma sill_p: (Φ:Set _).Finite:=by
 let X:= (univ:Finset (Hos S r)).toList; apply Set.Finite.subset (Set.finite_univ (α:=CK)|>.prod X.permutations.toFinset.finite_toSet) -- tune available
 intro i h; obtain ⟨y,rfl⟩:=h; exact ⟨Set.mem_univ _,List.mem_toFinset.mpr (List.mem_permutations.mpr (List.perm_of_nodup_nodup_toFinset_eq (scoreQ ..).1 (nodup_toList ..) (show (Plume.walksK y).toFinset=X.toFinset from by simp [X,Plume.walksK])))⟩
-- picks sensor lives on range
local notation "dN"=> Directions SU.group (Domain P B)
def news(z:dN)(k:ℕ)(b:ℝ): Finset (Sat S):= univ.filter (fun i=> Bravo k i z b)
lemma news_p (z:dN)(k:ℕ)(b:ℝ)(i:Sat S): i∈news z k b↔ Bravo k i z b:=by simp [news]
local instance : MeasurableSpace (Finset (Sat S)):= ⊤
local instance : MeasurableSingletonClass (Finset (Sat S)):=⟨fun _=>trivial⟩
lemma talks_m(k:ℕ)(b:ℝ): Measurable (fun z:dN=> news (S:=S) z k b):=by
 apply measurable_to_countable; intro s; let Pp:=news (S:=S) s k b
 change MeasurableSet {z:dN|news z k b=Pp}; simp_rw [Finset.ext_iff,news_p]; -- iff may rw P as abbreviation
 simp_rw [Set.setOf_forall]; apply MeasurableSet.iInter; intro i; have he:MeasurableSet {z:dN|Bravo k i z b}:=by simpa [palmB] using (plumX (n:=k) b ({i}:Finset (Sat S))).measurableSet
 by_cases u:i∈Pp; · simpa [u] using he
 simp_rw [iff_false_intro u, iff_false]; exact he.compl
end YM.CF.Jade

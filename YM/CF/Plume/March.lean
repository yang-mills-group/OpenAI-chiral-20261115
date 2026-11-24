import YM.CF.Plume.Nex
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Plume
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B))(x:ℝ)
local notation "G₀"=> SU.group
local notation "n₀"=> (Domain N B)
local notation "m₀"=> (Domain P B)
local notation "Tabs"=>Arena.Tab S
variable{S}
open scoped Classical ENNReal NNReal
open Girt Next.Fluctuations.Sector Dial
open Lich
-- active Modes: for Shape Y plan agreement full on X.
variable{k b l k1 k' o₁ o₂ r r' j:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]
local notation "bay"=> Stilo.bay
variable {X: Support (Domain N B)}{H H':Ride S}
variable{G:Ratio (mid N B) (mid P B)}{e:ℝ}{Q:GramM (mid P B)}
set_option pp.universes false
variable {V V':Orbit (mid N B)}{y y':Cord S}{K K':Ids (mid P B)}
lemma sail (h:Spark X y y')(p:Agrees X V.1 V'.1)(A:Stores S): let M:=cort V.1 y; let N:= cort V'.1 y'; Forge.Duo SU.group S (Eire.trot S M A) (Eire.trot S N A) X:= by
 intro U N; exact ⟨⟨fun _ _=> Iff.rfl,h.sharesB.site,fun i p=>h.sharesB.edge _ (p (mem_insert_self ..)),KinT h.sharesB,p,fun i p=>(h.sharesE _ (p (Set.mem_insert ..))).1,fun i p=>(h.sharesE _ (p (Set.mem_insert ..))).2⟩,fun _ _=> Iff.rfl,fun _ _=>Iff.rfl, fun _ _=>Iff.rfl⟩
-- no need filters agree F tab on Y
variable {X0:ι→Palot.leaf (Site (Domain N B))}{i:Troupe S r ι}{t:ℝ}
local notation "U₀"=> cort V.1 y
local notation "U'"=> cort V'.1 y'
local notation "AX"=> BranchX S X0 k
variable (h:Spark (Stilo.bay H) y y')(p:Palot.fits (BranchX S X0 k) i H)
include h p
lemma porous : brushK (penn S i) (chillB U₀) t= brushK (penn S i) (chillB U') t:=by
 let A:=penn S i; let K:=bay H; have ht(Y: Kite S r)(v:Y∈ i.toLeft): Y.1.val.place ⊆ K:= (halo_subset _ _).trans (litG S X0 p _ v)
 have he(j)(z:j∈ A.costs):Finset.image S.ratio.parent (touched j) ⊆ K:=by
    unfold A penn at z; rw [costs_g] at z; obtain ⟨i',k,v⟩:= mem_biUnion.mp z; exact fun y t=> ht _ k (mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨_,v,t⟩))) -- tune
 unfold brushK; refine congrArg (fun s:Finset (Cell (Domain P B))=>s.biUnion touched) (Finset.filter_congr ?_); intro z u; rw [show toll (chillB U₀) z=toll (chillB U') z from ?_]; -- tactic
 apply congrArg SU.group.chord; apply travel_local; intro η t' _; have hq:=he z u (mem_image_of_mem S.ratio.parent (show η.1∈ touched z from List.mem_toFinset.mpr t')); unfold chillB; have hu: η∈(cort V.1 y).park.trunks↔η∈(cort V'.1 y').park.trunks:= KinT h.sharesB η hq; simp only [hu]; exact congrArg (fun z:SU.E => if η∈ (cort V'.1 y').park.trunks then 1 else z) (h.sharesE η hq).1 -- forall congr syntax
lemma earned : Eire.earn S (chillB U₀) t i↔Eire.earn S (chillB U') t i:=by unfold Eire.earn; simp only [porous (V:=V) (V':=V') (t:=t) h p]
lemma beardX(Z: Rust (mid P B))(u:Z∈i.toRight.toLeft): Set.EqOn y.2.2 y'.2.2 ((rustL _ Z).val.2):=fun j v=> h.sharesL j ((mem_filter.mp (litF S X0 p _ u v)).2)
lemma beardL : Set.EqOn y.2.2 y'.2.2 (Passage S (bay H)):= fun j v=>h.sharesL j (mem_filter.mp v).2
omit h p
variable {D n l:ℕ}
lemma ca_l (f:Meter TailB G e)(F:Meter Grave G e)(h:ReefT G e f F)(v v':Rill.Arch G e)(u: 0 < e)(p:CrownB G S e v v' k H)(pH: H'≤ H)(T: FC (Single (mid P B)))(X:FC (LeanV (Single (mid P B))))(w:Odd G.count.val)(lip:Pitch bell (lipF (mintK S H')) n T)(hP:Pitch put (lipV (mintK S H')) D X): issue (cala G S w e u f F v k H') X T=issue (cala G S w e u f F v' k H') X T:=by
 apply paid_u _ _ hP lip
 · intro j v; have hp:= drift_l G S w e u f F _ _ _ h (show Disjoint (bay H) (bay (⊥:Ride S)) by simp [bayB]) (show H'≤ H ⊔ ⊥ from pH.trans le_sup_left) p _ (bay_m pH v); rwa [inf_eq_left.mpr pH] at hp
 intro k v j q; have hp:= drift_r G S w e u f F _ _ _ h (show Disjoint (bay H) (bay (⊥:Ride S)) by simp [bayB]) (show H'≤ H ⊔ ⊥ from pH.trans le_sup_left) p _ j (bay_m pH v); rwa [inf_eq_left.mpr pH] at hp
lemma knot_s (A: Dress G S e r k' U₀ Q k X0)(B':Dress G S e r k' U' Q k X0)(hp:CrownB G S e (A.coats i) (B'.coats i) k H)(h:A.portT=B'.portT)(t:A.portG=B'.portG)(hx:A.songP i=B'.songP i)(hv:A.brew i=B'.brew i)(hy:A.bodyL x l i=B'.bodyL x l i): Scion.vigor (A.stageT x l i) H=Scion.vigor (B'.stageT x l i) H:=by
 have he(j:Ride S)(v:j≤H): Scion.vig (A.stageT x l i) j=Scion.vig (B'.stageT x l i) j:=by
    apply Subtype.ext; change Scion.tempo _ j=Scion.tempo _ j; unfold Scion.tempo; by_cases t': Scion.cluster AX i ≤ j; swap; · rw [if_neg t',if_neg t']
    rw [if_pos t', if_pos t']; change issue (A.heatT i j) (A.bodyL x l i).val (A.songP i)*(A.brew i).val=issue (B'.heatT i j) (B'.bodyL x l i).val (B'.songP i)*(B'.brew i).val
    rw [←hy,←hx,←hv]; let C:= (A.brew i).val; refine congrArg (fun x:FC (LeanV _)=>x*C) ?_; unfold Dress.heatT; rw [←h,←t]; apply ca_l _ _ A.guardP (A.coats i) _ _ hp v (A.songP i) _ _ (n:=0) (D:=0) ((A.stageT x l i).capP _ t') ((A.stageT x l i).forP _ t') -- tune
 let X:=Scion.vig (A.stageT x l i); let Y:=Scion.vig (B'.stageT x l i); apply Stilo.proves; intro j v; exact (recon X j).trans ((he j v).trans (recon Y j).symm)
end YM.CF.Plume

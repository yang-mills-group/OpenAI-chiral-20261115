import YM.CF.Yaw.Marks
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Yaw
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Eire Jet Scroll Push.AbsoluteSums.Trees PetalP
variable {I N P B:Side}(S:StepData (Domain N B) (Domain P B)) (G:Ratio (mid N B) (mid P B)){r d k l D:ℕ}
open Rush Scroll Paige Vault Phase Acorn Spire
variable {ι:Type}[Fintype ι][DecidableEq ι](X:ι→ Palot.leaf (Site (Domain N B)))
local notation "m"=> mid P B
local notation "V'"=> Domain P B
local notation "H_"=> Eire.Ride S
local notation "S_"=> Eire.Folk S r ι
local notation "τ"=> Oboe (Single (mid P B))
local notation "χ"=> (LeanV (Single (mid P B)))
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable{S G}
variable (L:List (Kite S r))(U:List (Rust (mid P B)))(W:List ι)
local notation "Z'"=> weave_g L U W
open Eire Dress
variable {e A Q:ℝ}(R:GramM (mid P B))(M:E→Monk SU.group S)(T: ∀ i:E, Dress G S e r D (M i) R k X)
abbrev stems(Y:Kite S r)(D':List (Kite S r))(i:E): FC (Single (mid P B)):= let Q:= (T i).coats (weave_g L U W).toFinset; rankG S D (T i).pens (T i).dyes Q.val.1.1 Q.val.2 (T i).cloth L.toFinset (D'.map Prod.fst) Y.1
abbrev feral (C: Kite S r→ PetalP τ):Folk S r ι→ PetalP τ:=Sum.elim C (fun _=>PetalP.bud _)
-- use induction building receipt primitive across 
variable {t:E}{s:ℕ}(C:Kite S r→PetalP (Oboe (Single (mid P B)))) -- note D k
local notation "κ_"=> (Z').toFinset
local notation "Iu"=> (PetalP.bud (Oboe (Single (mid P B))))
lemma song_v (p:∀ᶠ i in 𝓝 t,(T i).wager.filter (fun x=> x∈ liftK S L.toFinset)=L.map Prod.fst)(h:∀ j∈L,∀ Y:List (Kite S r),Y.Sublist L→Meant t s (C j) bell (stems X L U W R M T j Y)):Meant t s (PetalP.Ribbon (weave_g L U W) (feral C)) bell (fun i=> (T i).songP (Z').toFinset):=by
 let F:=L.toFinset; let V(i):= (T i).coats (Z').toFinset; let B'(i):=(V i).val.1.1; let X':= fun (i:E)=>(V i).val.2; let Y'(l:List (Hos S r))(i:E):= Eire.paint S D (T i).pens (T i).dyes (B' i) (X' i) (T i).cloth F l
 let a(i):= (T i).wager; have hp': ∀ᶠ i in 𝓝 t,Y' (L.map Prod.fst) i=(T i).songP (Z').toFinset:=by
    filter_upwards [p] with i p' ; unfold songP; rw [left_i]; let x:=a i; unfold Y'; rw [←p']; exact jug S D (T i).pens (T i).dyes (B' i) (X' i) (T i).cloth L.toFinset (T i).wager
 apply Meant.germ _ hp'; suffices L':∀ l:List (Kite S r), l.Sublist L→Meant t s (PetalP.Ribbon (weave_g l U W) (feral C)) bell (Y' (l.map Prod.fst)) from L' L (.refl _)
 intro l; induction l with
 | nil=>
   intro _ ; suffices h:∀ J:List (Rust (mid P B) ⊕ ι), Meant t s (PetalP.Ribbon (J.map Sum.inr) (feral C)) bell (1:E→ FC (Single (mid P B))) by
      have ht':=(h (U.map Sum.inl ++ W.map Sum.inr)); rw [List.map_append, List.map_map,List.map_map] at ht'; exact ht'
   intro J; induction J with | nil=> exact singletonK .. | cons i J l => exact (((singletonK _ bell t).join_k l).germ (Eventually.of_forall (fun i: E=>show (1:FC (Single (mid P B)))*1=1 from mul_one _))) -- tune equiv
 | cons j V ih=>
    intro L'; let x:=T; exact (h j (L'.subset (List.mem_cons_self ..)) V ((List.sublist_cons_self ..).trans L')).join_k (ih ((List.sublist_cons_self ..).trans L'))
end YM.CF.Yaw

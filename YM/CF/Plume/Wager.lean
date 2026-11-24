import YM.CF.Plume.March

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
section order
-- ex ante order from finest ids. Restriction order unaffected by other data even when ties; later ties null. min of passage of stem.
variable {E:Type*}[DecidableEq E][Fintype E]
def sue(a:E→ℝ)(i:E): Lex (ℝ× Fin (Fintype.card E)):= toLex (a i,(Fintype.equivFin E) i)
abbrev suitsG (a:E→ℝ)(i j:E):Prop:= sue a i ≤ sue a j
instance (a:E→ℝ):IsTrans E (suitsG a):=⟨fun _ _ _ => le_trans⟩
instance (a:E→ℝ):Std.Antisymm (suitsG a):= ⟨fun i j p t=>(Fintype.equivFin E).injective (congrArg (fun i: Lex (ℝ × Fin (Fintype.card E))=> (ofLex i).2) (le_antisymm p t))⟩
instance(a:E→ℝ): Std.Total (suitsG a):=⟨fun _ _=> le_total ..⟩
lemma rail_p(V U:E→ℝ)(X: Finset E)(t:Set.EqOn V U X):(univ.sort (suitsG U)).filter (fun i=>i∈X)=X.sort (suitsG V):=by
 let H:= (univ.sort (suitsG U)).filter (fun i=> i∈X); let L:= X.sort (suitsG V); have hf:H.Pairwise (suitsG U):=(pairwise_sort ..).filter _; have ht:H.toFinset=X:=by ext; simp [H]; -- tune
 have hp : H.Pairwise (suitsG V):=hf.imp_of_mem (fun {i j} u v p=>by
    have hz:∀ j∈H,sue V j=sue U j:=fun l k=> congrArg (fun z:ℝ=> (toLex (z,(Fintype.equivFin E) l))) (t (show l∈X from ht ▸ (List.mem_toFinset.mpr k : l∈H.toFinset))); unfold suitsG; rw [hz _ u,hz _ v]; exact p)
 exact List.Perm.eq_of_pairwise' hp (pairwise_sort ..) (List.perm_of_nodup_nodup_toFinset_eq ((sort_nodup ..).filter _) (sort_nodup ..) (ht.trans (sort_toFinset ..).symm)) -- tune
end order
def deed(A:Ids (mid P B))(O:Hos S r):= let X:= Passage S (stem S O); priorP A (greet X (priorP A))
def walksK(A:Ids (mid P B)):= (univ:Finset (Hos S r)).sort (suitsG (deed A))
lemma scoreQ(A:Ids (mid P B)): (walksK (S:=S) (r:=r) A).Nodup ∧∀ i:Hos S r,i∈ walksK A:=⟨sort_nodup ..,fun i=>by simp [walksK]⟩
lemma sureD(A B':Ids (mid P B))(O:Hos S r)(h:Set.EqOn A B' (Passage S (stem S O))): deed A O= deed B' O:=by
 have ht:(Passage S (stem S O)).Nonempty:=by obtain ⟨y,u⟩:=stem_p S O; exact ⟨S.ratio.embed y, mem_filter.mpr ⟨mem_univ _,by rw [Ratio.embed_parent]; exact u⟩⟩
 have hg:Set.EqOn (priorP A) (priorP B') (Passage S (stem S O)):=fun i p=>congrArg Prod.fst (h p); dsimp only [deed]; rw [mastL _ _ _ hg]; exact hg (mastP _ ht _).1
lemma sail_s(A B':Ids (mid P B))(V: Finset (Hos S r))(h:∀ i∈V,Set.EqOn A B' (Passage S (stem S i))):(walksK A).filter (fun i=>i∈V)=(walksK B').filter (fun i=> i∈ V):=by rw [walksK,rail_p (deed A) _ _ (fun _ _=>rfl),walksK,rail_p (deed A) _ _ (fun i p=>sureD A B' i (h i p))]
end YM.CF.Plume

import YM.CF.Fief.Torus
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Jet Push.AbsoluteSums
local notation "G₅"=> SU.group
variable {c f n N X B:Side}{S:StepData (Domain N B) (Domain X B)}{G:Ratio (mid N B) (mid X B)}{a b e C H D:ℝ}{k l j:ℕ}
open Lich.Muster Font
attribute [local instance] opCStarAlgebra
local notation "η"=> Domain N B
local notation "mX"=>Domain X B
variable (k) {M:Male} {K D v x:ℝ}
variable (G)
variable {x:ℝ}
variable(T:Tube SU.group S)(A: Lich.Muster G S x e T)
variable (W:mSeal X B→ℝ)(P:mSeal X B→ Toll (Single (mid N B)))
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {F:Haze N X B G e}{Y: Msca N X B G e}
variable (Q:E→ Rent0 G e){r m':ℕ}(r k:ℕ)(y:E)
abbrev potR(L:Bit (Site (Domain N B))):= ∑ i∈ Lich.Muster.queen (S:=S) (x:=x) r L,2*W i
abbrev potQ(L:Bit (Site (Domain N B)))(u i:Single (mid N B)):= ∑ v∈ Lich.Muster.queen (S:=S) (x:=x) r L,P v u i
-- per Pose.Π budget legS/A actual.Ph. measure.Post.G.From.Crew.Holder
structure ReadK (P:Bit (Site (Domain N B))):Prop where
 moon : b<e
 heart: JointB G (Q y).val b
 tone Z: Lattice.halo r (hatY S Z)⊆ P.val → (∀ j:Bond (Domain X B),Skye.ends j⊆Z→Allows k (fun v=> SU.fund ((Q v).val.1 j)) y 1) ∧(∀ j:Bond (Domain N B),Skye.ends j⊆ cloudG G Z→Allows k (fun v=>SU.fund ((Q v).val.2 j)) y 1)
variable{H H':ℝ}
lemma cache_l (p:∀ i,Flash (dressL G e) (LineE k G C e) k i (A.LawQ i) (W i))(h:∀ i,Filer G i (P i) D k (A.Fame i))(hp:1<C)(ht:1<D)(L:Bit (Site (Domain N B)))(v:ReadK G Q (S:=S) r k y (b:=b) L) (u:E→ Monk SU.group S)
 (w:Allows k (fun v=>Lich.Muster.massX A (u v) L) y H)(hw:Allows k (fun v=>Lich.Muster.shardy A (u v) r L) y H') :
 Allows k (fun t=> legS A (u t) (Q t) r L) y (H+H'+potR (S:=S) (x:=x) W r L)∧ (∀ i j': Single (mid N B),Allows k (fun t=> legA A (Q t) r L i j') y (potQ (x:=x) (S:=S) P r L i j')):=by
 constructor
 · have hl: Allows k (fun t=> ((massX A (u t) L+ shardy A (u t) r L:ℝ):ℂ)) y (H+H'):= ((w.add hw).linear Complex.ofRealCLM (show ‖Complex.ofRealCLM‖≤1 by simp)).mono (by rw [one_mul])
   refine hl.add (Jet.allows_sum (fun i hp'=>?_)); obtain ⟨g,z⟩:= v.tone i (subset_of_eq ((mem_filter.mp hp').2)); exact (subtract_p (Jet.allows_const y ((p i).sumline _)) (riseP k Q (A.LawQ i) (p i).plot (p i).reads v.moon hp v.heart g z)).mono (le_of_eq (two_mul _).symm)
 intro i j; simp_rw [legA,Matrix.sum_apply]; refine Jet.allows_sum fun i' hp=> ?_; obtain ⟨g,z⟩:= v.tone i' (subset_of_eq (mem_filter.mp hp).2); exact riseP k Q (fun x=>A.Fame i' x i j) ((h i').folk i j) (fun a b t=>congrArg (fun H:Op (Single (mid N B))=> H i j) ((h i').reads _ _ t)) v.moon ht v.heart g z -- tune order
end YM.CF.Fief

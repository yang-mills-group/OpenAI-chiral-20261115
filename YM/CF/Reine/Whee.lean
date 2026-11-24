import YM.CF.Reine.Crown
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Reine
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti Cay Slate Forge Bloch Exterior
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {s:Signed}
section
open scoped Classical
-- kernel comparison on coarse config in one frame channel
local notation "B₀"=>radiusB x
local notation "r₀"=>Stores.till x
local notation "t₀"=>fiery G x S.patch.L
local notation "E₀"=>temp x
open Vol
open Atala
lemma totalX (j:ℕ) (i:Site c): i∈A.dome r ↔∃ t∈blip S A j,i ∈t.val.dome r:=by
 constructor; intro p; obtain ⟨z,h,p⟩:=halo_spec.mp p; rw [← bloomE S A j] at h; obtain ⟨k,h,w⟩:=mem_biUnion.mp h; exact ⟨k,h,halo_spec.mpr ⟨z,w,p⟩⟩
 rintro ⟨k,t,p⟩; exact (pack S k t).inside r p
lemma hop_x(A:Stores S)(s:Signed)(D:ℕ): tie (anchorage (turnStore s A) D)= univ.filter fun i=> orientZ S s i∈A.dome D :=by
 ext i : 1; rcases i with i|i|i|i <;> simp [orientZ,tie,anchorage,dome_turn]
variable (x:ℝ)(s:Signed)(A:Stores S)
def lyn (j:ℕ):Finset (Site f⊕ Site c):=univ.filter fun i=> herald S s (.inr i)∈ A.dome (j*radiusB x)
def strum (j:ℕ):Finset (Along S):= univ.filter fun i=> herald S s i∈A.dome (j*radiusB x)
lemma strum_eq(j:ℕ): strum x s A j=(tie (whim x j A s)).disjSum (lyn x s A j):=by unfold whim; rw [hop_x]; ext i : 1; cases i <;> simp [strum,lyn,herald]
lemma rush_eq(j:ℕ): rush x A s j=(strum x s A j)ᶜ:=by ext i : 1; simp [rush,strum]
lemma seed_B {j:ℕ}(h:j*radiusB x ≤ r): Set.PairwiseDisjoint ((blip S A r):Set (Hos S r)) (fun O=>strum x s O.val j):=by
 intro i t k v g; refine Finset.disjoint_left.mpr fun l p u=> Finset.disjoint_left.mp (stem_d S A t v g) ((Corona.halo_mono h (Finset.Subset.refl _)) (mem_filter.mp p).2) ((Corona.halo_mono h (Finset.Subset.refl _)) (mem_filter.mp u).2)
lemma seed_r(j r:ℕ): strum x s A j=(blip S A r).biUnion (fun O=> strum x s O.val j):=by ext i : 1; simp only [strum,Finset.mem_biUnion, mem_filter,mem_univ,true_and]; exact totalX r _
end
end YM.CF.Reine

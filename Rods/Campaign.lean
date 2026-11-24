import Rods.Links
import YM.SU5.FiniteGaugeData.Pannier.Sketch
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief VolumeRate
open Roots Buffered LocalLimit LocalLimit.Papal Dyad Dyad.Keeping Mew Compass Drift
attribute [-instance] instDecidableEqLex
set_option quotPrecheck false
open Buffered Advance Afterglow YM.CF.Pannier.Chancel
namespace Decaf
open Stencil Push.SectorMeasure Larch
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{e kL:ℝ}{B:Side}{P:Grasp V.U B e}{qχ:Chi}(A:SiteLedger V P kL qχ){φ:Vxpert V A}{D0 f v D Q U:ℕ}(J:PaperTrace V A f v φ D0)(S:Tickets V D0 D Q R.L A f v)(h:Margin R.L D0 D Q U)
variable(j r p:ℕ){G:Calibration}{m:Side}(u₁: U=G.ℓ)(hf:f≤ j)(hr:j≤r)(hv:r≤ v)(hp:22≤ p)(C D₁:ℕ→ℝ)(he:Scree.mid (A.side j) B=G.c m)
local notation "tK"=> sportT A h j r p u₁ J S h hf hr hv u₁ hp C D₁ he
local notation "Σs" k:max=>mid (A.side k) B
variable (l:List (Tix A j))
private lemma utter_sep{n m:Side}(e:n=m)(f w:Support (More n))(q:Disjoint (e ▸ f:Support (More m)) (e ▸ w:Support (More m))):Disjoint f w:=by subst m; exact q
include J S h u₁ hf hr hv hp
lemma spreadRoster(k:(A.gram j).p.B^3 + (A.gram j).p.B ≤ p/2)(q:Sport.race tK l): Very_Ψ (roster A j l) (A.gram j).p.B:=by
 let k':=(A.gram j).p.B; let w:=node ∘ roster A j l
 have ht(i j:Fin l.length)(k:i<j): p < separation (w i) (w j):=by
    have H:= List.pairwise_iff_get.mp q i j k
    have H1: Disjoint (sitepad ((l.get i).1) p) (sitepad (l.get j).1 p):= utter_sep he _ _ H
    by_contra! x; refine Finset.disjoint_left.mp H1 (?_:w j∈_) ?_
    · exact halo_spec.mpr ⟨w i,Finset.mem_singleton_self _,x⟩
    exact halo_spec.mpr ⟨_,Finset.mem_singleton_self _,(separation_self _).le.trans (Nat.zero_le _)⟩
 have hG(i j:Fin l.length)(e:i≠j): p < separation (w i) (w j):=by
   rcases e.lt_or_gt with u|v
   · exact ht _ _ u
   rw [separation_comm]; exact ht _ _ v
 have hx:Injective w:=fun i j e=> by by_contra y; have H:=hG i j y; rw [e,separation_self] at H; omega
 refine ⟨hx,fun i j e=>?_⟩; change k'^3+k'^3+k'+k'< separation (w _) (w _)
 have ht:=hG i j (fun v=> e (congrArg w v)); change k'^3+k'≤p/2 at k; omega
lemma sharpRace (A':Mark (Scree.mid (A.side v) B) →ℂ)(q:ℝ)
 (HR:∀ (I:Type)[LinearOrder I][Fintype I](o:I→Site (mid (A.side j) B))(l:List (PairKey I)),Very_Ψ o (A.gram j).p.B→(wrap0 l).Nodup→ ‖A' (braidP (Yz:=φ) (v:=v) V A j r o C D₁ l)‖≤q) (k:(A.gram j).p.B^3+(A.gram j).p.B≤ p/2)(q₁:Sport.race tK l): ‖A' (Sport.film tK l)‖ ≤ q:=by
 rw [links]; apply HR; exact spreadRoster A J S h j r p u₁ hf hr hv hp C D₁ he l k q₁; exact noDouble A j l
#print axioms sharpRace
end Decaf
end YM.CF.Py.Rate
end

import YM.CF.Tuft.Sheer
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Vow Larch
variable {I:Type*}[DecidableEq I](R:Finset I)(G:I→Scree.Hub n)(F U:I→InkD n)
local notation "Yx"=>sunY R G F
variable (Ψ:Sweep n→ Equiv.Perm I)(p:∀ (s:Sweep n) i,i∈R ↔ Ψ s i∈R)(hg:∀ (s:Sweep n) i,i ∈ R→G (Ψ s i) = moveHub s (G i))
variable (hv:∀ (s:Sweep n) i,i∈ R →∀ V:Pane n,U (Ψ s i) (flashA s V)=suit_Y s (U i V))(hF:∀ i∈R,∀ V:Pane n,deadP (F i V)=deadP (U i V))
include p hg hv hF
lemma sol_F: Sym_P (numbD (sunY R G F)):=by
 intro s; apply funext; intro i; apply funext; intro V; let Y:= flashA s V; let T:= Ψ s; let o:=moveHub s i
 change suit_Y s⁻¹ (deadP ((∑ x∈R with G x=o,F x) Y))=deadP ((∑ x∈R with G x=i,F x) V)
 simp only [Finset.sum_apply,darn_K,map_sum]; symm; refine sum_equiv T (fun j=> ?_) fun j t=>?_ ; · simp only [mem_filter]; refine ⟨fun h=>⟨(p ..).mp h.1, by unfold T; rw [hg s j h.1,h.2]⟩,fun ⟨u,v⟩=>?_⟩; have z:(G j=i):=(Ione.scope_q s).injective ((hg _ _ ((p ..).mpr u)).symm.trans v); exact ⟨(p ..).mpr u,z⟩
 let Z:=p s j; let x:= (mem_filter.mp t).1; rw [hF _ x,hF _ (Z.mp x), show U (T j) Y=_ from hv s _ x _,show deadP (suit_Y s _)= _ from dead_v ..,moon_Y,mul_inv_cancel,toon_Q]
end YM.CF.Ione

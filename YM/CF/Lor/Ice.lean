import YM.CF.Lor.Glyph
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
-- common allowance-target category.Across any Horizon.S.True.N.Anchor.g
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open Fief
-- exact ζ covariance anchored. ink(U tides) matters only fine.Agency; V terms cancel without SAP Smooth. 
variable(Q:Patch){S:StepData c f}(F:Tube G₅ S) (M: Monk SU.group S)(q:Chi)(n l:ℕ)(x v s β α L:ℝ)(Z: ChartRatio G₅)(i:Site c)(d:ℝ)
local notation "A"=> M.key
local notation "Λ"=> Directions SU.group c
local notation "m₀"=> M.zoo x
local notation "φ"=> Stores.till x
local notation "U"=> fun z:Λ=>M.atop z x
local notation "B"=> Cloak.bent F x M d l q v L
local notation "G"=> tape∘ B
local notation "W"=> repine F x M d l q v L
open Matrix
lemma belt_l (y:Λ)(t:ℝ)(hv:v≠0)(h:L≠0): B (y,t*coupling β*L/v)= ((rough M (t•M.z)).atop y x).fuel x F q d l β:=by
 let N:= (rough M (t • M.z)).atop y x; let Q:= (M.atop y x).V; let P:= liftN F x Q M.k M.key M.park q d (M.bush x) l; let K:= pushP F M.key M.park Q M.k q d x (M.bush x) l; have he:K (N.bell x)= t • K (M.bell x):=by
    rw [show N.bell x = t • (M.bell x) from rfl]; unfold K pushP; rw [show tape.symm (t • (M.bell x))= t • tape.symm (M.bell x) from Next.SectorChange.colors.symm.map_smul _ _,mulVec_smul]
 change P+(t*coupling β*L/v) • (v • (L⁻¹ • K (M.bell x))) = P+coupling β • K (N.bell x)
 rw [he]; simp_rw [smul_smul]; rw [show t*coupling β*L/v * (v * L⁻¹)= coupling β * t from ?_]; field_simp
section
-- generic chart zoom, HAAR budget scrap ~o(g); 
abbrev dues(z:Λ×ℝ):=∑ w∈ Tarn.gate x M i,ansC (S:=S) i w.val.val* logGuard q Z s (tape (B z) w)
abbrev prism_w(s: Signed)(Up:Config SU.group f)(j:Along S):ℝ:= match j with
| .inr (.inl j)=> gplot (batch F.up.loop φ) (pull s 0 Up) j
| _ =>0
abbrev psalms(s:Signed)(j:Along S)(N:Monk SU.group S):ℝ:= prism_w F x s (N.sent x F q d l β) j
def shade(N: Monk SU.group S):=averaged fun s=>∑ j∈Arena.hoop S s i,psalms F q l x β d s j N -- tune order
lemma dew_r (j:Along S)(s:Signed)(m: Monk SU.group S)(p:m.V=M.V): Corne.fle F x q d α l β s j M-Corne.fle F x q d α l β s j m= psalms F q l x β d s j M-psalms F q l x β d s j m:=by
 rcases j with (w|w|w|w)|(w|w)
 · rfl
 · rfl
 · unfold fle Tarn.TaleX psalms prism_w; rw [p,sub_self,sub_self]
 · rfl
 · rfl
 unfold Corne.fle Tarn.TaleX psalms prism_w; rw [p,sub_self,sub_self]
lemma ice_z (m:Monk SU.group S)(p:M.V=m.V): Corne.ink F x q d α l β i M - Corne.ink F x q d α l β i m= shade F q l x β i d M-shade F q l x β i d m:=by
 unfold Corne.ink shade; unfold averaged; rw [←mul_sub,←mul_sub,←sum_sub_distrib, ←sum_sub_distrib]; apply congrArg; refine sum_congr rfl fun a t=>?_ ; rw [←sum_sub_distrib, ←sum_sub_distrib]; exact sum_congr rfl fun j _=>dew_r F M q l x β α d j a m p.symm
lemma dual_r(t:ℝ)(hv:v≠0)(h:L≠0)(w:Λ): let z:=t*coupling β*L/v; let N: Monk SU.group S:= rough (U w) (t•M.z)
 kite F x q d l N β Z s i= dues F M q l x v s L Z i d (w,z):=by
 intro a N; unfold Corne.kite Corne.dua Corne.flare dues; unfold a; have ht:= belt_l F M q l x v β L d w t hv h; rw [ht]
 exact Eq.symm (Finset.sum_subset (f:=fun j:m₀=>ansC (S:=S) i j.val.val * logGuard q Z s (tape (N.fuel x F q d l β) j)) (s₁:=Tarn.gate x M i) (subset_univ _) fun i _ u=>by unfold ansC; rw [if_neg (fun j=>u (mem_filter.mpr ⟨mem_univ _,j⟩)),zero_mul])
end
end YM.CF.Lor

import YM.CF.Ridge.Fume
import YM.CF.Ione.Rale
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
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
open Bake Lilt Rue Trees
variable (E:Pax n)(F:Pax n)(K:Cusp n)
local notation "T0"=> Sweep n
local notation "Γ"=> (plight_C n)
local notation "Hz"=> Scree.Hub n
-- root pension distribute. supports preserving regular total memory.
variable (τ:Ids n) {v:Aura n→ℝ}(qE:Sym_a E)(p:Turf E)(s_:0≤h) (t:∀ i:Aura n, Vow.Medal P i.val ∅ (E i) h (v i))
variable(Q:Sweep n→Prop)(q:Pant_k Q E)
local notation "sE"=> cast_E E τ
include s_ t q p
lemma worth_SK (u:∀ i:Seat n,tallB v P.B (P.supportExponent+1+1) i≤b): IncX Q sE P h (reserveT P.power P.order P.B 1*b):=by
 let V:=pence_Q P v; refine ⟨⟨V,dare_L P E τ p s_ t,fun i=> ?_⟩,fun s w U g X y=>?_ ⟩
 · let R:= reserveT P.power P.order P.B 1; let X:= univ.filter (fun j:Hz=>i=j.val.1); let G:= univ.filter (fun z:Aura n=>i∈z.val); apply le_trans _ (mul_le_mul_of_nonneg_left (u i) (show 0≤R from (by unfold R reserveT coin_n stilK; positivity)))
   rw [←sum_filter,←sum_fiberwise_of_maps_to (s:=X) (t:=G) (g:=lagE) (fun j p=>mem_filter.mpr ⟨mem_univ _, (mem_filter.mp p).2.symm ▸ j.property⟩), tallB,mul_sum]; apply sum_le_sum; intro j y; let Z:Hz:=⟨(i,j.val),(mem_filter.mp y).2⟩; have hk : lagE Z=j:=Subtype.ext rfl; rw [sum_eq_single_of_mem (s:=X.filter fun i=>lagE i=j) Z (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩,hk⟩)]; exact loan_t P E s_ t j i Z hk
   intro v t' h; have hx:v=Z:= Subtype.ext (Prod.ext ((mem_filter.mp (mem_filter.mp t').1).2.symm) (congrArg Subtype.val (mem_filter.mp t').2)); exact False.elim (h hx)
 let I:=lagE X; let W:Orbit n:=(y,τ); let S:= moldA s I; have hv: E S ((yellA s W).1,τ)= FrameR s U (E I W):=by rw [tama s U g,←q s w,←p S (yellA s W) τ] -- -- tune closing effect
 change bassH S • E S ((yellA s W).1,τ)= FrameR s U (bassH I • _); rw [hv,map_smul,show bassH S=bassH I from ?_]; unfold S bassH; rw [show (moldA s I).val.card=I.val.card from Finset.card_map _]
end YM.CF.Ione

import YM.CF.Lich.Way
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lich
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
-- separate path ledger Φ.M.Target.S.P
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{r n j d:ℕ}
namespace Muster
variable{G S x e T}
variable(A:Muster G S x e T)
variable(U: Monk SU.group S)(V W:Rent0 G e) -- V true W at ζ=0
local notation "θ"=> A.room
local notation "j"=> A.loft
local notation "β"=> A.beta
local notation "q"=> A.trot
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "l"=> A.post
local notation "F"=> U.sent x T q θ l β
local notation "Y"=> (U.park,U.k)
local notation "K"=> U.key.dome (j*radiusB x)
local notation "Q'"=> A.LawQ
local notation "YY"=> A.Beds
-- account per site
-- far components plus interior.Optional momentum.
open Corne
-- Lens finite. parcel by core.Extension of tessellation includes every face.
local notation "m"=> More (mid N B)
abbrev slot(w:LinkS S n):Support (Domain N B):= univ.biUnion fun i:Fin (n+2)=>halo ((l+65)*radiusB x) {S.ratio.parent (w i).1}
def badge(w:LinkS S n):Palot.leaf (Site (Domain N B)):= ⟨slot A w,by let z:Fin (n+2):=0; let i:=S.ratio.parent (w z).1; exact ⟨i,mem_biUnion.mpr ⟨z,mem_univ _, (halo_subset _ _) (mem_singleton_self _)⟩⟩ ⟩
def leys(o:Site m)(w:LinkS S n):ℝ:=plant S o w*(pave T x q θ l w U-paveB (x:=x) T w (kist U))
variable (n)
def want(o:Site m)(L:Palot.leaf (Site (Domain N B))):= ∑ i∈finW o S x n with badge A i=L,leys A U o i
def massX(L:Palot.leaf (Site (Domain N B))):= ∑' k:ℕ,∑ o:Site (Domain N B),want (k+3) A U o L -- order n
lemma transact (h:Ready T x)(p:1000≤ radiusB x)(o:Site m): penR T x q θ l U n o= ∑ a:Palot.leaf (Site (Domain N B)),want n A U o a :=by unfold penR; rw [bedsX _ _ _ _ _ _ n o h p,spitB T (kist U) _ h p]; unfold want; rw [comet,← sum_sub_distrib]; exact sum_congr rfl fun i _=>(mul_sub (plant S o i) _ _).symm
structure Portus : Prop where
 guard:∀ L:Palot.leaf (Site (Domain N B)),Summable (fun k:ℕ=> ∑ i:Site m, want (k+3) A U i L)
lemma summons(h:Ready T x)(ht:1000≤radiusB x)(p:Portus A U): ∑ i,massX A U i=taxT A U:=by unfold massX taxT; rw [← Summable.tsum_finsetSum (fun i _=>p.guard i)]; refine tsum_congr fun k=>?_ ; simp_rw [transact (k+3) A U h ht, Finset.sum_comm (f:= want (k+3) A U)] -- orientation simp loop
-- locality and coverage.W.Wealth.Note.Signed sort.
variable{E:Support (Domain N B)}{U':Monk SU.group S}(w:Palot.leaf (Site (Domain N B)))(p:Beat U U' E)(h:w.val ⊆ E)(ht:1000≤radiusB x)(hr:Ready T x)
include p h ht hr
lemma wells (o:Site m) : want n A U o w=want n A U' o w:= by unfold want; refine sum_congr rfl fun b z=>?_ ; have he(i):Beat.shadows (o:=S.ratio.parent (b i).1) E ((l+58)*radiusB x):= fun x' v=> h ((mem_filter.mp z).2 ▸ (show x'∈ (badge A b).val from mem_biUnion.mpr ⟨i,mem_univ _,(Corona.halo_mono (Nat.mul_le_mul_right _ (by omega)) (Subset.refl _)) v⟩)); unfold leys; rw [payV T x q θ l b hr ht he p,stencil T A b hr ht he (Beat_k U p)]
lemma purse: massX A U w=massX A U' w:= tsum_congr fun k=>sum_congr rfl fun i _=>wells (k+3) A U w p h ht hr _ -- check order
end Muster
end YM.CF.Lich

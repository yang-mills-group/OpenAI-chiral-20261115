import YM.CF.Fief.Lucid
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
local notation "L"=> mid N B
variable (G)
-- induced F Ledger at free histories any epoch. size capacity I(kernel). patches.D
abbrev cohort(x:Site (Domain X B))(j:ℕ):= (univ:Finset (Single (mid N B))).filter fun i=> (ratio G).embed (place_x i) ∈ Branch.bay (terr _) x j
lemma col(m:Site mX)(j:ℕ)(p:Odd G.count.val): ((cohort G m j).card:ℝ)≤ Tenant.quota*((j:ℝ)+1)^4:=by
 let I:=cohort G m j; let T:= tempo G 1; let P:Seal _:=Branch.bay (terr _) m j
 have ht: I.image (patchQ G)⊆ Branch.board T P:=by intro i t; obtain ⟨j,h,rfl⟩:=mem_image.mp t; refine mem_filter.mpr ⟨mem_univ _,?_ ⟩; change lookM G _∈ P; rw [trK G _ p]; exact (mem_filter.mp h).2
 apply le_trans _ ((temper_cap G 1).place m j); rw [← Finset.card_image_of_injective I (f:=patchQ G) (?_ )]; exact_mod_cast card_le_card ht; exact (patchQ G).injective -- tune
local notation "Lt"=> Fintype.card
variable {b' c D A:ℝ}{w:mSeal X B→Toll (Single (mid N B))}{F:Haze N X B G e} (p:Odd G.count.val)(P:∀ S,Filer G S (w S) b' k (F S))(h:Ledger a w c)(hp:0<a)
include P h p hp
lemma cage(o:Site mX)(j:ℕ) : ∑ S∈(hit0 o).filter (fun x=>x.card=j), Branch.rent (a/2) S*ledgerV (w S) ≤ Real.exp (-a/2*j)*(Tenant.quota*((j:ℝ)+1)^4)*c:=by
 let A:=(hit0 o).filter fun x=>x.card=j; let m:=Real.exp (-a/2*j); have hm:0 ≤ m:=(Real.exp_pos _).le
 have hx(i)(u:i∈A) : Branch.rent (a/2) i=m*Branch.rent a i:=by unfold Branch.rent m; rw [←Real.exp_add,(mem_filter.mp u).2]; congr 1; ring
 let X':=cohort G o j; have he S (hi:S∈A) : ledgerV (w S)=∑ i∈X',∑ k,w S i k:=by
    unfold ledgerV; rw [←sum_subset X'.subset_univ]; intro i _ ht; apply sum_eq_zero; intro k _; by_contra p; obtain ⟨g,v,-⟩:= (P S).root i k p
    have he:o∈S:= (mem_filter.mp (mem_filter.mp hi).1).2; apply ht; apply mem_filter.mpr; exact ⟨mem_univ _,by rw [←(mem_filter.mp hi).2]; exact Grove.basin g he (mem_filter.mp v).2⟩
 rw [sum_congr rfl (fun i (k:i∈A)=>show Branch.rent (a/2) i*_=m*(Branch.rent a i* (∑ j∈X',∑ k,w i j k)) by rw [hx i k,he i k,mul_assoc]),←mul_sum, show Real.exp _ * _ * c=m*(Tenant.quota*((j:ℝ)+1)^4*c) by unfold m; rw [mul_assoc]]; apply mul_le_mul_of_nonneg_left _ hm
 simp_rw [mul_sum]; rw [sum_comm]; have hv(i):∑ S∈A,∑ k,Branch.rent a S*w S i k ≤ c:=by
    rw [sum_comm]; refine le_trans ?_ (h.rows i); exact sum_le_sum fun k _=> sum_le_sum_of_subset_of_nonneg (subset_univ A) (fun S _ _=>mul_nonneg (Real.exp_pos _).le ((P S).pos i k))
 exact (sum_le_sum (fun i (_:i∈X')=>hv i)).trans (by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (col G o j p) h.posP)
def lampQ (a:ℝ):= (∑' i:ℕ,Real.exp (-a/2*i)*(Tenant.quota*((i:ℝ)+1)^4))
lemma cap_l (o:Site (Domain X B)) :hitE (a/2) (fun i=>ledgerV (w i)) o≤ lampQ a*c:=by
 let M:= Fintype.card (Site (Domain X B)); have hx:∀ S:Support mX,S.card∈range (M+1):=fun i=> mem_range.mpr (lt_of_le_of_lt (card_le_univ _) (by unfold M; omega))
 rw [show hitE (a/2) (fun i=>ledgerV (w i)) o=∑ i∈ range (M+1),∑ S∈(hit0 o).filter (fun S=>S.card=i),Branch.rent (a/2) S * ledgerV (w S) from ?_]; swap
 · simp_rw [sum_filter]; -- first tactic needs sum_filter at hit0 not also unfold hitE .
   rw [sum_comm]; simp [hx,hitE] -- tune
 refine (sum_le_sum (fun i _=> cage G k p P h hp o i)).trans ?_; rw [←sum_mul]; exact mul_le_mul_of_nonneg_right ((fund_hit a Tenant.quota hp (by unfold Tenant.quota; positivity)).sum_le_tsum _ (fun i _=>by unfold Tenant.quota; positivity)) h.posP
end YM.CF.Fief

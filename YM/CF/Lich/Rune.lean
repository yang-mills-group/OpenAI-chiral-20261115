import YM.CF.Lich.Mars
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
-- chained counts.Pinterest
open Matrix Further.CurvedGaussianJets.Tracks PhysicalNext.OrderedAffine2B.SymFare
variable {J E:Type}[DecidableEq J][Fintype J][DecidableEq E]
def laneG(f:J→Finset J)(t:Finset J): (n:ℕ)→ Finset (Run J n):= fun n=> univ.filter fun i=> i 0 ∈ t ∧ ∀ j':Fin n,i j'.succ ∈ f (i j'.castSucc)
lemma moonG (w:J)(f:J→Finset J)(n:ℕ): (laneG f {w} (n+1)).card≤ (laneG f (f w) n).card:= by
 let H:=laneG f {w} (n+1); let W:=laneG f (f w) n; let r(u:H):= Fin.tail u.val; have hp(u:H): u.val 0=w:=mem_singleton.mp (mem_filter.mp u.property).2.1
 let R(u:H):↥W:=⟨r u,by
    have he:= (mem_filter.mp u.property).2; refine mem_filter.mpr ⟨mem_univ _,?_,fun i=>he.2 i.succ⟩; exact (hp u ▸ (show u.val _∈f (u.val 0) from he.2 0)) ⟩
 have hu : Injective R:=fun i j' v=> Subtype.ext (funext fun k=>Fin.cases ((hp i).trans (hp j').symm) (congrFun (Subtype.ext_iff.mp v)) k) -- congrFun used implicit k
 have h:= Fintype.card_le_of_injective R hu; rwa [Fintype.card_coe, Fintype.card_coe] at h
lemma thrush(f:J→Finset J)(t:Finset J)(k n:ℕ) (p:∀ i,(f i).card ≤ k) : (laneG f t n).card ≤ t.card*k^n:=by
 induction n generalizing t with
 | zero => simp only [pow_zero,mul_one]; exact Finset.card_le_card_of_injOn (fun v=> v 0) (fun i w=> (mem_filter.mp w).2.1) fun i h j' t g=> funext (fun u=> by fin_cases u; exact g)
 | succ n ih =>
    have ht: (laneG f t (n+1))= t.biUnion fun i=>laneG f {i} (n+1):= Finset.ext fun i=>by
       rw [mem_biUnion]; refine ⟨fun w=> ⟨i 0,(mem_filter.mp w).2.1,mem_filter.mpr ⟨mem_univ _,mem_singleton_self _,(mem_filter.mp w).2.2⟩⟩,fun ⟨x,z,g⟩=>?_⟩; exact mem_filter.mpr ⟨mem_univ _,(mem_singleton.mp (mem_filter.mp g).2.1).symm ▸ z,(mem_filter.mp g).2.2⟩
    rw [ht]; exact Finset.card_biUnion_le.trans ((sum_le_sum (fun i _=> (moonG i f n).trans ((ih (f i)).trans (Nat.mul_le_mul_right _ (p i))))).trans_eq (by simp [pow_succ']))
local notation "m"=> Domain N B
local notation "m'"=> Domain P B
abbrev ratioB (S:StepData m m')(v:ℕ):ℕ:= Fintype.card Axis*S.patch.L.val^4*(v+v+1)^4
lemma iconic (o:Site m)(v:ℕ): let W:= (univ:Finset (Bond m')).filter (fun i=>separation o (S.ratio.parent i.1) ≤ v); W.card ≤ ratioB S v:=by intro W; exact le_trans (fine_count W (Rel.pavilion v o) (fun i h=>(Rel.theatre ..).mpr (mem_filter.mp h).2)) (Nat.mul_le_mul_left _ ((Corona.halo_size ({o}:Support m) v).trans_eq (by simp)))
lemma hearty (o:Site m)(n:ℕ) : let P:=ratioB S (3*radiusB x); (finW o S x n).card ≤ ratioB S 1*P^(n+1):=by
 intro D; let M:=3*radiusB x; let t(p: Site m)(r:ℕ):=(univ:Finset (Bond m')).filter (fun i=> separation p (S.ratio.parent i.1) ≤ r); let f(i:Bond m'):= t (S.ratio.parent i.1) M
 let H:=t o 1; have he:= thrush f H D (n+1) (fun i=> iconic (S:=S) (S.ratio.parent i.1) M); apply le_trans _ (he.trans (Nat.mul_le_mul_right _ (iconic (S:=S) o 1))); apply Finset.card_le_card; intro w z; obtain ⟨p,h,u,v⟩:= mem_filter.mp z; exact mem_filter.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_univ _,Tarn.innZ _ _ h⟩,fun i=>mem_filter.mpr ⟨mem_univ _,v i _ (Set.mem_insert _ _) _ (Set.mem_insert _ _)⟩⟩ -- tune unused T
end Muster
end YM.CF.Lich

import Bay.C.Mind
import YM.SU5.Exchange.Seed.Station
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf



open Levier Urn Ione
open Peaks


open QuadClock Bake Salt
variable {n:Side} (s:Sweep n)

section
-- adapt Stax Hare
local notation "VX"=> Aura n
local notation "Hk"=> hook (Seat n)
local notation "SD"=> Support (More n)
local notation "Ta"=> Salt.actY s
local notation "Tu"=> moldA s
open PowerSeries
variable (F:Cusp n)(K K':Rinse (Seat n) (Copy n))
 (V:Orbit n)
local notation "M"=> Cadre.chip K F
local notation "M₂"=> Cadre.chip K' F
local notation "Λ"=> Ione.suit_Y s
local notation "W'"=> yellA s V
variable
 (hA: ∀ X D Y,{m m':Copy n} →m' (yellA s V)=Ione.suit_Y s (m V)→K' (moldA s X) (actY s D) (moldA s Y) m' (yellA s V)=Ione.suit_Y s (K X D Y m V))
 (e:∀ X:Aura n,∀ D⊆X.val,F (moldA s X) (actY s D) (yellA s V)= Ione.suit_Y s (F X D V))
set_option linter.unusedVariables false

lemma turn_p (X: VX)(D:Support (More n))(G:Hk)(k:ℕ)(t:∀ Y:VX,∀ U ⊆ Y.val,∀ m ≤k,coeff m (M₂ (Tu Y) (Ta U)) W' =Λ (coeff m (M Y U) V)):
 coeff k (∏ j∈burn s G, M₂ j ((Ta D)∩j.val)) W'=Λ (coeff k (∏ j∈G, M j (D∩ j.val)) V):=by
 have hp : (∏ j∈burn s G,M₂ j (Ta D∩j.val))=∏ j∈G,M₂ (Tu j) ((Ta D)∩(Tu j).val):=by exact prod_map G (moldA s).toEmbedding (fun j=> M₂ j ((Ta D)∩j.val)) -- pattern
 rw [show ∏ j∈burn s G,M₂ j ((Ta D)∩j.val)= _ from hp]; -- prove via coefficient.R
 let A(i:Aura n):=M₂ (Tu i) (Ta (D∩i.val)); rw [show (∏ j∈G,M₂ _ _)=∏ j∈G,A j from ?_]; swap; · refine prod_congr rfl fun i u=>congrArg (M₂ (Tu i)) (Finset.map_inter ..).symm
 rw [coeff_prod,coeff_prod,Finset.sum_apply,Finset.sum_apply,map_sum]; apply sum_congr rfl; intro j w; rw [Finset.prod_apply,Finset.prod_apply,map_prod]; exact prod_congr rfl fun i p=> t i _ inter_subset_right _ (le_trans (single_le_sum (fun i _=>Nat.zero_le (j i)) p) ((mem_finsuppAntidiag.mp w).1.le))
include hA
set_option maxHeartbeats 180000 in
lemma turn_rill (X Y:VX)(D:SD)(k:ℕ)(S: Finset Hk)(pS:∀ G:Hk,G∈S↔burn s G∈ S)(u:D⊆ X.val)(t:∀ Y:VX,∀ U⊆Y.val,∀ m ≤ k,coeff m (M₂ (Tu Y) (Ta U)) W'=Λ (coeff m (M Y U) V)): coeff k (rill K' M₂ S (Tu X) (Ta D) (Tu Y)) W'=Λ (coeff k (rill K M S X D Y) V):=by
 rw [rils,rils,Finset.sum_apply,Finset.sum_apply,map_sum]; symm; apply sum_equiv (burn s); intro G; rw [mem_inter,mem_inter,trum,pS G]
 intro G g; exact (@hA X D Y (coeff k (∏ j∈G,M j (D∩j.val))) (coeff k (∏ j∈burn s G,M₂ j ((Ta D)∩j.val))) (turn_p s F K K' V X D G k t)).symm
include e
lemma rise_k (X:Aura n)(D:SD)(k:ℕ)(u:D⊆ X.val): coeff k (M₂ (Tu X) (Ta D)) W'=Λ (coeff k (M X D) V):=by
 induction k using Nat.strong_induction_on generalizing X D with| h k ih=>
    cases k with
    |zero=>rw [Cadre.peg,Cadre.peg,e X _ u]
    |succ i=>
       nth_rw 1 [Cadre.peel]; nth_rw 1 [Cadre.peel D _ X F] -- might expand inside lhs
       rw [sprig,sprig,Cadre.stepL,map_sum,Cadre.stepL,map_sum, Pi.smul_apply,Pi.smul_apply,map_smul]; apply congrArg; rw [Finset.sum_apply,Finset.sum_apply,map_sum]; symm; refine sum_equiv (moldA s) (by simp) ?_; intro Y _; exact (turn_rill s F K K' V hA X Y D i _ (by simp) u fun Y D p i' h=> ih i' (Nat.lt_succ_of_le h) _ _ p).symm

lemma tuny (u:ℕ)(X:Aura n)(D:SD)(r:D⊆X.val):
 layerN F K' u (Tu X) (Ta D) W'=Λ (layerN F K u X D V):=by
 simp only[layerN, Finset.sum_apply]
 rw[map_sum]; exact sum_congr rfl fun i _=>rise_k s F K K' V hA e X D i r
end

open TreasuryFog Mew

lemma hub_inj : Injective (moveHub s) := by
 intro i j h; apply Subtype.ext; have ht:=congrArg Subtype.val h; refine Prod.ext ((boxA s).symm.injective (congr_arg Prod.fst ht)) ?_; exact Finset.map_injective (boxA s).symm.toEmbedding (congrArg Prod.snd ht)
lemma force_inj : Injective (moveForce s) := by
 intro i j h; apply Subtype.ext; have ht:=congrArg Subtype.val h; exact Prod.ext (hub_inj s (congrArg Prod.fst ht)) (Finset.map_injective _ (congr_arg Prod.snd ht))

lemma settler {F:ForceBudget n}
 (e:passingF n s F F): passingU n s (settleK F) (settleK F) := by
 intro i x p D q
 rw [settleK,settleK,Finset.sum_apply,Finset.sum_apply,map_sum]
 let A:= Equiv.ofBijective _ ⟨force_inj s,Finite.surjective_of_injective (force_inj s)⟩
 symm; refine sum_equiv A ?_ (fun j _=>(e j x p).symm)
 intro j
 simp only [motV,mem_filter,mem_univ,true_and]
 exact and_congr (moldA s).injective.eq_iff.symm
    (map_injective (boxA s).symm.toEmbedding).eq_iff.symm

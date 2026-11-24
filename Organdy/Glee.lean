import Organdy.Buoy
import YM.CF.Salt.Rider
import YM.CF.Stax.Bust
/-! Relative layer covariance, adapting YM/CF/Stax/Hare rise induction. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Tulip Lat Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive  Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Urn Tenant Hake Salt Spire Nacre Dial SU
open QuadClock PowerSeries Vow.TreasuryFog
variable (s:Sweep n)
local notation "T"=> γS s
local notation "D₁" => detX s.s
local notation "B₁" => s.charge
local notation "JS"=> Single n
local notation "Fz"=> FC (Dwell n)

local notation "VX"=> Aura n
local notation "Ta"=> Salt.actY s
local notation "Tu"=> moldA s
local notation "Hk"=> hook (Seat n)
local notation "SD"=> Support (More n)
local notation "Λ"=> Ione.suit_Y s

section Rise
variable (V:Orbit n)
local notation "W'"=> yellA s V
variable (K fK:Rinse (Seat n) (Copy n)) (F:Vow.Cusp n)
variable (leapQ:∀ X:Aura n,∀ D:Support (More n),∀ Y:Aura n,∀ i j:Copy n,
   j (yellA s V)=Ione.suit_Y s (i V)→ fK (moldA s X) (actY s D) (moldA s Y) j (yellA s V)=Ione.suit_Y s (K X D Y i V))
variable (e:∀ X:Aura n,∀ D⊆X.val,F (moldA s X) (actY s D) (yellA s V)=Ione.suit_Y s (F X D V))
local notation "M"=> Cadre.chip K F
local notation "M'"=> Cadre.chip fK F
set_option linter.unusedVariables false
lemma turn_p (X: VX)(D:Support (More n))(G:Hk)(k:ℕ)(t:∀ Y:VX,∀ F ⊆ Y.val,∀ m ≤k,coeff m (M' (Tu Y) (Ta F)) W' =Λ (coeff m (M Y F) V)):
 coeff k (∏ j∈burn s G, M' j ((Ta D)∩j.val)) W'=Λ (coeff k (∏ j∈G, M j (D∩ j.val)) V):=by
 have hp : (∏ j∈burn s G,M' j (Ta D∩j.val))=∏ j∈G,M' (Tu j) ((Ta D)∩(Tu j).val):=by exact prod_map G (moldA s).toEmbedding (fun j=> M' j ((Ta D)∩j.val)) -- pattern
 rw [show ∏ j∈burn s G,M' j ((Ta D)∩j.val)= _ from hp]; -- prove via coefficient.R
 let A(i:Aura n):=M' (Tu i) (Ta (D∩i.val)); rw [show (∏ j∈G,M' _ _)=∏ j∈G,A j from ?_]; swap; · refine prod_congr rfl fun i u=>congrArg (M' (Tu i)) (Finset.map_inter ..).symm
 rw [coeff_prod,coeff_prod,Finset.sum_apply,Finset.sum_apply,map_sum]; apply sum_congr rfl; intro j w; rw [Finset.prod_apply,Finset.prod_apply,map_prod]; exact prod_congr rfl fun i p=> t i _ inter_subset_right _ (le_trans (single_le_sum (fun i _=>Nat.zero_le (j i)) p) ((mem_finsuppAntidiag.mp w).1.le))
include leapQ
lemma turn_rill (X Y:VX)(D:SD)(k:ℕ)(S: Finset Hk)(pS:∀ G:Hk,G∈S↔burn s G∈ S)(u:D⊆ X.val)(t:∀ Y:VX,∀ F⊆Y.val,∀ m ≤ k,coeff m (M' (Tu Y) (Ta F)) W'=Λ (coeff m (M Y F) V)): coeff k (rill fK M' S (Tu X) (Ta D) (Tu Y)) W'=Λ (coeff k (rill K M S X D Y) V):=by
 rw [rils,rils,Finset.sum_apply,Finset.sum_apply,map_sum]; symm; apply sum_equiv (burn s); intro G; rw [mem_inter,mem_inter,trum,pS G]
 intro G g; exact (leapQ _ _ _ _ _ (turn_p s V K fK F X D G k t)).symm
include e
lemma rise_k (X:Aura n)(D:SD)(k:ℕ)(u:D⊆ X.val): coeff k (M' (Tu X) (Ta D)) W'=Λ (coeff k (M X D) V):=by
 induction k using Nat.strong_induction_on generalizing X D with| h k ih=>
    cases k with
    |zero=>rw [Cadre.peg,Cadre.peg,e X _ u]
    |succ i=>
       nth_rw 1 [Cadre.peel]; nth_rw 1 [Cadre.peel D K X F] -- might expand inside lhs
       rw [sprig,sprig,Cadre.stepL,map_sum,Cadre.stepL,map_sum, Pi.smul_apply,Pi.smul_apply,map_smul]; apply congrArg; rw [Finset.sum_apply,Finset.sum_apply,map_sum]; symm; refine sum_equiv (moldA s) (by simp) ?_; intro Y _; exact (turn_rill s V K fK F leapQ X Y D i _ (by simp) u fun Y D p i' h=> ih i' (Nat.lt_succ_of_le h) _ _ p).symm

end Rise

lemma stableFill (F:ForceBudget n) (w:passingF n s F F):
    passingU n s (settleK F) (settleK F):=by
 intro i x e D u
 have g(S:SD): Ta S = S.map (boxA s).symm.toEmbedding:=rfl
 simp only [settleK,Finset.sum_apply,map_sum];symm
 refine sum_equiv (Salt.fanZ s) ?_ (fun i _=>(w i x e).symm)
 intro j
 simp only [mem_filter,mem_univ,true_and]
 change (_ ↔ Tu (lordD j)=Tu i ∧ Ta _=Ta D)
 exact and_congr ((moldA s).injective.eq_iff).symm ((Finset.map_injective _).eq_iff).symm

def PassingK (K L:Rinse (Seat n) (Copy n)): Prop:=
 ∀ V:Orbit n,Injective (priorP V.2)→∀ X:VX,∀ D:SD,∀ Y:VX,∀ i j:Copy n,
   j (yellA s V)=Λ (i V)→ L (Tu X) (Ta D) (Tu Y) j (yellA s V) =Λ (K X D Y i V)
lemma passingLayer (F:ForceBudget n) (w:passingF n s F F)
   (K L:Rinse (Seat n) (Copy n))(u:PassingK s K L)(d:ℕ):
   passingU n s (layerN (settleK F) K d) (layerN (settleK F) L d):=by
 intro i x e D z
 simp only [layerN,Finset.sum_apply,map_sum]
 exact sum_congr rfl fun j _=>rise_k s x K L (settleK F) (u x e) (fun X=>stableFill s F w X x e) i D j z
end YM.CF.Organdy

import YM.CF.Stax.Bust
import YM.CF.Pith.Pole
import YM.CF.Stax.Cast
import YM.CF.Sour.Park
import YM.CF.Sour.Tile
import YM.CF.Ione.Tape
import YM.CF.Cadre.Point
import YM.CF.Cadre.Gear
import YM.CF.Vow.Grow
import YM.CF.Bake.Pep
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Stax
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
local notation "CΞ"=> Cipher n
variable (P: BudgetPoint)(h:ℝ)(δ:ℕ)
variable {P h δ}
variable (F:Aura n→Support (More n)→ Copy n)(r: Aura n→ Support (More n)→ℝ)(hF:∀ X:Aura n,∀ D⊆ X.val,Fray P h δ X D (F X D) (r X D))
variable (K:Rinse (Seat n) (Copy n))(z:Aura n→ℝ)
variable {M:Orbit n→Aura n→ FC (Dwell n)}(T:Pitch P h δ K z M)
local notation "Q"=> Cadre.chip K F
local notation "N"=> Cadre.chip (cribR z) r
local notation "Qd"=> nutL K F
local notation "Nd"=> nutL (cribR z) r
variable (w:0≤h)
open PowerSeries
open Salt Ione Levier Sour
variable (s:Sweep n)
local notation "Ta"=> Salt.actY s
local notation "Tu"=> moldA s
local notation "Pu"=> Palot.robe
local notation "SD"=> Support (More n)
local notation "Πt"=> (boxA s).symm.toEmbedding
local notation "σX'"=> σX (n:=n) P
variable {H:Bag n}(V:Orbit n)(c:Bias δ H P h z)(p:Injective (priorP V.2)) -- tune shadow
variable (hb:∀ i:Orbit n,Injective (priorP i.2)→∀ X:Aura n,H (moldA s X) (yellA s i)=sauce s.charge (detX s.s) (Sour.γS s) (H X i))
local notation "M"=> Cadre.chip (Bias.payX c) F
local notation "M'"=> nutL (Bias.payX c) F
local notation "Λ"=> Ione.suit_Y s
local notation "W'"=> yellA s V
variable (e:∀ X:Aura n,∀ D⊆X.val,F (moldA s X) (actY s D) (yellA s V)= Ione.suit_Y s (F X D V))
variable {m:ℕ}
lemma turn_p (X: VX)(D:Support (More n))(G:Hk)(k:ℕ)(t:∀ Y:VX,∀ F ⊆ Y.val,∀ m ≤k,coeff m (M (Tu Y) (Ta F)) W' =Λ (coeff m (M Y F) V)):
 coeff k (∏ j∈burn s G, M j ((Ta D)∩j.val)) W'=Λ (coeff k (∏ j∈G, M j (D∩ j.val)) V):=by
 have hp : (∏ j∈burn s G,M j (Ta D∩j.val))=∏ j∈G,M (Tu j) ((Ta D)∩(Tu j).val):=by exact prod_map G (moldA s).toEmbedding (fun j=> M j ((Ta D)∩j.val)) -- pattern
 rw [show ∏ j∈burn s G,M j ((Ta D)∩j.val)= _ from hp]; -- prove via coefficient.R
 let A(i:Aura n):=M (Tu i) (Ta (D∩i.val)); rw [show (∏ j∈G,M _ _)=∏ j∈G,A j from ?_]; swap; · refine prod_congr rfl fun i u=>congrArg (M (Tu i)) (Finset.map_inter ..).symm
 rw [coeff_prod,coeff_prod,Finset.sum_apply,Finset.sum_apply,map_sum]; apply sum_congr rfl; intro j w; rw [Finset.prod_apply,Finset.prod_apply,map_prod]; exact prod_congr rfl fun i p=> t i _ inter_subset_right _ (le_trans (single_le_sum (fun i _=>Nat.zero_le (j i)) p) ((mem_finsuppAntidiag.mp w).1.le))
include hb p
lemma turn_rill (X Y:VX)(D:SD)(k:ℕ)(S: Finset Hk)(pS:∀ G:Hk,G∈S↔burn s G∈ S)(u:D⊆ X.val)(t:∀ Y:VX,∀ F⊆Y.val,∀ m ≤ k,coeff m (M (Tu Y) (Ta F)) W'=Λ (coeff m (M Y F) V)): coeff k (rill (Bias.payX c) M S (Tu X) (Ta D) (Tu Y)) W'=Λ (coeff k (rill (Bias.payX c) M S X D Y) V):=by
 rw [rils,rils,Finset.sum_apply,Finset.sum_apply,map_sum]; symm; apply sum_equiv (burn s); intro G; rw [mem_inter,mem_inter,trum,pS G]
 intro G g; exact (leap z s D V _ _ c p hb _ _ (turn_p F z s V c X D G k t)).symm
include e
lemma rise_k (X:Aura n)(D:SD)(k:ℕ)(u:D⊆ X.val): coeff k (M (Tu X) (Ta D)) W'=Λ (coeff k (M X D) V):=by
 induction k using Nat.strong_induction_on generalizing X D with| h k ih=>
    cases k with
    |zero=>rw [Cadre.peg,Cadre.peg,e X _ u]
    |succ i=>
       nth_rw 1 [Cadre.peel]; nth_rw 1 [Cadre.peel D _ X F] -- might expand inside lhs
       rw [sprig,sprig,Cadre.stepL,map_sum,Cadre.stepL,map_sum, Pi.smul_apply,Pi.smul_apply,map_smul]; apply congrArg; rw [Finset.sum_apply,Finset.sum_apply,map_sum]; symm; refine sum_equiv (moldA s) (by simp) ?_; intro Y _; exact (turn_rill F z s V c p hb X Y D i _ (by simp) u fun Y D p i' h=> ih i' (Nat.lt_succ_of_le h) _ _ p).symm
lemma nut_k(X:Aura n)(D:SD)(k:ℕ)(u:D⊆ X.val):coeff k (M' (Tu X) (Ta D)) W'=Λ (coeff k (M' X D) V):=by
 cases k; · rw [tick_r,tick_r]; exact (map_zero _).symm
 rename_i i; rw [nutL,sprig,nutL,sprig,Cadre.front,Cadre.front,map_sum,map_sum,Pi.smul_apply,Pi.smul_apply,map_smul]; apply congrArg; rw [Finset.sum_apply,Finset.sum_apply,map_sum]; symm; refine sum_equiv (moldA s) (by simp) ?_; intro Y _; refine (turn_rill F z s V c p hb X Y D i _ ?_ u fun Y D u i _=>rise_k F z s V c p hb e Y D i u).symm; intro G; rw [farW,mem_filter,mem_filter]; exact and_congr (iff_of_true (mem_univ _) (mem_univ _)) map_nonempty.symm -- lhs univ.Iff.rfl wrong
lemma bark (X:Aura n)(D:SD)(u:D⊆ X.val): (birthL c.payX (Tu X) (Ta D)) W' =Λ ((birthL c.payX X D) V):=by
 unfold birthL; simp_rw [show (Ta D=∅)↔D=∅ from Finset.map_eq_empty]; split; · apply leap z s ∅ V 1 1 c p hb X X; exact (map_one _).symm
 exact (map_zero _).symm
end YM.CF.Stax

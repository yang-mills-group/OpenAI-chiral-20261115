import YM.CF.Stax.Bust
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
variable {z₁:Aura n→ℝ}{H H':Bag n}(D:Support (More n))(V:Orbit n)(F' F₀:Copy n)(c:Bias δ H P h z)(c0:Bias δ H' P h z₁)(p:Injective (priorP V.2))(hb:∀ i:Orbit n,Injective (priorP i.2)→∀ X:Aura n,H' (moldA s X) (yellA s i)=sauce s.charge (detX s.s) (Sour.γS s) (H X i))
local notation "W'"=> yellA s V
include c0 hb c p
lemma star_two (X Y:Aura n)(t: Bias.αt Y X D δ):coll_T P (Tu X) (Ta D) (H' (Tu Y)) W'=sauce s.charge (detX s.s) (Sour.γS s) (coll_T P X D (H Y) V):=by
 let a:=moldA s X; have hv:= (optic s D Y X δ).mpr t; let Λ:=sauce s.charge (detX s.s) (γS s); let Qv:=σX' X D; let Kv:=c.scope X Y D t.1 t.2.1 t.2.2; let Ku:=c0.scope (moldA s X) (moldA s Y) (actY s D) hv.1 hv.2.1 hv.2.2
 by_cases f:Gates Qv X.val V.1; swap
 · unfold coll_T; rw [if_neg ?_,if_neg f,sauce,singT,win_z,map_zero]; exact mt (lights_V ..).mp f -- tune
 obtain ⟨Y',q,v⟩:=f; let Z:Orbit n:=(Y',V.2); let X':= σX' a (Ta D); have he: Agrees _ _ _ ∧ Set.EqOn _ _ _:=yellow s V Z X.val v (fun _ _=>rfl)
 let U:= yellA s Z; rw [Kv.toCrate.latch V Z v (fun _ _=>rfl),Kv.toCrate.pointV Z q,Ku.toCrate.latch _ U he.1 he.2, Ku.toCrate.pointV _ (show U.1 ∈ X' from ((Salt.lights_C ..)).mpr q),hb Z p] -- tune
lemma leap_two (X Y:VX)(g:F' W'=suit_Y s (F₀ V)):c0.payX (Tu X) (Ta D) (Tu Y) F' W'=suit_Y s (c.payX X D Y F₀ V):=by
 by_cases hA:Bias.αt Y X D δ; swap; · unfold Bias.payX; rw [dif_neg hA,dif_neg (fun t=> hA ((optic s D Y X δ).mp t)),Pi.zero_apply, Pi.zero_apply,map_zero]
 apply Subtype.ext; rw [c0.truth _ _ _ _ ((optic s D Y X δ).mpr hA) _, g]; change Sault.rind (coll_T _ _ _ _ _ *sauce _ _ _ _) =sauce _ _ _ (c.payX X D Y F₀ V).val; rw [c.truth _ _ _ _ hA _,Sault.plower,star_two z s D V c c0 p hb X Y hA,show (sauce _ _ _) (coll_T P X D (H Y) V*(F₀ V).val)= _ from singm ..]

local notation "Mq"=> Cadre.chip (Bias.payX c0) F
local notation "Mm"=> Cadre.chip (Bias.payX c) F
local notation "M'm"=> nutL (Bias.payX c) F
local notation "Λ"=> Ione.suit_Y s
omit hb p
variable (e:∀ X:Aura n,∀ D⊆X.val,F (moldA s X) (actY s D) (yellA s V)= Ione.suit_Y s (F X D V))
variable {m:ℕ}
lemma turn_two (X: VX)(D:Support (More n))(G:Hk)(k:ℕ)(t:∀ Y:VX,∀ F ⊆ Y.val,∀ m ≤k,coeff m (Mq (Tu Y) (Ta F)) W' =Λ (coeff m (Mm Y F) V)):
 coeff k (∏ j∈burn s G, Mq j ((Ta D)∩j.val)) W'=Λ (coeff k (∏ j∈G, Mm j (D∩ j.val)) V):=by
 have hp : (∏ j∈burn s G,Mq j (Ta D∩j.val))=∏ j∈G,Mq (Tu j) ((Ta D)∩(Tu j).val):=by exact prod_map G (moldA s).toEmbedding (fun j=> Mq j ((Ta D)∩j.val)) -- pattern
 rw [show ∏ j∈burn s G,Mq j ((Ta D)∩j.val)= _ from hp]; -- prove via coefficient.R
 let A(i:Aura n):=Mq (Tu i) (Ta (D∩i.val)); rw [show (∏ j∈G,Mq _ _)=∏ j∈G,A j from ?_]; swap; · refine prod_congr rfl fun i u=>congrArg (Mq (Tu i)) (Finset.map_inter ..).symm
 rw [coeff_prod,coeff_prod,Finset.sum_apply,Finset.sum_apply,map_sum]; apply sum_congr rfl; intro j w; rw [Finset.prod_apply,Finset.prod_apply,map_prod]; exact prod_congr rfl fun i p=> t i _ inter_subset_right _ (le_trans (single_le_sum (fun i _=>Nat.zero_le (j i)) p) ((mem_finsuppAntidiag.mp w).1.le))
include hb p
lemma turn_paid (X Y:VX)(D:SD)(k:ℕ)(S: Finset Hk)(pS:∀ G:Hk,G∈S↔burn s G∈ S)(u:D⊆ X.val)(t:∀ Y:VX,∀ F⊆Y.val,∀ m ≤ k,coeff m (Mq (Tu Y) (Ta F)) W'=Λ (coeff m (Mm Y F) V)): coeff k (rill (Bias.payX c0) Mq S (Tu X) (Ta D) (Tu Y)) W'=Λ (coeff k (rill (Bias.payX c) Mm S X D Y) V):=by
 rw [rils,rils,Finset.sum_apply,Finset.sum_apply,map_sum]; symm; apply sum_equiv (burn s); intro G; rw [mem_inter,mem_inter,trum,pS G]
 intro G g; exact (leap_two z s D V _ _ c c0 p hb _ _ (turn_two F z s V c c0 X D G k t)).symm
include e
lemma rise_two (X:Aura n)(D:SD)(k:ℕ)(u:D⊆ X.val): coeff k (Mq (Tu X) (Ta D)) W'=Λ (coeff k (Mm X D) V):=by
 induction k using Nat.strong_induction_on generalizing X D with| h k ih=>
    cases k with
    |zero=>rw [Cadre.peg,Cadre.peg,e X _ u]
    |succ i=>
       nth_rw 1 [Cadre.peel]; nth_rw 1 [Cadre.peel D _ X F] -- might expand inside lhs
       rw [sprig,sprig,Cadre.stepL,map_sum,Cadre.stepL,map_sum, Pi.smul_apply,Pi.smul_apply,map_smul]; apply congrArg; rw [Finset.sum_apply,Finset.sum_apply,map_sum]; symm; refine sum_equiv (moldA s) (by simp) ?_; intro Y _; exact (turn_paid F z s V c c0 p hb X Y D i _ (by simp) u fun Y D p i' h=> ih i' (Nat.lt_succ_of_le h) _ _ p).symm

end YM.CF.Stax

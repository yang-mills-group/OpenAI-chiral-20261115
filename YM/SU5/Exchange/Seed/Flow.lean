import YM.CF.Stax.Flow
import YM.CF.Cadre.Pawn
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
-- P supports meeting kernel leaf Y
open PowerSeries

-- two different budgets: free derivative on stencil constant vs Mark acting
-- on filled gas subsets, often VERY different. Differential output before
-- dressing norm.Even uses Pension.Timer; no auxiliary approximation of exponent.
variable (Q A' : leaf A→ℝ)(X:leaf A)(Z:leaf A→ Finset A→ℝ)
local notation "K"=> cribR Q

def uCost (V:lace A ℝ)(X:leaf A)(D:Finset A):PowerSeries ℝ :=
 moss X D A'+ ∑ Y:ΣA,rill K V (farW A) X D Y

variable (V:lace A ℝ) -- add lemma transfer.Play
lemma uCast {V':lace A ℝ}{n:ℕ}(W:∀ X:ΣA,∀ D:Finset A, ∀ i≤n,coeff i (V X D)=coeff i (V' X D)) :
 coeff n (uCost Q A' V X D)=coeff n (uCost Q A' V' X D):=by
 unfold uCost; rw [map_add,map_add,map_sum,map_sum]
 refine congrArg ((coeff n (moss X D A'))+ ·) (sum_congr rfl fun Y _ => ?_)
 rw [rils,rils]; apply sum_congr rfl
 intro F w; rw [coeff_prod,coeff_prod]; apply congrArg; apply sum_congr rfl; intro s p
 apply prod_congr rfl; intro y q; exact W _ _ _ ((single_le_sum (fun j _=> Nat.zero_le (s j)) q).trans_eq (mem_finsuppAntidiag.mp p).1)

def uRamp: ℕ→ leaf A→ Finset A→ ℝ
 | 0=> Z
 | n+1 => fun X D=> ((n:ℝ)+1)⁻¹ • coeff n (uCost Q A' (fun X D=> mk fun i=> if h:i≤n then uRamp i X D else 0) X D)
termination_by i=>i

def uChip :lace A ℝ:=fun X D=>mk fun i=> uRamp Q A' Z i X D
local notation "N"=> uChip Q A' Z
lemma uRule : N X D= ham (uCost Q A' N X D) (Z X D):=by
 ext n; cases n
 · rw [uChip,coeff_mk,tick_r,uRamp]
 rename_i i; rw [sprig,uChip,coeff_mk,uRamp]; apply congrArg; apply uCast; intro x y j h; simp only [uChip,coeff_mk,dif_pos h]
lemma uPeg:coeff 0 (N X D)=Z X D:=by rw [uRule,tick_r]
lemma uLead : flowZ N Q A' N:=by
 intro X D u i; nth_rw 1 [uRule]; rw [Cadre.tide]; unfold uCost arpX; simp_rw [phrase]; rfl
lemma uWarm (hQ:0≤ Q)(hA:0≤ A')(hZ:∀ X:ΣA,∀ D⊆X.val,0≤Z X D) (e:D⊆X.val):cent (N X D):=by
 intro n; induction n using Nat.strong_induction_on generalizing X D with
 | h i ih=>
    cases i
    · rw [uPeg]; exact hZ X D e
    rename_i n; rw [uRule,sprig,uCost,map_add,map_sum]; refine mul_nonneg (show (0:ℝ)≤ ((n:ℝ)+1)⁻¹ by positivity) (add_nonneg ?_ ?_)
    · unfold moss; split; · rw [map_zero]
      rw [coeff_C]; split; exact hA X; exact le_rfl
    refine sum_nonneg (fun X _=> ?_); rw [rils]
    refine sum_nonneg (fun G g=> mul_nonneg (hQ X) ?_); rw [coeff_prod]
    exact sum_nonneg fun j u=>prod_nonneg fun a w=> ih _ (Nat.lt_succ_of_le ((single_le_sum (fun k _=> Nat.zero_le (j k)) w).trans_eq (mem_finsuppAntidiag.mp u).1)) _ _ inter_subset_right

-- give Timer eventual usage later at Support.Pl.
lemma uGears (hQ:0≤ Q) (hA: 0≤ A') (hZ:∀ X:ΣA,∀ D ⊆ X.val,0 ≤ Z X D)
 (κ L w s c d e γ:ℝ)(σ: Palot.leaf A→ℝ)(T:Tour σ s)
 (hC:∀ i:A, nook (fog (loom_v L w σ 0) Q γ) i ≤ c)(hD:∀ i:A,shelfR (fog (loom_v L w σ 0) Q γ) i ≤ d) (hI:∀ i:A,nook (A'*loom_v L w σ 0) i ≤ e)
 (m:1 ≤ κ)(hx:0 ≤ s)(pW:0 ≤ w)(ha:0 ≤ γ)(hS:s*c ≤ w)(hκ:0 ≤ c)(per:0 ≤ L-w*1)(hb:e+d*γ-(w-s*c)*γ<0)
 (u:∀ i:A,nook ((roofL Z κ)*loom_v L w σ 0) i < γ): Timer N Q κ L w σ s γ c d e 1 A':=by
 refine ⟨fun X D l=>uWarm D Q A' X Z hQ hA hZ l,hQ,m,T,hx,hκ,zero_le_one,per,pW,ha,?_,hC,hD,hA,hI,hS,hb,uLead Q A' Z⟩
 intro i; have hp:seed_v N κ 0 0=roofL Z κ:=by unfold seed_v bark; simp_rw [car_k,uPeg]
 unfold serif; rw [hp]; exact u _
end YM.CF.Cadre

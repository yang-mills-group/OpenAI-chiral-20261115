import YM.CF.Swell.Bark
import YM.CF.Brood.Sure
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt Leaf
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Prism Moto Oath Font Levier Rill
attribute [local instance] loreM loreN boreKSpace boreXN
open Push.AbsoluteSums Trees Wray Ione Fief
variable {N:Side}{P:BudgetPoint}{A:Type}[Fintype A]{n:ℕ}
variable (σ:A→ Seat N)(h:∀ t:Seat N,(univ.filter fun i=> σ i=t).card≤ n)
variable (M:A→Bag N)(V:A→Aura N→ℝ){Γ H b ℓ:ℝ}{δ:ℕ} (F:∀ i,Blip_o (σ i) (M i) (V i) P δ H b ℓ)
include F h
lemma pulse_L (o:Seat N)(X:ℝ)(v:X+1≤ ℓ)(t:0 ≤b) : tallB (fun j=>∑ i:A,V i j) P.B X o ≤ feeU P.B n*b:=by
 have hp(i):= (F i).chant.weight
 have ht:=pyre_k σ h o (fun i:A=> fun Y:Aura N=>Y.val) V hp X P.B b t (fun i Q v=>by by_contra ht; exact v ((F i).pays _ ht).2) ?_; swap
 · intro i; refine le_trans ?_ ((F i).fee); unfold mass_B Cadre.nook Cadre.spark; rw [sum_filter]; apply sum_le_sum; intro X _; by_cases p:σ i∈ X.val; · rw [if_pos p]; change currency P.B _ _ *V i X≤ V i X*Real.exp ((ℓ-0*0)*_); rw [zero_mul,sub_zero,mul_comm]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right v (Nat.cast_nonneg _))) (hp _ _)
   rw [if_neg p, (F i|>.pays _ p).2,mul_zero] -- align out guard. 
 refine le_trans ?_ ht; unfold tallB Λpay; simp_rw [sum_mul]; rw [sum_comm]; refine sum_le_sum fun i _=>sum_le_sum fun j _=> (mul_comm ..).le
lemma vΨ(o:Seat N)(X:ℝ)(v:X+1 ≤ℓ)(t:0≤b) : let Γ':=Leaf.σ_H (fun x=>∑ i:A,V i x); Cadre.nook (Γ'*loom_v X 0 (widthK N P.B) 0) o ≤ 2*feeU P.B n*b:=by
 intro Γ'; let K':=fun x=>∑ i:A,V i x; refine le_trans ?_ ((mul_le_mul_of_nonneg_left (pulse_L σ h M V F o X v t) (by norm_num:0≤(2:ℝ))).trans_eq (mul_assoc ..).symm); unfold Cadre.nook tallB; rw [mul_sum]; apply sum_le_sum; intro i _; change 2*K' i* Real.exp ((X-0*0)*_) ≤ 2*(K' i*Trees.currency _ _ _); rw [zero_mul, sub_zero, mul_assoc]; exact le_rfl
omit h F
variable (E:Aura N→ℝ)(j k:ℝ)
abbrev μReq (k:ℕ)(i:ℕ):ℝ:= i.factorial*Real.exp 1*(Sour.spanV k)^i
abbrev κRoom(K:ℕ)(X:Aura N):ℝ:= ↑X.val.card
lemma hD_Q (X:Aura N)(t:j+1 ≤ k)(i:ℕ): let b:=Sour.spanV P.B; let A:= κRoom P.B X; A^i * loom_v j 0 (widthK N P.B) 0 X ≤ μReq P.B i * loom_v k 0 (widthK N P.B) 0 X:=by
 intro b A; let v:=widthK N P.B; let c:= v X; have ht:= (vigor N P.B).rate X; have h0:0 ≤ c:= zero_le_one.trans ((vigor ..).pos X)
 have hc:(c:ℝ)^i ≤ (i.factorial:ℝ)*Real.exp 1*Real.exp c:= by
    have hp:= polynomial_cost  (show 0< (1:ℝ) from zero_lt_one) h0 i; simp at hp; refine le_trans (pow_le_pow_left₀ h0 (le_add_of_nonneg_left zero_le_one) i) hp -- tune namespaces
 have hv:=pow_le_pow_left₀ (show 0 ≤ A from Nat.cast_nonneg _) ht i; change A^i*_ ≤ _
 apply le_trans (mul_le_mul_of_nonneg_right hv (Real.exp_pos _).le); unfold loom_v; rw [zero_mul,sub_zero,sub_zero,mul_pow]
 have hz:= (Real.exp_monotone (show c+j*c ≤ k*c from (by nlinarith))); refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by unfold Sour.spanV; positivity)) (Real.exp_pos _).le).trans ?_; rw [Real.exp_add] at hz
 have hv:=mul_le_mul_of_nonneg_left hz (show 0 ≤ μReq P.B i from (by unfold μReq Sour.spanV; positivity)); change _ ≤ μReq P.B i*Real.exp (k*c); refine le_trans ?_ hv; unfold μReq; apply le_of_eq; change (Sour.spanV P.B)^i*((i.factorial:ℝ)*Real.exp 1*Real.exp c)*Real.exp (j*c)=_; ring
-- shift.X
end YM.CF.Swell

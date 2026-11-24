import YM.SU5.Selected.Cor.Bright
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
-- Mult-index $Bool outer feasts. choose one phase t per group independently.
open Stencil (pval pulseNode heatize pace heats)
variable {n d t:Type*}[Fintype n][DecidableEq n][Fintype d][DecidableEq d][Fintype t][DecidableEq t]
namespace Mint
abbrev Pull (n v:Type*) := WRect n (Bool × v)
local notation "P₀" b:max => mask (fun i:d=>(b,i))
lemma pull_back(b:Bool)(i:d)(x:n)(A:Pull n d): (A*P₀ b) x i=A x (b,i):= mask_mem ..
lemma pull_self (b:Bool): (P₀ b)ᴴ*(P₀ b)=1:= mask_self _ (fun i j p=> (Prod.mk.inj p).2)
lemma pull_toll (b:Bool): ‖P₀ b‖ ≤1:= mask_norm (pull_self b)
lemma pull_no (b:Bool): (P₀ b)ᴴ*(P₀ (!b))= (0:Op d):=by ext i j; rw [mask_mem,Matrix.conjTranspose_apply]; simp [mask, Bool.not_eq_self]
lemma diag_pay (x:d→ℂ) (u:∀ i, ‖x i‖≤1): ‖Matrix.diagonal x‖ ≤1:=by
 rw [←Matrix.l2_opNorm_toEuclideanCLM]; apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num); intro v; rw [one_mul]; apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp; rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]; refine sum_le_sum (fun i _=> ?_); rw [show (acts (Matrix.diagonal x) v).ofLp i=x i * v.ofLp i from ?_]; · refine pow_le_pow_left₀ (norm_nonneg _) ((norm_mul ..).trans_le (mul_le_of_le_one_left (norm_nonneg _) (u _))) _
 rw [act_at]; simp [Matrix.mulVec,dotProduct,Matrix.diagonal_apply, ite_mul]
variable (f:d→ pulseNode)
local notation "φ" i:max => pval (f i)
def xM : Op d:= Matrix.diagonal (fun i=>(φ i:ℂ)^(11:ℕ))
def yM : Op d:= Matrix.diagonal (fun i=>(φ i:ℂ))
def pM : Op d:= Matrix.diagonal (fun i=>(heatize (φ i):ℂ))
def lower : WRect (Bool× d) d:= P₀ false +(P₀ true)* xM f
def upper : WRect (Bool× d) d:= (P₀ false+(P₀ true)*yM f)* pM f
lemma lower_pay: ‖lower f‖≤2:= by unfold lower; refine (norm_add_le ..).trans ((add_le_add (pull_toll false) ((charge_mul (pull_toll true) (diag_pay _ ?_)).trans_eq (one_mul _))).trans_eq (by norm_num)); intro i; change ‖(φ i:ℂ)^ (11:ℕ)‖ ≤ _; rw [norm_pow,Complex.norm_of_nonneg (pace ..).1]; exact pow_le_one₀ (pace ..).1 (pace ..).2
lemma upper_pay: ‖upper f‖ ≤ 2:= by
 unfold upper; apply (Matrix.l2_opNorm_mul ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (diag_pay _ ?_)).trans; · refine (norm_add_le ..).trans ((add_le_add (pull_toll false) ((charge_mul (pull_toll true) (diag_pay _ ?_)).trans_eq (one_mul _))).trans_eq (by norm_num)); intro i; exact (Complex.norm_of_nonneg (pace ..).1).trans_le (pace ..).2
 intro i; exact (Complex.norm_of_nonneg ((heats (φ i) (pace ..).1).1.le)).trans_le (heats (φ i) (pace ..).1).2
private lemma peak_(u:pulseNode): ((1:ℂ)+star ((pval u:ℂ)^(11:ℕ))*(pval u:ℂ)) * (heatize (pval u):ℂ)= 1:=by
 have ht:star ((pval u:ℂ)^(11:ℕ))=((pval u)^(11:ℕ):ℂ):=by simp
 rw [ht]; have h0: (1:ℂ)+(pval u:ℂ)^ (12:ℕ) ≠0:=by have h:= Complex.ofReal_ne_zero.mpr (Stencil.power_node u).ne'; push_cast at h; exact h
 unfold heatize; push_cast; rw [←pow_succ, mul_inv_cancel₀ h0]
lemma vote : (lower f)ᴴ* upper f=1:= by
 unfold lower upper; rw [Matrix.conjTranspose_add,Matrix.conjTranspose_mul,← Matrix.mul_assoc,Matrix.add_mul,Matrix.mul_add,Matrix.mul_add, ←Matrix.mul_assoc (P₀ false)ᴴ,Matrix.mul_assoc _ (P₀ true)ᴴ, Matrix.mul_assoc _ (P₀ true)ᴴ,←Matrix.mul_assoc (P₀ true)ᴴ];
 rw [pull_self false,show (P₀ false)ᴴ*(P₀ true)=0 from pull_no false,show (P₀ true)ᴴ*(P₀ false)=0 from pull_no true, Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,pull_self true, Matrix.one_mul]
 ext i j; unfold xM yM pM; rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,Matrix.add_apply,Matrix.mul_diagonal]; by_cases p:i=j; · subst j; simp only [Matrix.one_apply_eq,Matrix.diagonal_apply_eq,Pi.star_apply]; exact peak_ .. -- tune
 rw [Matrix.one_apply_ne p,Matrix.diagonal_apply_ne _ p,zero_mul,zero_add,zero_mul]
-- local rank matrices at given i, function f aggregated; portionG generic with t finite; ingredients used $Marker Pen$.
section
variable {n d t:Type}[Fintype n][LinearOrder n][Fintype d][DecidableEq d][Fintype t][DecidableEq t] (F : Pull n (d× t))(k:d) (f:d→pulseNode)
-- local arms $i$ all copies at t. Use with $P.Caste`
abbrev yoke (b:Bool): WRect n t:= F*mask (fun i:t=>(b,k,i))
lemma yoke_at (b:Bool) (x:n)(j:t): yoke F k b x j=F x (b,k,j):= mask_mem ..
#print Station.portionG
open Station (portionG)
-- only in Stamps? portionG requires n = Single n! use helper. (later)
def takeO (F: WRect n (d× t)): WRect n t:= F*mask (fun i:t=>(k,i))
lemma takeL : takeO k (@HMul.hMul _ _ (Matrix n (d×t) ℂ) Matrix.instHMulOfFintypeOfMulOfAddCommMonoid F (lower (f ∘ Prod.fst))) = mixt_a (f k) (yoke F k true) (yoke F k false) := by
 ext x j; unfold takeO; rw [mask_mem]; unfold lower; rw [Matrix.mul_add,←Matrix.mul_assoc,Matrix.add_apply,mask_mem,xM,Matrix.mul_diagonal,mask_mem]; unfold mixt_a; rw [Matrix.add_apply,Matrix.smul_apply]; simp only [smul_eq_mul,comp_apply, yoke_at]; ring -- tc dec
lemma takeU : takeO k (@HMul.hMul _ _ (Matrix n (d×t) ℂ) Matrix.instHMulOfFintypeOfMulOfAddCommMonoid F (upper (f ∘ Prod.fst)))= mixt_b (f k) (yoke F k true) (yoke F k false):= by
 ext x j; unfold takeO; rw [mask_mem]; unfold upper; rw [←Matrix.mul_assoc, pM,Matrix.mul_diagonal,Matrix.mul_add, ←Matrix.mul_assoc,Matrix.add_apply, mask_mem, yM, Matrix.mul_diagonal,mask_mem]; unfold mixt_b; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, comp_apply, yoke_at]; ring
end
end Mint
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mint
#print axioms vote
#print axioms upper_pay
#print axioms takeU

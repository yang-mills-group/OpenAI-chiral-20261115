import YM.CF.Proa.Wings
import YM.CF.Graph.Coif
import YM.CF.Continuum.Sink
/-!
# Excitation-height estimate on the finite coupled ket

 Estimate of a MANY-letter inserted amplitude against an exponential tilt and
 the very same Board incl its fuel. Extra θ orientations will want both types of
 incoherence in our sell. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Scree Pastry
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
open Phase Spire
namespace Furnace
variable {n:Type*}[LinearOrder n][Fintype n]
variable {P R T:Op n}(h:IsStarProjection P){H J Z x:ℝ}(p:0<H)
local notation "w⇑" r:max=> ((r:ℂ))
def burn (P:Op n)(z x:ℝ): Op n:= (z:ℂ) • P + (x:ℂ) • (1-P)
abbrev upstairs (P:Op n)(H:ℝ) := burn P H⁻¹ H
abbrev downstairs (P:Op n)(H:ℝ) := burn P H H⁻¹
local notation "U" => upstairs P H
local notation "V" => downstairs P H
include h
lemma permit {x Z:ℝ} : burn P x Z*(1-P)= (Z:ℂ) • (1-P):=by rw [burn,add_mul,Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,Porth h,h.one_sub.isIdempotentElem.eq,smul_zero,zero_add] -- h not included! tune
include h
lemma rento {x Z:ℝ} : burn P x Z * P=(x:ℂ) • P:=by rw [burn,add_mul,Algebra.smul_mul_assoc, Algebra.smul_mul_assoc,h.isIdempotentElem.eq,show (1-P)*P=0 by rw [sub_mul,h.isIdempotentElem.eq,one_mul,sub_self],smul_zero,add_zero]
lemma staled {x Z:ℝ} : star (burn P x Z)=burn P x Z:=by simp [burn,h.isSelfAdjoint.star_eq]
omit h in
lemma freeHouse (P:Op n): burn P 1 1=1:=by simp [burn]
lemma gateway (k l m f:ℝ): burn P k l*burn P m f=burn P (k*m) (l*f):=by nth_rw 2 [burn]; rw [mul_add,Algebra.mul_smul_comm,Algebra.mul_smul_comm,permit h,rento h]; simp only [burn, smul_smul]; congr 2 <;> push_cast <;> ring
include p
lemma street : U*V=1:=by rw [gateway h,inv_mul_cancel₀ p.ne',mul_inv_cancel₀ p.ne', freeHouse]
lemma salt : V*U=1:=mul_eq_one_comm.mp (street h p)
omit p
lemma shift {M:Op n}(u: Commute M P) (i:ℝ) : Commute M (upstairs P i):=by
 unfold upstairs burn; exact (u.smul_right _).add_right (((Commute.one_right _).sub_right u).smul_right _)
omit h in
lemma twisting (T:UNI n)(P:Op n)(x y:ℝ) : twist T (burn P x y)=burn (twist T P) x y:=by simp only [burn,map_add,twist_scalar,map_sub,map_one]

private def oct (H:ℝ)(F:Finset n) := fun i:n=> if i∈F then (H:ℂ) else ((H:ℂ))⁻¹
omit h
lemma burn_cut (H:ℝ)(F:Finset n) : downstairs (cutM F) H=Matrix.diagonal (oct H F):=by
 ext x y; by_cases w:x=y
 · subst y; by_cases p:x∈F <;> simp [downstairs,burn,cutM,oct,p]
 simp [downstairs,burn,cutM,w]
private lemma octave_one (b:1 ≤ H)(F S:Finset n): ‖∏ i∈S,oct H F i‖≤ H^F.card:=by
 let d:=oct H F; rw [norm_prod]; apply le_trans (b:=∏ i∈S∩F,H) _ (by rw [prod_const]; exact pow_le_pow_right₀ b (card_le_card inter_subset_right)); have he: S=(S∩F) ∪ (S\F):= by ext; simp; tauto
 nth_rw 1 [he]; rw [prod_union (Finset.disjoint_left.mpr (fun i p q=>(mem_sdiff.mp q).2 (mem_inter.mp p).2))]; let B:=∏ i∈S\F, ‖d i‖; have ht:B≤1:=by
    apply le_trans (prod_le_prod (s:=S\F) (f:=fun i=> ‖d i‖) (fun _ _=>norm_nonneg _) (g:=fun _=>1) (fun i v=>by simp [d,oct,(mem_sdiff.mp v).2,Real.norm_of_nonneg (zero_le_one.trans b), inv_le_one_of_one_le₀ b])) (by simp)
 rw [show ∏ i∈S∩F, ‖d i‖ = ∏ i∈S∩F,H from prod_congr rfl fun i v=> by simp [d,oct,(mem_inter.mp v).2,Real.norm_of_nonneg (zero_le_one.trans b)]]; exact mul_le_of_le_one_right (by exact prod_nonneg (fun _ _=> zero_le_one.trans b)) ht
include h
theorem claim {v:Wave n}(b:1 ≤ H)(w:Sea P v): ∃ C:ℝ, 0 < C ∧ acts (quant U) v= ((C:ℂ))⁻¹ • v∧ ‖quant V‖ ≤ C:=by
 have p:=zero_lt_one.trans_le b
 obtain ⟨T,F,rfl⟩:=spot_projection P h
 let J:=cutM F; let E:= twist T J
 let α:= quantU T
 let C:=H^F.card; let X:=quant (downstairs E H)
 have ht:0<C:=pow_pos p _
 have he:X=twist α (Matrix.diagonal fun s=> ∏ i∈s,oct H F i):=by unfold X; rw [show downstairs E H=twist T (downstairs J H) from (twisting ..).symm,burn_cut, quant_twist, quant_diag] -- using change
 have hh:X*lineOp E=(C:ℂ) • lineOp E:=by
    rw [he,line_twist,cutLine,← map_mul,← twist_scalar]; apply congrArg; ext x y; rw [cutM,Matrix.diagonal_mul]; by_cases v:x=y; swap; · simp [v]
    subst y; by_cases d:x=F; swap; · simp [d]
    rw [d]; simp only [mem_singleton_self,ite_true,Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul,mul_one]; trans ∏ i∈F,(H:ℂ); exact prod_congr rfl fun i h=> if_pos h; simp [C]
 refine ⟨C,ht,?_,?_⟩
 · have hb:acts X v=(C:ℂ) • v:=calc
       _ = acts X (acts (lineOp E) v):= by rw [w.1]
       _ = _ := by rw [←act_mul,hh,act_smul,w.1]
   let Y:= quant (upstairs E H); calc
     _ = ((C:ℂ))⁻¹ • acts Y (acts X v):=by rw [hb,map_smul]; rw [inv_smul_smul₀ (by exact_mod_cast ht.ne')]
     _ = _:= by rw [←act_mul, ← quant_mul,street h p, quant_one, act_one]
 change ‖X‖ ≤ C; rw [he,twist_formula, show star α.val=(star α).val from rfl]; rw [CStarRing.norm_mul_coe_unitary _ (star α),CStarRing.norm_coe_unitary_mul,Matrix.l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg ht.le).mpr (octave_one b F)
end Furnace
end YM.CF.Signal
#print axioms YM.CF.Signal.Furnace.claim

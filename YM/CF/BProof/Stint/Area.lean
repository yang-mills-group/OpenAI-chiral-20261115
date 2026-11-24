import YM.CF.Lattice.Tenant
import YM.CF.BProof.Stint.Mask

/-! Window criterion from VolB-op. With sharp projectors. To simplify
commutator estimate, truncate B-matrix kernel purchases first and pay only the
fractional volume increase when enlarging windows by that cutoff. This gives the
local-box-to-global-norm estimate for B-Pproj. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Stint
open Function Filter Fock Finset Branch Lattice Tenant
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {s:Side}
def area (s:Side)(i:ℕ):ℝ:= (bay (terr s) 0 i).card
lemma area_pos (s:Side)(i:ℕ): 0<area s i := by unfold area; exact Nat.cast_pos.mpr (card_pos.mpr ⟨0,(bay_mem i).mpr (by rw [(terr s).reflex]; omega)⟩)
lemma area_any (x:Site s)(i:ℕ): ((bay (terr s) x i).card:ℝ) = area s i:=by
 unfold area; congr 1; let f(t:Site s):= t+x; have h:bay (terr s) x i=(bay (terr s) 0 i).image f:=by
    ext y; obtain ⟨t,rfl⟩:= (show ∃ t,f t=y from ⟨y-x,sub_add_cancel ..⟩) -- tune
    have he: Injective f:=fun a b=>add_right_cancel
    simp only [mem_image,he.eq_iff, exists_eq_right]; rw [bay_mem,bay_mem]; change separation x (f t) ≤ i ↔ separation 0 t ≤ i; nth_rw 1 [←zero_add x]; rw [show f t=t+x from rfl,separation_translate]
 rw [h,card_image_of_injective _ (show Injective f from fun a b=> add_right_cancel)]

lemma gentle {k:ℝ}(hk:1<k)(a:ℕ): ∃ K:ℕ, ∀ s:Side, ∃ r:ℕ, r+a≤K ∧ area s (r+a) ≤ k*area s r:=by
 have ht:=one_pos.trans hk; let C:ℝ:=16*((a:ℝ)+1)^4; obtain ⟨n,hn,g⟩:= (Eventually.and (eventually_ge_atTop 1) (((tendsto_pow_const_div_const_pow_of_one_lt 4 hk).const_mul C).eventually (gt_mem_nhds (show C*0<1 by simp)))).exists
 have hu:(16:ℝ)*(((n*a:ℕ):ℝ)+1)^4< k^n:=by
    change C*((n:ℝ)^4/k^n)<1 at g; rw [←mul_div_assoc,div_lt_one (pow_pos ht _)] at g; apply lt_of_le_of_lt ?_ g; unfold C; rw [mul_assoc,←mul_pow]; push_cast; have he:1≤(n:ℝ):=by exact_mod_cast hn
    gcongr; nlinarith
 refine ⟨n*a,fun s=>?_⟩; by_contra! v
 have hh(i:ℕ)(t:i≤n): k^i≤area s (i*a):=by
    induction i with
    | zero => rw [pow_zero,Nat.zero_mul]; unfold area; exact_mod_cast (Nat.succ_le_iff.mpr (card_pos.mpr ⟨0,(bay_mem 0).mpr (by rw [(terr s).reflex])⟩) : 1 ≤ (bay (terr s) 0 0).card)
    | succ i ih => rw [pow_succ',Nat.succ_mul]; exact le_trans (mul_le_mul_of_nonneg_left (ih (by omega)) ht.le) (v (i*a) (by rw [← Nat.succ_mul]; gcongr)).le
 exact ((hh n le_rfl).not_gt (lt_of_le_of_lt (Tenant.reach ..) hu))

variable {I Z G:Type*}[Fintype I][DecidableEq I](b:Stage (Site s) I Z G)
lemma areas (r:ℕ)(x:Ket I): ∑ z:Site s, ‖acts (strip b (bay (terr s) z r)) x‖^2 = area s r*‖x‖^2:=by
 simp_rw [EuclideanSpace.norm_sq_eq]; rw [sum_comm, mul_sum]; refine sum_congr rfl fun i _=>?_
 simp_rw [strip,cut_apply,board,mem_filter,mem_univ,true_and,bay_mem,(terr s).sym _ (b.home i),←bay_mem,apply_ite (fun t:ℂ=> ‖t‖),norm_zero,ite_pow,zero_pow (by decide : 2≠0),←sum_filter] -- tune
 rw [show univ.filter (fun x:Site s=>x∈bay (terr s) (b.home i) r)=bay (terr s) (b.home i) r from (by ext; simp),sum_const,nsmul_eq_mul,area_any]
end YM.CF.BProof.Stint

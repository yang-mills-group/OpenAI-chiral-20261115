import YM.CF.Fock.Glacier
/-! Local rotations for any legal pair, using triangular lifts. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Matrix NormedSpace Finset Fock
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]
abbrev I (n:Type*):=Bool×n
abbrev rflip (a:I n):I n:=(!a.1,a.2)
def pen (i:I n):FC n:= if i.1 then takeF i.2 else put i.2
lemma pen_ors (i j:I n): antiB (pen i) (pen j) = if j=rflip i then 1 else 0 :=by
 rcases i with ⟨i|i,f⟩; all_goals rcases j with ⟨j|j,x⟩ <;> simp only [pen,rflip,Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_true,ite_false]
 all_goals first | simpa [antiB] using put_put f x | simpa [antiB] using take_take f x | (rw [antiB_comm]; simpa [antiB] using mixed x f) | simpa [antiB,eq_comm] using mixed f x
lemma scold (i j k: I n) : pen i*pen j*pen k - pen k*(pen i*pen j)= (if j=rflip k then pen i else 0) - (if i=rflip k then pen j else 0):=by
  have he:=pen_ors k j; have ht:=pen_ors k i
  unfold antiB at *; split_ifs at * <;> first
    | solve | linear_combination (norm := noncomm_ring) pen i*he-ht*pen j

def mix(K:Op (I n)):=∑ i:I n,∑ j:I n,K i j • (pen i*pen j)
def boxL (K:Op (I n))(B:FC n):= mix K * B-B*mix K
def phaseX (K:Op (I n))(i k:I n):=K i (rflip k)-K (rflip k) i
lemma cashout (K:Op (I n))(p:I n): boxL K (pen p) = ∑ i:I n,phaseX K i p • pen i:=by
 unfold boxL mix
 simp_rw [mul_sum,sum_mul,← sum_sub_distrib,Algebra.mul_smul_comm,Algebra.smul_mul_assoc, ←smul_sub,scold, smul_sub]; simp only [sum_sub_distrib, smul_ite, smul_zero]
 rw [sum_comm (f:=fun i (j:I n)=> if i=rflip p then K i j • pen j else _)]
 simp [phaseX, sub_smul,sum_sub_distrib]
def stackX (D A W:Op n):Op (I n):=Matrix.of fun i j=>(2:ℂ)⁻¹*(if i.1 then if j.1 then D i.2 j.2 else A i.2 j.2 else if j.1 then -A j.2 i.2 else W i.2 j.2)
def quantX (P C:Op n):Op (I n):=stackX (reserve P C) (driftB P C) (weldB P C)
lemma mix_add (K H:Op (I n)): mix (K+H)=mix K+mix H:=by simp only [mix,Matrix.add_apply, add_smul,sum_add_distrib]
lemma mix_neg (A:Op (I n)): mix (-A)= -mix A:=by simp only [mix,Matrix.neg_apply,neg_smul,sum_neg_distrib]
lemma mix_less (A B:Op (I n)): mix (A-B)=mix A-mix B:=by rw [sub_eq_add_neg,mix_add,mix_neg]; rfl
lemma exciteS (P C:Op n): mix (quantX P C)=excite P C :=by
 unfold excite inning dyad mix quantX
 simp [Fintype.sum_prod_type,pen,stackX, smul_add,smul_sub,mul_smul, sum_add_distrib, sum_neg_distrib,smul_sum]; abel
lemma mix_put (C:Op n): mix (stackX 0 0 C)=coupl C:=by
 unfold coupl squareP mix; simp [Fintype.sum_prod_type, stackX,pen, mul_smul,smul_sum]

abbrev nilX (A:FC n):Prop:= ∀ k:ℕ, Fintype.card n< k→A^k=0
lemma mark_x {C:Op n}(p:Cᵀ= -C)(i:n) : Commute (coupl C) (takeF i*coupl C-coupl C*takeF i):=by
 rw [pair_pull p]; exact row_comm i C
lemma mark_y {C:Op n}(i:n):Commute (coupl C) (put i):=by
  change _*_= _*_
  simp only [coupl,squareP,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]; congr 1
  simp_rw [sum_mul,mul_sum,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]; apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro p _
  rw [mul_assoc]; congr 1; have hx:=put_put p i; have he:= put_put k i; linear_combination (norm := noncomm_ring) put k* hx - he*put p -- sign

structure UnitR (A:FC n):Prop where
  exhaust : nilX A
  stall (i:I n):Commute A (A*pen i-pen i*A)
lemma Commies_cut (A B:FC n)(U:UNI (Finset n))(i:I n) (j:FC n)(h: twist U A=B)(t: twist U j=pen i)(g:Commute A (A*j-j*A)):Commute B (B*pen i-pen i*B):=by rw [←h,←t, ← map_mul, ← map_mul, ←map_sub]; unfold Commute SemiconjBy; rw [←map_mul,g.eq,map_mul]
lemma cutR {C:Op n}{s:Finset n}(g:Cᵀ= -C)(h:IsUnit (stage (cutM s) C)): UnitR (excite (cutM s) C) :=by
 let A:= blend (cutM s) C; let B:= flake s; have he:= flake_excite h; change twist B (coupl A)=_ at he; have hk:Aᵀ = -A := blend_skew (cutM_idp _) h g
 refine ⟨fun k v=> ?_, fun i=>?_⟩
 · rw [←he,← map_pow,coupl_nil A k v,map_zero]
 rcases i with ⟨j,i⟩
 have hx: Commute (coupl A) (coupl A * takeF i-takeF i*coupl A):=by rw [← neg_sub]; exact (mark_x hk i).neg_right
 have ht: Commute (coupl A) (coupl A * put i-put i*coupl A):=by rw [(mark_y i).eq,sub_self]; exact Commute.zero_right ..
 have hi (h:i∈s) : twist B (put i)=takeF i∧twist B (takeF i)=put i:=by rw [flake_take, flake_put, drift, if_pos h]; simp [takeF]
 have hy (h:i∉s):twist B (put i)=put i ∧ twist B (takeF i)=takeF i :=by rw [flake_put,flake_take,drift,if_neg h]; exact ⟨rfl,rfl⟩
 by_cases h:i∈ s <;> cases j
 · exact Commies_cut _ _ B _ (takeF i) he (hi h).2 hx
 · exact Commies_cut _ _ B _ _ he (hi h).1 ht
 · exact Commies_cut _ _ B _ _ he (hy h).1 ht
 exact Commies_cut _ _ B _ _ he (hy h).2 hx
lemma paletteR(A:FC n)(h:UnitR A)(U:UNI n) : UnitR (twist (quantU U) A):=by
 let Q:=quantU U; let V:=star U
 have he: star Q=quantU V:=by apply Subtype.ext; exact (quant_star U.val).symm
 let X:=twist Q A
 refine ⟨fun k p=> by rw [← map_pow,h.exhaust k p,map_zero],fun i=> ?_⟩
 let j:=twist (star Q) (pen i)
 have ht: twist Q j=pen i:=by unfold j; rw [← twin,show Q*star Q=1 from mul_inv_cancel Q]; apply one_des -- tune
 apply Commies_cut _ X Q _ j rfl ht; unfold j; rw [he]; rcases i with ⟨a|a,i⟩
 · let D:=fun i:n=> pen (false,i); change Commute A (A * twist _ (put i)-twist _ (put i)* _); rw [twist_p]; unfold prong; change Commute A (A*(∑ x,V.val x i • D x)-(∑ x,V.val x i • D x)*A)
   simp_rw [mul_sum,sum_mul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,← sum_sub_distrib, ← smul_sub]; exact Commute.sum_right _ _ _ fun j _=> (h.stall (false,j)).smul_right (show ℂ from _)
 · let D:=fun i:n=>pen (true,i); change Commute A (A * twist _ (takeF i)-twist _ (takeF i)* _); rw [twist_t]; unfold prong
   change Commute A (A*(∑ x,cc V.val x i • D x)-(∑ x,cc V.val x i • D x)*A); simp_rw [mul_sum,sum_mul,Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ←sum_sub_distrib, ← smul_sub]; exact Commute.sum_right _ _ _ fun j _=> (h.stall (true,j)).smul_right _
lemma unitR {C P:Op n}(h:IsStarProjection P)(g:Cᵀ= -C)(e:IsUnit (stage P C)): UnitR (excite P C):=by
 obtain ⟨U,s,rfl⟩:= spot_projection P h
 let D:= congrC (star U) C
 have he : C=congrC U D := by
    unfold D; conv_rhs => arg 1; rw [←star_star U]
    rw [congr_inv]
 have hg:IsUnit (stage (cutM s) D):= by
    have ht:=live_cong (star U) e; rw [←stage_twist (star U), twist_inv] at ht; exact ht
 rw [he,←excite_cov hg]; exact paletteR _ (cutR (skew_form g) hg) _
end YM.CF.Acorn

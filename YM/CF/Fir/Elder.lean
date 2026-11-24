import YM.CF.Fir.Esc
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable (u:Bool)(j:ℕ)(L M:Side)(hj:Even j)(ho:Odd L.val)(he:Odd M.val){p:Momentum}
def slashA : Stk L:=stack L (fun _=>angle u)
abbrev sA (u:Bool)(L:Side):Stk L:=slashA u L
lemma slabQ : angle u*angle u=angle u:=by cases u; change (1-Aop)*(1-Aop)=1-Aop; rw [mul_sub,sub_mul 1 Aop Aop,mul_one,AOne,one_mul]; abel; exact AOne -- inspect semis
lemma symQ : star (angle u)=angle u:=by cases u <;> simp [angle,Aadj]
lemma slate : sA u L*sA u L=sA u L:=by rw [sA,slashA, ← stack_mul]; congr 1; exact funext fun _=> slabQ u
lemma slateS: star (sA u L)=sA u L:=by rw [sA,slashA,stack_star]; congr 1; exact funext fun _=> symQ u
lemma pebSlate : peb L*sA u L=sA u L*peb L:=by simp only [peb,sA,slashA,spike_mul,mul_spike,one_mul,mul_one]
lemma slateT (p:Momentum): trident L p*sA u L=sA u L*trident L p:=by
  ext ⟨i,a⟩ ⟨k,b⟩; simp only [Matrix.mul_apply,trident,s_app,sA,slashA,St,Fintype.sum_prod_type,aliasBlock,Matrix.of_apply,s_app,Matrix.smul_apply,smul_eq_mul]; simp [ite_mul,mul_ite,mul_comm]
lemma slateW (hp:physical p): stackW j L p*sA u L=sA u L*stackW j L p:=by
  have h:= congr_arg star (slateT u L p); simp only [star_mul,slateS] at h
  have he:= pebSlate u L
  rw [stackW,returned, show star p=p from hp]; change (sprig _ _ _+star (trident L p)*(1-peb L))*_= _
  rw [mul_add,add_mul,mul_assoc,show (1-peb L)*sA u L=sA u L*(1-peb L) by rw [mul_sub,sub_mul,one_mul,mul_one,he],← mul_assoc,show star (trident L p)*sA u L=sA u L*star (trident L p) from h.symm,mul_assoc]; congr 1; exact (stackA L _ _).eq.symm
lemma Ws_end (p:Momentum): stackW j L p*peb L=sprig j L p:=by rw [stackW,add_mul,mul_assoc,sub_mul,one_mul,peb_sq,sub_self,mul_zero,add_zero,sprig,peb_col]
def wood (p:Momentum): Stk L:= (stackW j L p)⁻¹ * sA u L+returned (stackW j L) p*(1-sA u L)
include hj ho in
lemma timber (hp:p∈realCube zone):
  let H:=wood u j L p; let T:=stackW j L p; let A:=sA u L
  T*(A*H)=A ∧ H*(T*A)=A ∧ (1-A)*H=star T*(1-A) := by
  intro H T A
  have he:T*T⁻¹=1 := Matrix.mul_nonsing_inv T (Matrix.isUnit_iff_isUnit_det _ |>.mp (lofty _ _ hj ho hp))
  have ht:T*A=A*T:=slateW _ _ _ hp.1
  have hu:A*A=A:=slate ..
  have hg:=mul_eq_one_comm.mp he
  have hu1:A*T⁻¹=T⁻¹*A:=by calc
    A*T⁻¹= T⁻¹*T*(A*T⁻¹):=by rw [hg,one_mul]
    _=T⁻¹*A:= by rw [mul_assoc,← mul_assoc T,ht, mul_assoc A T,he,mul_one]
  have hr: A*(1-A)=0:=by rw [mul_sub,mul_one, hu,sub_self]
  have hb:(1-A)*A=0:=by rw [sub_mul,one_mul,hu,sub_self]
  have hs: star T * A = A * star T:= by nth_rw 1 2 [← show star A=A from slateS ..]; rw [← star_mul,← ht,star_mul]
  have hm : (1-A)*T=T*(1-A):=by rw [mul_sub,sub_mul,mul_one,one_mul,ht]
  have hq:H=T⁻¹*A+star T*(1-A):=by unfold H wood returned; rw [show star p=p from hp.1]; rfl
  rw [hq]
  have hx:A*(T⁻¹*A+star T*(1-A))=T⁻¹*A:=by rw [mul_add,← mul_assoc,hu1,← mul_assoc A, ← hs,mul_assoc (star T),hr,mul_zero,add_zero,mul_assoc,hu]
  rw [hx,← mul_assoc,he,one_mul,add_mul]; refine ⟨rfl,?_,?_⟩
  · rw [mul_assoc _ A,← mul_assoc A,← ht,mul_assoc T,hu,← mul_assoc,hg,one_mul,mul_assoc _ (1-A),← mul_assoc (1-A),hm,mul_assoc T,hb,mul_zero,mul_zero,add_zero]
  rw [sub_mul,one_mul,hx]; abel
lemma knocked (M:Side) (l:Site M) (h:Odd M.val)(hp:p∈realCube zone) (hx:p≠0): aliasAt p l≠0:=by
  intro he; by_cases h:l=0
  · rw [h,alias_zero_eq,narrow] at he; exact hx ((smul_eq_zero.mp he).resolve_left (inv_ne_zero (side_ne _)))
  obtain ⟨a,ha⟩:=hit_grade l; have hm: 0<zone*up l a:=mul_pos zone_pos (up_pos ..)
  have hb:= scaled_alias_lower l (mem_cube_real hp zone_pos) a (by intro h'; have ht:=grade_gt h; simp_all [up]); rw [he] at hb; simp at hb; exact (not_lt.mpr hb) hm
end YM.CF.Fir

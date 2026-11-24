import YM.CF.Peaks.Coeur
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable (j:ℕ) (L:Side)(ho:Odd L.val)(hj:Even j)(he:1≤j) {N P:Side} (G:Ratio N P)
variable (u:Bool)(M:Male)(x:Coil N P)
lemma circ (u:Bool): lobe G (!u)=1-lobe G u:=by cases u <;> simp [lobe_plus]
lemma spurH : Commute (lobe G u) (hood G) := by
  have he:(plates N fun _=>sA u G.count * peb G.count)=plates N fun _=>peb G.count*sA u G.count:=by simp only [pebSlate]
  unfold Commute SemiconjBy; rw [lobe,shoulder,op_kron_mul,op_kron_mul,pilesP,pilesP, he]
lemma foil_neg: foal j (!u) M G x=1-foal j u M G x:=by
  rw [foal,foal,← foot_one,← foot_sub]; congr 1; cases u <;> simp [skewE]
lemma wh_neg : wh j L ho (!u) M G x=1-wh j L ho u M G x:=by
  rw [wh,wh,circ]; let C (z):= endorse G (skewE j (upMale L ho M) z N x.2)
  let V:=hood G; let H:=lobe G u
  have he: V-C u=C (!u):=by
    ext i k; by_cases h:en G i∧en G k <;> cases u <;> simp [hood,C,V,h, endorse,extendK,skewE,Matrix.sub_apply]
  change (1-H)*(1-V)+C _=_; rw [←he,sub_mul,one_mul]; unfold C; change (1-V-_)+_= 1-(H*(1-V)+C u); change (1-V-H*(1-V)+(V-C u))=_; abel -- simplify
lemma whirl {H: Op (Single N)} (h:IsStarProjection H) : IsStarProjection (lobe G u*(1-hood G)+endorse G H):=by
  let A:=lobe G u; let V:=hood G; let T:=endorse G H
  have H1:A*A=A:=(lobe_sq ..).1; have H2:star A=A:=(lobe_sq ..).2
  have hv:V*V=V:=(hood_proj G).1; have hg:star V=V:=(hood_proj G).2
  have hk:T*T=T:=by unfold T; rw [rude, h.isIdempotentElem.eq]
  have hx: star T=T:=by unfold T; rw [←endorse_star,h.isSelfAdjoint.star_eq]
  have hh:V*T=T:=by unfold V hood T; rw [rude,one_mul]
  have hl:T*V=T:=by have h:=congr_arg star hh; rwa [star_mul,hx,hg] at h
  let B:=1-V; have hb:star B=B:= by unfold B; rw [star_sub,star_one,hg]
  have hb': B*B=B:=by unfold B; rw [mul_sub,sub_mul (1:Op _) V V,hv,one_mul,mul_one]; abel
  have hp:A*B=B*A:=by unfold B; rw [mul_sub,sub_mul,(spurH ..).eq,mul_one,one_mul]
  have ht: B*T=0:=by unfold B; rw [sub_mul,one_mul,hh,sub_self]
  have ht': T*B=0:=by have he:=congr_arg star ht; rwa [star_mul,hx,hb,star_zero] at he
  change IsStarProjection (A*B+T)
  refine ⟨?_,?_⟩
  · unfold IsIdempotentElem; rw [add_mul,mul_add,mul_add,show A*B*(A*B)=A*B by rw [← mul_assoc,mul_assoc A B A,← hp,← mul_assoc A,H1,mul_assoc,hb'], show A*B*T=0 by rw [mul_assoc,ht,mul_zero],show T*(A*B)=0 by rw [hp,←mul_assoc,ht',zero_mul],hk]; simp
  rw [isSelfAdjoint_iff,star_add,star_mul,H2,hb,hx,hp]
variable (T:Script Male)
def halves (T:Script Male)(u:Bool): Script Male:=fun M _ _ G x=> lake j L ho @T u M G x+lake j L ho @T (!u) M G x

def pine (T:Script Male)(u:Bool): Script Male:=fun M _ _ G x=> foal j u M G x*(halves j L ho @T u M G x)⁻¹*wh j L ho u M G x

include hj he in
lemma seller (p:Use j L @T): Save L true false (fun i _ _ G x=> (halves j L ho @T u i G x)⁻¹) ∧ UnitAlways L (halves j L ho @T u):=by
  have hp(v):Save L false true (lake j L ho @T v):=by obtain ⟨h,e,f⟩:= cup j L ho hj he p v; exact (f.mul h).mul e
  let X:Script Male:=fun i _ _ G x=> dip j u i G x+dip j (!u) i G x
  have he': Save L true false @X:= (fortnight j L ho hj he u).plus (fortnight j L ho hj he (!u))
  refine righted false true ((hp u).plus (hp (!u))) he' ?_
  intro i c f G hx
  obtain ⟨ha,hb,hc,hm⟩:=illumine j L ho hj he G hx i u p
  obtain ⟨hp,hq,ht,hT⟩:=illumine j L ho hj he G hx i (!u) p
  let S:=foal j u i G 1; let A:=dip j u i G 1; let Y:= dip j (!u) i G 1
  change S*A=A at hc; rw [foil_neg] at ht; change (1-S)*Y=Y at ht
  have h1:S*Y=0:=by rw [sub_mul,one_mul] at ht; exact sub_eq_self.mp ht
  have h2:(1-S)*A=0:=by rw [sub_mul,one_mul,hc,sub_self]
  have hh : lake j L ho @T u i G 1 *Y=0:=by rw [lake,mul_assoc,h1,mul_zero]
  have hz : lake j L ho @T (!u) i G 1 *A=0:=by rw [lake,mul_assoc,foil_neg,h2,mul_zero]
  dsimp only [X]; rw [halves,add_mul,mul_add,mul_add,hh,hz,ha,hp,wh_neg]; simp
lemma spruce_kt (p:Use j L @T)(hx:IsUnit (halves j L ho @T u M G x))
    (h:IsStarProjection (foal j u M G x))(k:IsStarProjection (wh j L ho u M G x)): let A:=lake j L ho @T u M G x; let B:= pine j L ho @T u M G x; let P:=foal j u M G x; let V:=wh j L ho u M G x; A*B=V ∧ B*A=P ∧ P*B=B∧ B*V=B:=by
  intro S Q A V; let K:=halves j L ho @T u M G x; let J:=lake j L ho @T (!u) M G x
  have hh:S*A=S:=by unfold S lake; rw [mul_assoc,h.isIdempotentElem.eq]
  have he:V*S=S:=by unfold S lake; rw [←mul_assoc,← mul_assoc,k.isIdempotentElem.eq]
  have hl : V*J=0:=by unfold J lake; rw [wh_neg,← mul_assoc,← mul_assoc,mul_sub,mul_one,k.isIdempotentElem.eq,sub_self,zero_mul,zero_mul]
  have hp : J*A=0:=by unfold J lake; rw [foil_neg,mul_assoc,sub_mul,one_mul,h.isIdempotentElem.eq,sub_self,mul_zero]
  have ht : V*K=S:=by rw [show K=S+J from rfl,mul_add,he,hl,add_zero]
  have hT : K*A=S:=by rw [show K=S+J from rfl,add_mul,hh,hp,add_zero]
  have hg:T=T:=rfl
  change S*(A*K⁻¹*V)=V∧A*K⁻¹*V*S=A∧A*(A*K⁻¹*V)=A*K⁻¹*V∧A*K⁻¹*V*V=A*K⁻¹*V
  obtain ⟨hf,hr⟩: K*K⁻¹=1 ∧ K⁻¹*K=1:=Fock.live hx
  have ha:A*A=A:=h.1; have hv:V*V=V:=k.1
  constructor
  · rw [← mul_assoc,← mul_assoc S A,hh,← ht, mul_assoc V K,hf,mul_one,hv]
  refine ⟨?_,?_,?_⟩
  · rw [mul_assoc _ V S,he,← hT,mul_assoc A,←mul_assoc _ K,hr,one_mul,ha]
  · rw [←mul_assoc,←mul_assoc A A,ha]
  rw [mul_assoc _ V V,hv]
end YM.CF.Peaks

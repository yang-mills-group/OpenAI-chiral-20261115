import YM.CF.Peaks.Call
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable (j:ℕ)(L: Side)(ho:Odd L.val)(hj:Even j)(hg:1≤ j)
def upMale (h:Odd L.val)(M:Male):Male:= ⟨L*M.val,h.mul M.property⟩
def ticketT (G:Script Male)(u:Bool):Script Male:=fun M _ _ g x=> (G M g x)⁻¹ * lobe g u+ star (G M g (icec x))*(1-lobe g u)
def foal (u:Bool):Script Male:=fun M _ _ g x=> foot g (skewE j M u _ x.1)
def wh (u:Bool):Script Male:=fun M N _ G x=> lobe G u*(1-hood G)+endorse G (skewE j (upMale L ho M) u N x.2)
def lake (T:Script Male)(u:Bool): Script Male:=fun M _ _ G x=> wh j L ho u M G x*ticketT @T u M G x* foal j u M G x
def dip(u:Bool): Script Male:=fun i _ _ G x=>mosaic G true false (tub (boards u j G.count i.val)) x
include ho hj hg in
lemma cup {T:Script Male}(p:Use j L @T)(u:Bool): Save L false true (ticketT @T u) ∧ Save L true true (foal j u)∧ Save L false false (wh j L ho u):=by
  let M:= fun m:Male=> upMale L ho m
  have hv: Lively (fun m N=> skewE j (M m) u N):=by obtain ⟨a,c,e,h,s,v,w,H⟩:=skew_s j hg u; exact certify h v (v:=w) fun i N hv=>H _ _ hv
  refine ⟨?_,flowers _ (skew_s j hg u), ((gradeBudget L false u).mul ((Save.one Male).sub (hood_tag L ho))).plus (hailing L ho _ hv)⟩
  exact (((useK j L hj ho p).1).mul (gradeBudget L true u)).plus ((p.expense.withOpp _ _ @T).mul ((Save.one Male).sub (gradeBudget L true u))) -- orientation args
include ho hj hg in -- fix
lemma fortnight (u:Bool): Save L true false (dip j u):=by
  refine unanimous true false L ho (fun (i:Male) L=> tub (boards u j L i.val)) ?_
  have ht:= ((trimP L).reindex (fun i:Male=>())).times (ticket u j L (fun i:Male=> i.val) ho (fun i=> i.property) hj hg);
  obtain ⟨⟨a,c,h,hK,H⟩,-⟩:=tub_bill ht (fun i p hp x hx=> board_verify u j L i.val hj ho i.property hp x hx); simp only [mul_one] at H
  exact ⟨a,c,h,hK,H⟩
variable {N P:Side}(G:Ratio N P)(h:G.count=L)(M:Male)(u:Bool)
lemma bleed (G:Ratio N P)(u:Bool): lobe G u*(1-hood G)=(plates N fun _=> tall u G.count)⊗ₖ (1:Op Slot):=by
  rw [tall, ← pilesP,←pilesM] -- syntax
  rw [lobe,shoulder,piles1,mul_sub,op_kron_mul,one_mul,mul_one, mul_sub,mul_one]; ext; simp [sub_mul] -- fix
lemma foot_stamp (A:Op (Site P×SpinIdx)): foot G (A ⊗ₖ (1:Op Slot))=(solo G A)⊗ₖ 1 := rfl
lemma trans_eq (T:Op (Inta G))(h:IsUnit T): (T ⊗ₖ (1:Op Slot))⁻¹= T⁻¹ ⊗ₖ 1:= Xgr T h
lemma kronvec_sub (A B:Op (Inta G)): (A ⊗ₖ (1:Op Slot))-B ⊗ₖ 1 = (A-B) ⊗ₖ 1 := by ext; simp [mul_sub,sub_mul]
include h ho hg in
lemma wh_base : wh j L ho u M G 1=plates N (vine u j G.count M.val) ⊗ₖ 1:=by
  unfold wh; rw [bleed,show skewE j (upMale L ho M) u N ((1:Coil N P).2)=_ from skew_flat j hg _ u N, endorsement]
  have hx:L*M.val=G.count*M.val:=by rw [h]
  simp only [upMale,hx]; rw [cart_traded (cBar j (G.count*M.val) u hg (by rw [h]; exact ho.mul M.property)),← Matrix.add_kronecker,← low_pose, pilesA]; rfl
include hg in
lemma foal_base : foal j u M G 1= (solo G (cart P (tub (bent u j M.val)))) ⊗ₖ 1 := by unfold foal; rw [Prod.fst_one,show skewE _ _ _ _ _=_ from skew_flat j hg M u P,foot_stamp]
lemma ice_one {N F:Side}: icec (1:Coil N F)=1:=by rw [show (1:Coil N F)=unionP 1 by unfold unionP; simp [profile_trivial]; rfl, revI]
variable {T:Script Male}
include h hj ho in
lemma T_flat (p:Use j L @T): ticketT @T u M G 1=
    let V:=cart N (tub (brix j G.count)); let S:=plates N fun _=> sA u G.count; (V⁻¹*S+star V*(1-S)) ⊗ₖ 1 :=by
  let W:=cart N (tub (brix j G.count)); let U:Op (Inta G):=plates N fun _=>sA u G.count
  unfold ticketT lobe; rw [ice_one,p.fixed _ G h,Xgr _ (brix_inv G j hj (h.symm ▸ ho)), op_kron_mul,one_mul, op_star_kron,star_one]
  change _ + (star W ⊗ₖ 1)*(1-U ⊗ₖ 1)=(W⁻¹*U+star W*(1-U))⊗ₖ 1
  rw [show (1:Op (Iota G))-U ⊗ₖ 1=(1-U) ⊗ₖ 1 from (by simpa only [Matrix.one_kronecker_one] using kronvec_sub G 1 U),op_kron_mul,one_mul, Matrix.add_kronecker]
include h ho hg hj in
lemma illumine (p:Use j L @T):
    lake j L ho @T u M G 1*dip j u M G 1=wh j L ho u M G 1 ∧
    dip j u M G 1 * lake j L ho @T u M G 1=foal j u M G 1∧
    foal j u M G 1*dip j u M G 1=dip j u M G 1 ∧ dip j u M G 1*wh j L ho u M G 1=dip j u M G 1:=by
  have hv:Odd G.count.val:=h.symm ▸ ho
  let Y:=cart N (tub (boards u j G.count M.val))
  rw [lake, wh_base j L ho hg G h,foal_base _ hg G,T_flat j L ho hj G h M u p,show dip j u M G 1=Y⊗ₖ 1 from doodle _ _ _ _ (cBoards j G.count M.val u hg hj M.property hv).sumK];
  obtain ⟨hh,he,hb,hc,hL⟩:=sock G j M.val u hg hj M.property hv
  simp only [Y,op_kron_mul,mul_one]; rw [hh,he,hb,hc]; trivial
end YM.CF.Peaks

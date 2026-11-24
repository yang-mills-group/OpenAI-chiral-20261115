import YM.CF.Peaks.Opening
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable (j:ℕ)(L:Side)(hj:Even j)(hl:Odd L.val)

structure Use (j:ℕ)(L:Side)(T: Script Male):Prop where
  expense: Save L true false T
  orients (M:Male) {c f:Side}(G:Ratio c f) (x:Coil c f): Commute (lobe G true) (T M G x)
  fixed (M:Male) {c f: Side}(G:Ratio c f)(h:G.count=L): T M G 1=cart c (tub (brix j G.count)) ⊗ₖ 1

def cloth (j:ℕ)(m : Male) {N P:Side}(G:Ratio N P)(x:Coil N P): Op (Iota G):=
    let T:= mosaic G true false (tub (brix j G.count)) x; let S:=lobe G true; let P':=lobe G false
    S*T*S+P'*T*P'
lemma brix_save (hl:Odd L.val): Save L true false (fun (_:Male) N P G x=> mosaic G true false (tub (brix j G.count)) x):=by
  refine unanimous true false L hl (fun (_:Male) L=> tub (brix j L)) ?_
  obtain ⟨⟨σ,C,hσ,hC,H⟩,-⟩:= tub_bill ((trimP L).times (W_quote j L hl)) (fun _=>fun _ hp x hx=>verifies _ _ hp _ hx)
  simp only [one_mul,mul_one] at *; exact ⟨σ,C,hσ,hC,fun i r t=> H () r t⟩
include hl in
lemma canUse : Use j L (cloth j):=by
  refine ⟨?_,?_,?_⟩
  · unfold cloth; dsimp only; exact (((gradeBudget L true true).mul (brix_save j L hl)).mul (gradeBudget L false true)).plus (((gradeBudget L true false).mul (brix_save j L hl)).mul (gradeBudget L false false))
  · intro M c f G x
    rw [Commute,SemiconjBy]; unfold cloth; simp only [lobe_plus]
    let S:= lobe G true
    have he:S*S=S:=(lobe_sq ..).1
    let A:= mosaic G true false (tub (brix j G.count)) x
    change S*(S*A*S+(1-S)*A*(1-S))=(S*A*S+(1-S)*A*(1-S))*S
    have hx : S*(1-S)=0:=by rw [mul_sub,he,mul_one]; abel
    have ht:(1-S)*S=0:=by rw [sub_mul,he,one_mul]; abel
    rw [mul_add,add_mul,← mul_assoc S,← mul_assoc S S, he, ← mul_assoc S,← mul_assoc S (1-S),hx,zero_mul,zero_mul,mul_assoc _ S S,he,mul_assoc _ (1-S) S,ht,mul_zero]
  intro M N P G he
  have hh: Odd G.count.val:=he.symm ▸ hl
  let A:=cart N (tub (brix j G.count)); let W:=A ⊗ₖ (1:Op Slot); let S:=lobe G true
  have hu:A=plates N (brix j G.count):=cart_traded (cBrix j _ hh) N
  have hA : W*S=S*W:= by
    unfold S W lobe
    simp only [hu,op_kron_mul,one_mul,pilesP]
    suffices h : (plates N fun p=>brix j G.count p*sA true G.count)=plates N fun p=>sA true G.count*brix j G.count p by rw [h]
    apply pilesE; intro p hp hx; rw [brix,mul_assoc,slateW true j _ hp.1,← mul_assoc,slateT,mul_assoc]
  have hz:= doodle G true false (tub (brix j G.count)) (cBrix j _ hh).sumK
  unfold cloth; dsimp only; rw [hz,lobe_plus]
  change S*W*S+(1-S)*W*(1-S)=W
  have hs : S*S=S:=(lobe_sq ..).1
  simp only [mul_sub,sub_mul,mul_one,one_mul,←hA,mul_assoc _ S S,hs]; abel

-- flat inverse cost. det pivot.
def eix (L:Side) (j:ℕ)(p:Momentum): Stk L:= (brix j L p)⁻¹
include hj hl in
lemma bids : Pay (fun _: Unit=>1) fun _=> eix L j:=by
  have hp: Pay (fun _:Unit=>1) fun _=> brix j L:=by
    have ht:= (trimP L).times (W_quote j L hl); simp only [one_mul] at ht; exact ht
  have he: Firm (fun _:Unit=>1) fun _ p=>Matrix.det (brix j L p):= moderateFirm _ hp.determinant (fun p h=>isUnit_iff_ne_zero.mp (Matrix.isUnit_iff_isUnit_det _ |>.mp (IsUnit.mul (isUnit_iff_exists_inv.mpr ⟨_,(pointed L p h.1).2⟩) (lofty _ _ hj hl h))))
  unfold eix; simpa only [mul_one,inv_one,Matrix.inv_def,Ring.inverse_eq_inv'] using hp.adj.scale (hp.determinant.inv he (fun _=>one_pos))
include hl hj in
lemma eix_r (p:Momentum)(hp : p∈realCube zone)(x) (hx:p+reciprocal x∈realCube zone) : eix L j (p+reciprocal x)=eix L j p:=by rw [eix,eix,verifies j L hp x hx]
lemma Xgr {n m:Type*}[Fintype n][Fintype m][DecidableEq n][DecidableEq m](A:Op n)(h:IsUnit A): (A ⊗ₖ (1:Op m))⁻¹=A⁻¹⊗ₖ 1 := by
  have he : (A ⊗ₖ (1:Op m))*(A⁻¹⊗ₖ 1)=1:=by rw [op_kron_mul,(Fock.live h).1,one_mul, Matrix.one_kronecker_one]
  exact Matrix.inv_eq_right_inv he
variable {T:Script Male}
include hl hj in
lemma useK (p:Use j L @T): Save L false true (fun i _ _ G x=> (T i G x)⁻¹)∧ UnitAlways L @T:=by
  let B:Script Male:=fun i _ _ G x=> mosaic G false true (tub (eix G.count j)) x
  have hl': Save L false true @B:=by
    refine unanimous false true L hl (fun (_:Male) L=> tub (eix L j)) ?_
    obtain ⟨⟨σ,C,h,k,H⟩, _⟩:= tub_bill (bids j L hj hl) (fun i p hp x hx=> eix_r j L hj hl p hp x hx)
    simp only [mul_one] at H; exact ⟨σ,C,h,k,fun i a b=> H () a b⟩
  refine righted true false p.expense hl' (fun i c f G hg=>?_)
  have h : Odd G.count.val:=hg.symm ▸ hl
  have hh := paid (bids j G.count hj h) (fun i p hp x hx=>eix_r j G.count hj h p hp x hx) ()
  change _* mosaic _ _ _ _ _=_
  rw [p.fixed _ G hg,doodle G false true _ hh.sumK, op_kron_mul,one_mul,cart_traded hh,cart_traded (cBrix j G.count h),pilesP]
  rw [show (plates c fun x=> brix j G.count x * eix G.count j x)=(plates c fun _=> (1:Stk G.count)) from pilesE _ _ fun x hp hq=> (Fock.live (show IsUnit (brix j G.count x) from ((isUnit_iff_exists_inv.mpr ⟨_,(pointed _ _ hp.1).2⟩).mul (lofty _ _ hj h hp)))).1, piles1,Matrix.one_kronecker_one]
end YM.CF.Peaks

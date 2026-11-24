import YM.CF.Dial.Shawl
/-! Determinant correction. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable (j:ℕ)(L: Side)(ho:Odd L.val)(hj:Even j)(he:1≤j)(T:Script Male)(p:Use j L T)
def skirt:Chop Male:=fun _ _ _ G _=> lobe G true
def rack (T:Script Male):Chop Male:=fun i _ _ G x=> lobe G true*ticketT T true i G x.1*lobe G true
def recoilP(T: Script Male): Chop Male:=fun i _ _ G x=> lobe G true*star (ticketT T false i G (chargeB x).1)*lobe G true
section mat
variable {n:Type*}[Fintype n] [DecidableEq n]{A P:Op n}
lemma poleM (h:IsUnit A)(p:P*A=A*P): P*A⁻¹=A⁻¹*P:=by apply h.mul_left_cancel; rw [←mul_assoc,←p,mul_assoc,(live h).1,mul_one,←mul_assoc, (live h).1,one_mul]
lemma brimM (h:IsSelfAdjoint P)(p:P*A=A*P): P*star A=star A*P:=by nth_rw 1 2 [←h.star_eq]; rw [←star_mul,←p,star_mul]
end mat
include hj he p ho
lemma spinning : Still L fun G x=>∀ i,
    let B:=lobe G true; let W:=ticketT T true i G (unionP x.1); let V:=ticketT T false i G (unionP x.1); let K:=recoilP T i G (post x)
    Commute W B ∧ Clad B B W V K :=by
  have ht: Still L fun G x=>∀ i, IsUnit (T i G (unionP x.1)):=by
    obtain ⟨a,b,v,H⟩:=(useK j L hj ho p).2
    exact ⟨a,b,v,fun G he hv U h=> H G he hv _ (ambient a a b le_rfl h.covW)⟩
  apply ((marginH j L ho hj he T p).plus ht).forward; intro N F G hg x h i B W V K
  let Y:=T i G (unionP x.1); have hy:Commute B Y:= p.orients i G _; have hB:IsStarProjection B:=lobe_sq ..; have hp:B*B=B:=hB.1
  have hx: Commute B W:=by
    unfold W ticketT; rw [revI x.1]; exact (Commute.mul_right (poleM (h.2 i) hy) (Commute.refl _)).add_right (Commute.mul_right (brimM hB.isSelfAdjoint hy.eq) ((Commute.one_right _).sub_right (Commute.refl _)))
  have hv:star V*W=1:=(h.1 i true).bridge
  have hu: W*star V=1:=mul_eq_one_comm.mp hv
  have he:star V*B=B*star V:=by apply (live_of hu).mul_left_cancel; rw [←mul_assoc,hu,one_mul,←mul_assoc _ B (star V),←hx.eq,mul_assoc,hu,mul_one]
  have hh: K= B*star V*B:=by unfold K recoilP; rw [charge_p]; rfl
  have hQ:B*W*B=W*B:=by rw [hx.eq,mul_assoc,hp];
  have hG:B*star V*B=star V*B:=by rw [←he,mul_assoc,hp];
  rw [hh]; refine ⟨hx.symm,hB,hB,hv,?_,?_,?_,?_⟩
  · rw [hQ,hG,←mul_assoc,mul_assoc (star V) B W,hx.eq,← mul_assoc,hv,one_mul,hp]
  · rw [hQ,hG,←mul_assoc,mul_assoc W B (star V), ←he,←mul_assoc,hu,one_mul,hp]
  · rw [←mul_assoc,←mul_assoc,hp]
  rw [mul_assoc _ B B,hp]
lemma bonus : Land L skirt (rack T) (recoilP T):=by
  have hp: BoxD L (false,true) (false,true) skirt:= BoxD.marked (gradeBudget L false true); have hz : BoxD L (true,true) (true,true) skirt:= BoxD.marked (gradeBudget L true true)
  refine ⟨hp, (hp.chain (BoxD.marked (cup j L ho hj he p true).1)).chain hz,(hz.chain ((BoxD.marked (cup j L ho hj he p false).1).balm)).chain hp,fun i _ _ G h=>⟨plus_r G true,?_⟩,(spinning j L ho hj he T p).forward ?_⟩
  · unfold rack; rw [mul_assoc,plus_r,←mul_assoc, mul_assoc _ _ (helmC G),proffer G j L ho T i true p h hj,←mul_assoc, plus_r,cc_mul,cc_mul]; simp only [mul_assoc]
  intro N F G h U H i
  have hh: IsStarProjection (lobe G true):=lobe_sq G _
  exact ⟨hh, (by unfold rack skirt; rw [←mul_assoc,←mul_assoc,hh.isIdempotentElem.eq]),(H i).2.right⟩
end YM.CF.Dial

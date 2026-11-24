import YM.CF.Dial.Falcon
/-! Two coherent fields admit an exact, exponentially supported logarithm of the unnormalized branch-level (unsquared) wedge comparison. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable (j:ℕ)(L:Side)(ho:Odd L.val)(hj:Even j)(he:1≤j)(T:Script Male)(p:Use j L T)
variable(u:Bool)
def mateF(P:Script Male): Chop Male:=fun i _ _ G x=> P i G x.1
include ho he hj p
lemma marginH: Still L fun G x=>∀ i u, Along j L ho T u i G (unionP x.1):=by obtain ⟨a,t,v,V⟩:=joined j L ho hj he T p; exact ⟨a,t,v,fun G he hv U h i u=> V G he hv i U.1 h.covW u⟩
lemma brass: Land L (mateF (wh j L ho u)) (mateF (lake j L ho T u)) (mateF (pine j L ho T u)):=by
  obtain ⟨h,B,Z⟩:= cup j L ho hj he p u
  refine ⟨BoxD.marked Z,BoxD.marked ((Z.mul h).mul B),BoxD.marked (pine_funds j L ho hj he T p u),fun i _ _ G g=>?_,(marginH j L ho hj he T p).forward ?_⟩
  · unfold mateF; have ht :=board_q G j L ho i u g he; refine ⟨ht,?_⟩; rw [lake]; let z:= helmC G
    rw [mul_assoc, homeT G j i u he,←mul_assoc, mul_assoc _ (ticketT T u i G (vacancyY _ _).1) z,proffer G j L ho T i u p g hj,←mul_assoc, ht, cc_mul,cc_mul]; simp only [mul_assoc]
  intro N P G hx x g i
  let A:=wh j L ho u i G ((post x).1); have hh:= g i u; refine ⟨hh.beam,?_,hh.baseC⟩
  unfold mateF; rw [lake,←mul_assoc,←mul_assoc,show A*A=A from hh.beam.isIdempotentElem.eq]
lemma parentheses (n:ℕ)(hn:0<n)(h:Joy L (mateF (wh j L ho u)) (mateF (lake j L ho T u)) n):
 Still L fun G x=> ∀ i,
   let z:=post x; let P:=mateF (wh j L ho u); let A:=mateF (lake j L ho T u);
   let C:=P i G z; let W:=A i G z
   filled C (squareD G false z) ≠0 ∧
   acts (quant W) (filled (mateF (foal j u) i G z) (squareD G true z))= Complex.exp ((earnings P A n i G z).trace) • (filled C (squareD G false z)) :=by -- let implicit `P i G z`
  let Y:Chop Male:=mateF (wh j L ho u); let S:Chop Male:=mateF (lake j L ho T u)
  refine (((brass j L ho hj he T p u).taxes ho hn h).plus (marginH j L ho hj he T p)).forward ?_
  intro N P G hc x hp i z H B C W
  obtain ⟨hv, A, k⟩:= hp.1 i; refine ⟨k,?_⟩
  have h':= boom (court G j L ho T u i (hp.2 _ u)) (squareD G true z)
  have hm : (earnings H B n i G z).trace= _:= hv
  exact Eq.trans h' (by rw [hm]; exact A.symm)
end YM.CF.Dial

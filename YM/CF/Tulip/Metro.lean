import YM.CF.Tulip.View
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tulip
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
def funde (j:ℕ)(M:Male)(N:Side):Chin N→Op (Single N):=if M.val=1 then fun x=>projector (dome N x) else fun x=>projector (art N j M.val x)
def skewE (j:ℕ) (M:Male)(u: Bool)(N:Side):Chin N→Op (Single N):=fun x=>if u then funde j M N x else 1-funde j M N x -- edit
lemma funde_s (j)(hj:1≤j): Lively (funde j):=by
  have hx:Lively (fun (_:Male) N x=>projector (dome N x)):=by obtain ⟨a,c,e,h,k,r,v,T⟩:=dome_cap; exact certify h r (v:=v) fun i N hv=> T () N hv
  obtain ⟨a,c,e,h,k,r,v,T,S⟩:=hx.link (painter j hj).1
  exact ⟨a,c,e,h,k,r,v,fun i N hv=>by unfold funde; split; exact T i N hv; exact S i N hv⟩
lemma skew_s (j)(hj:1≤j)(u:Bool) : Lively (fun M N=> skewE j M u N):=by cases u; exact Lively.one.sub (funde_s j hj); exact funde_s j hj
lemma funde_q (j)(hj:1≤j): ∃ a:ℝ,0<a∧∃ v:ℕ, ∀ i:Male,∀ N:Side,v≤ N.val → ∀ U:Bkg (More N), Cube.Guard U a → IsStarProjection (funde j i N (profile U)) := by
  obtain ⟨e,he,n,H⟩:= (painter _ hj).2
  let d:= min e ((1/60:ℝ)/256); have hd: 0<d:=lt_min he (by norm_num)
  refine ⟨d,hd,n,fun i N hx U hg=>?_⟩; unfold funde; split
  · exact (Broad hd (by have h:d≤ _:= min_le_right ..; linarith) U hg).projection
  exact (H i N hx U (hg.shrink (min_le_left e _))).projection
lemma funde_flat (j)(hj:1≤j)(M: Male)(N: Side): funde j M N 1= cart N (tub (bar j M.val)) ⊗ₖ (1:Op Slot):=by
  rw [show cart N (tub (bar j M.val))= _ from cart_traded (A:=bar j M.val) (cBar j M.val true hj M.property) N, ← ptone N hj _ M.property]; unfold funde; split
  next he=> rw [he]; exact flatBand j hj _
  exact projector_one N hj M
lemma skew_flat (j)(hj:1≤j)(M:Male)(u:Bool)(N:Side): skewE j M u N 1= cart N (tub (bent u j M.val)) ⊗ₖ (1:Op Slot):=by
  cases u; swap; exact funde_flat j hj M N
  change 1-funde j M N 1= _
  have he: Reads (tub (bar j M.val)) (bar j M.val):=cBar j M.val true hj M.property
  have hx: plates N (bent false j M.val)=1-plates N (bar j M.val):=by rw [← piles1,pilesM]; rfl
  rw [funde_flat j hj M N,cart_traded he,cart_traded (cBar j M.val false hj M.property),hx]; ext ⟨x,a⟩ ⟨y,b⟩; simp [Matrix.one_apply,mul_ite]; grind
end YM.CF.Tulip

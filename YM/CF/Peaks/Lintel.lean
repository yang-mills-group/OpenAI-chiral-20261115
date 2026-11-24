import YM.CF.Peaks.Harbor
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable (j:ℕ)(L:Side)(ho:Odd L.val)(hj:Even j)(he:1≤j)(T : Script Male) (ht:Use j L @T)
variable {N P : Side}(G:Ratio N P)(hg:G.count=L)(M:Male)(u:Bool)
-- at vacuum any size. stencil open checks
include ho hj he ht hg
lemma crystal : pine j L ho @T u M G 1=dip j u M G 1:=by
  obtain ⟨h1,h2,h3,h4⟩:= illumine j L ho hj he G hg M u ht
  obtain ⟨h5,h6,h7,h8⟩:= illumine j L ho hj he G hg M (!u) ht
  let A:=foal j u M G 1; let B:= wh j L ho u M G 1
  let X:= lake j L ho @T u M G 1; let Y:= lake j L ho @T (!u) M G 1
  let U:=dip j u M G 1; let V:=dip j (!u) M G 1
  change X*U=B at h1; change U*X=A at h2; change A*U=U at h3; change U*B=U at h4
  rw [foil_neg] at h7; rw [wh_neg] at h5 h8; change Y*V=1-B at h5; change (1-A)*V=V at h7; change V*(1-B)=V at h8
  have hp:A*V=0:=by rw [sub_mul,one_mul] at h7; exact sub_eq_self.mp h7
  have hx:(1-A)*U=0:=by rw [sub_mul,one_mul,h3,sub_self]
  have hxy:X*V=0:=by unfold X; rw [lake,mul_assoc,hp,mul_zero]
  have hYX:Y*U=0:=by unfold Y; rw [lake,mul_assoc,foil_neg,hx,mul_zero]
  have hb:(X+Y)*(U+V)=1:=by rw [mul_add,add_mul,add_mul,hYX,h1,hxy,h5]; abel
  unfold pine; change A*(X+Y)⁻¹*B=U
  rw [Matrix.inv_eq_right_inv hb, mul_add,h3,hp, add_zero,h4]
lemma pine_stencil (D:List Axis)(hx:D.length+2≤j): let C:=cart N (tub (coverlet u j G.count M.val D));
  (sentry G D ⊗ₖ 1)*(pine j L ho @T u M G 1*hood G)= C⊗ₖ 1:=by
  intro C; let hL:Odd G.count.val:=hg.symm ▸ ho
  rw [crystal j L ho hj he T ht G hg,dip]; rw [show mosaic G true false _ 1= _ from doodle G true false _ (cBoards j G.count M.val u he hj M.property hL).sumK, shoulder, op_kron_mul,one_mul,op_kron_mul,one_mul, rideD G u j _ he hj hL M.property D hx] -- order
omit G M hg
lemma pine_funds : Save L true false (pine j L ho T u):=by
  obtain ⟨-,p,l⟩:= cup j L ho hj he ht u; exact (p.mul (seller j L ho hj he u T ht).1).mul l
lemma plank (i:Axis): Save L true true (fun (_:Male) c f G x=> foot G (trackM i x.1)):= by
  have hp:Lively (fun (_:Unit) N x=> @trackM N i x):= allsum _ _ fun a _=> step_live i a
  apply flowers (f:=fun (_:Male) _ x=> trackM i x); obtain ⟨a,r,e,l,k,q,v,H⟩:=hp; exact certify l q (v:=v) fun m N h=> H () N h

def grapple (D:List Axis): Script Male:=fun _ c f G x=> (D.map (fun i=> foot G (trackM i x.1)-1)).prod -- not used j etc
lemma grapple_f (D:List Axis): Save L true true (grapple D):=by -- needs omit j?
  induction D with
  | nil=> exact Save.one Male
  | cons a l ih=>exact ((plank j L ho hj he T ht a).sub (Save.one Male)).mul ih -- check
include G M hg
lemma track_still (i:Axis): @trackM P i 1= echo i ⊗ₖ (1:Op Slot):=by
  rw [← (profile_trivial (N:=More P)),step_profile,loveAt]; let E : Bkg (More P):=1; have hp:links E=1:=by ext ⟨x,b⟩; simp [E,links]; -- inspect
  change unityP P (Lat.shift matter (links E) _ i)=_; rw [hp]
  ext ⟨⟨x,a⟩,l⟩ ⟨⟨y,b⟩,w⟩; simp only [unityP,Matrix.submatrix_apply];
  change Lat.shift _ _ _ _ (x,a,l) (y,b,w)= _; have hh(i:Axis)(x:Site P): Lat.hop matter (1 : Bkg P) (anticut P) i x= seam (anticut P) x i • (1:Op (SpinIdx×Slot)) :=by rw [Lat.hop]; simp only [Lat.color,Pi.one_apply,map_one, show ∀ (A:Op Slot), A=A from fun _=>rfl]; rw [show (1:UNI Slot).val=(1:Op Slot) from rfl,Matrix.one_kronecker_one]
  by_cases g:a=b <;> by_cases h:l=w <;> by_cases f:x+step i=y <;> simp [Lat.shift,jump_apply,echo,hh,h,g,f, Matrix.one_apply,advance]
lemma sticks (D:List Axis): grapple D M G 1=sentry G D ⊗ₖ 1:=by
  induction D with
  | nil=> change 1=(1:Op _)⊗ₖ (1:Op Slot); exact Matrix.one_kronecker_one.symm
  | cons a D ih=>
    change (foot G (trackM a 1)-1)*grapple D M G 1= ((solo G (echo a)-1)*sentry G D)⊗ₖ (1:Op Slot)
    rw [track_still j L ho hj he T ht G hg M a,foot_stamp]
    rw [show (solo G (echo a) ⊗ₖ (1:Op Slot))-1=(solo G (echo a)-1) ⊗ₖ 1 by simpa using kronvec_sub G (solo G (echo a)) 1, ih, op_kron_mul,one_mul]
end YM.CF.Peaks

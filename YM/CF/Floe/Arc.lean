import YM.CF.Floe.Clock
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
variable {N:Side}{a b c d r e:ℝ}
open LedgerP
abbrev Δ:=IndexK
abbrev Vary(u:Axis)(z:Δ):FrameP z.1:= upx z.2 u
abbrev tagC(F:pMat)(i:Δ)(x:BayP i.1):=cc (F i (echoL x))
abbrev starL(F:pMat)(i:Δ)(x:BayP i.1):= star (F i (echoL x))
abbrev kM(j:Bool)(i:Δ):FrameP i.1 :=mark j
def haloB(u:Axis):pMat:= fun i x=>1-(1/2:ℝ) • (Vary u i x +starL (Vary u) i x)+spin i.1 Slot (gammaOp u)*((1/2:ℝ) • (Vary u i x-starL (Vary u) i x))
def massB:pMat:=fun i x=>spin i.1 Slot grading *(-1+∑ j:Axis, haloB j i x)
abbrev compB(i:Δ)(x:BayP i.1):=projector (massB i x)
abbrev gumD(P:pMat)(F:pMat) (i:Δ)(x:BayP i.1):Op (Model i.1):= P i x* F i x * tagC P i x
abbrev headP(j:Bool):pMat:= gumD compB (kM j)
abbrev stark:pMat:= headP false+ gumD (1-compB) (kM false)
def prospect:pMat:=1-starL (kM false)*stark
def mercy(z:Δ):FrameP z.1:= fun i=> (1-prospect z i)⁻¹*starL (kM false) z i
abbrev omenP:pMat:=headP true * mercy+(1-compB)-1
abbrev zκ:pMat:=headP false*starL (headP false)+(1-compB)-1
lemma vp(u:Axis):LedgerP (Vary u) true true:=keeps (a:=1) (b:=1) (fun i=> payroll (a:=1) i.2 u le_rfl) zero_lt_one zero_lt_one
lemma km(j:Bool): LedgerP (kM j) true false:=keeps (a:=1) (b:=1) (fun i=> mark_t (a:=1) (N:=i.1) j le_rfl) zero_lt_one zero_lt_one
lemma oy(A:Op SpinIdx): LedgerP (fun i x=> spin i.1 Slot A) true true:=keeps (a:=1) (b:=1) (fun i=>staticF ..) zero_lt_one zero_lt_one
lemma μLp: LedgerP massB true true:=by
 have hx (u:Axis): LedgerP (haloB u) true true:= plus (sub (identL _) (scale_t (plus (vp u) (mirrorL (vp u))) _)) (times (oy _) (scale_t (sub (vp _) (mirrorL (vp _))) _))
 apply times (oy _); apply plus (minus (identL _)); simp only [Axis, Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty, add_zero]; exact plus (hx _) (plus (hx _) (plus (hx _) (hx _))) -- tune nesting
section lift
variable(i:Δ)(x:Own i.1)
local notation "Y"=>skin x.val
@[simp] lemma kM_y(j:Bool): kM j i Y= Tenant.pairF j i x:=rfl
@[simp] lemma vMY(u): Vary u i Y=(anchor i x).T u:=by
 unfold Vary upx; apply congrArg (jump (advance u)); funext r; change _= _ • Lat.color matter _; unfold uhl; rw [show color matter (rough _ x (r,u))= color matter (x.val.1 (node r,u)) * _ from color_mul matter (x.val.1 _) (x.val.1 (node r+step u,u))]; rfl
@[simp] lemma star_my(F:pMat): starL F i Y=star (F i Y):=by unfold starL; rw [en]
@[simp] lemma tag_my(F:pMat):tagC F i Y=cc (F i Y):=by unfold tagC; rw [en]
@[simp] lemma mass_j: massB i Y=Kmat i x:=by
 unfold massB; change spin _ _ _*_= spin _ _ _*(-1+ ∑ j:Axis, (anchor i x).inc j); simp_rw [haloB,star_my,vMY]; rfl
@[simp] lemma comp_j: compB i Y= Pmat i x:=by unfold compB; rw [mass_j]; rfl
@[simp] lemma head_j(j): headP j i Y=body (Pmat i x) (pairF j i x):=by unfold headP gumD; rw [tag_my,comp_j,kM_y]; rfl
@[simp] lemma st_j: stark i Y=stage (Pmat i x) (pairF false i x):=by
 change headP false _ _+gumD _ _ _ _= _; rw [head_j,gumD,tag_my]; simp only [Pi.sub_apply,Pi.one_apply,comp_j,kM_y]; rfl
-- choose left inverse route
set_option maxHeartbeats 800000 in
lemma karma: ‖prospect i Y‖≤1/3:=by
 let W:=pairF false i x; let V:UNI (Model i.1):=⟨W,unit_each false i x⟩; let T:= stage (Pmat i x) W
 unfold prospect; simp only [Pi.sub_apply, Pi.one_apply,Pi.mul_apply,st_j,star_my,kM_y]; rw [← CStarRing.norm_coe_unitary_mul V]; change ‖W*(1-star W*T)‖≤_
 rw [mul_sub,mul_one, ←mul_assoc,show W*star W=1 from V.property.2,one_mul,norm_sub_rev]; exact tight ..
set_option maxHeartbeats 800000 in
@[simp] lemma mercy_c: mercy i Y= (stage (Pmat i x) (pairF false i x))⁻¹:=by
 let S:= stark i Y; let B:Op (Model i.1):= pairF false i x; have he: IsUnit S:= closeUnit (A:=S) (⟨B,unit_each false i x⟩:UNI (Model _)) ((by unfold S; rw [st_j]; exact (tight false i x).trans_lt (by norm_num))) -- tune
 let M:=prospect i Y; have hv: 1-M=star B*S:=by unfold M prospect; simp only [Pi.sub_apply,Pi.one_apply,Pi.mul_apply,star_my,kM_y]; exact sub_sub_cancel ..
 have hz:IsUnit (1-M):=by apply nearOne; rw [sub_sub_cancel]; exact (karma i x).trans_lt (by norm_num)
 unfold mercy; rw [←st_j,star_my,kM_y]; change (1-M)⁻¹*star B=S⁻¹
 calc _ = ((1-M)⁻¹*star B*S)*S⁻¹ :=by rw [mul_assoc (_ * _), (live he).1,mul_one]
      _ = _:=by rw [mul_assoc ((1-M)⁻¹),←hv,(live hz).2,one_mul]
@[simp] lemma omen_l: omenP i Y= (show Op (Model i.1) from beamX i x) - 1:=by unfold omenP; simp only [Pi.sub_apply, Pi.one_apply,Pi.mul_apply,Pi.add_apply,head_j,mercy_c,comp_j]; rfl
@[simp] lemma zκ_l: zκ i Y= (show Op (Model i.1) from weighX i x) - 1:=by unfold zκ; simp only [Pi.sub_apply, Pi.one_apply,Pi.mul_apply,Pi.add_apply,star_my,head_j,comp_j]; rfl
end lift
lemma σLp: LedgerP compB true true:= focal μLp (fun i x=> by rw [mass_j]; exact attends ..)
lemma hk(j:Bool): LedgerP (headP j) true false:= times (times σLp (km _)) (ccL σLp)
lemma lamLp: LedgerP prospect false false:=by
 let η:=sub (identL _) σLp; let p: LedgerP stark true false:= plus (hk false) (times (times η (km false)) (ccL η)); exact sub (identL _) (times (mirrorL (km false)) p)
lemma μCp: LedgerP mercy false true:=times (geom lamLp karma (by norm_num) (by norm_num)) (mirrorL (km _))
lemma ψOp:LedgerP (fun i x=>pencil (omenP i x)) true true:=logF (sub (plus (times (hk true) μCp) (sub (identL _) σLp)) (identL _)) (c:=1/2) (fun i x=>(show ‖omenP i (skin x.val)‖≤1/2 from (by rw [omen_l]; exact billR ..))) (by norm_num) (by norm_num)
lemma ψZp: LedgerP (fun i x=> pencil (zκ i x)) true true:= logF (sub (plus (times (hk false) (mirrorL (hk false))) (sub (identL _) σLp)) (identL _)) (c:=7/9) (fun i x=>(show ‖zκ i (skin x.val)‖≤7/9 from (by rw [zκ_l]; exact weighR ..))) (by norm_num) (by norm_num)
end YM.CF.Floe

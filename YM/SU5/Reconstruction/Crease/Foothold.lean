import YM.SU5.Reconstruction.Crease.BackLight
/-!
# Our transported angle `ll†`.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame.Clasp
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Picket
open scoped BigOperators Topology InnerProductSpace ComplexOrder
variable {H K D:Hilbert}(C: Clasp K H D)
def plume : H.Op:= C.l.comp C.l.adjoint
def shadow : H.Op := 1-C.plume
local notation "P"=> C.plume
local notation "R"=> C.shadow
lemma portAngle : P = C.Left.conjStarAlgEquiv C.angle:=by
 apply dense_cancel C.l C.p; ext1 x
 change C.l (C.l.adjoint (C.l x)) = (((C.Left.conjStarAlgEquiv C.angle)) (C.l x))
 rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,←C.left_done x, LinearIsometryEquiv.symm_apply_apply]
 -- tune lhs also rewrote
 rw [C.left_done x]
 change C.l (C.angle x)=_
 rw [← C.left_done]; apply congrArg (C.Left)
 exact DFunLike.congr_fun (show peel C.l * C.angle=C.angle*peel C.l by rw [angle, ←peel_sq,mul_assoc]) x
lemma plume_graph (x:H): P x=C.l (C.l.adjoint x):= rfl
lemma plume_self : IsSelfAdjoint P:= by
 unfold plume; change (C.l.comp C.l.adjoint).adjoint=_; rw [adjoint_comp,adjoint_adjoint]
lemma shadow_self : IsSelfAdjoint R:= by unfold IsSelfAdjoint shadow; rw [star_sub,C.plume_self.star_eq,star_one]
lemma through_self (A:H.Op)(p:IsSelfAdjoint A)(x y:H):inner ℂ (A x) y=inner ℂ x (A y):= by
 conv_lhs=> lhs; rw [show A=A.adjoint from p.symm]
 exact ContinuousLinearMap.adjoint_inner_left A _ _
lemma plume_inj : Injective P:=by
 intro x y h; apply ext_inner_left ℂ; intro z
 have t : C.l.adjoint x=C.l.adjoint y:= C.j h
 apply congrFun (a:=z) (C.p.equalizer (continuous_id.inner continuous_const) (continuous_id.inner continuous_const) ?_)
 funext w; change inner ℂ (C.l w) x=inner ℂ (C.l w) y; rw [← adjoint_inner_right, t, adjoint_inner_right]
lemma shadow_inj : Injective R:=by
 have h : Injective ( (1:K.Op)- C.angle:K.Op):= C.complement ▸ C.r.adjoint_comp_self_injective_iff.mpr C.k
 have he: C.shadow = C.Left.conjStarAlgEquiv (1-C.angle):=by rw [map_sub,map_one,shadow,portAngle]
 intro x y p; apply C.Left.symm.injective; rw [he,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] at p; exact h (C.Left.injective p)
lemma unites : P + R =1:=by unfold shadow; abel
lemma opponents : Commute P R:=by unfold shadow; exact (Commute.one_right _).sub_right (Commute.refl _)
lemma warmer (x:K): R (C.l x)= C.l (C.r.adjoint (C.r x)):=by
 have hp:= congrArg C.l (C.calculation x); rw [map_add] at hp; change C.l x-C.l (C.l.adjoint (C.l x))=_; apply sub_eq_iff_eq_add.mpr; rw [add_comm]; exact hp.symm
lemma formulates (x y:H)(p:P y=R x) : x=P (x+y) ∧ y=R (x+y):=by
 rw [map_add,map_add]
 constructor
 · have ht: P x+R x=x:= DFunLike.congr_fun C.unites x; rw [p,ht]
 have ht: P y+R y=y:= DFunLike.congr_fun C.unites y; rw [← p,ht]
-- tune
lemma transBeat (t:ℝ) : Commute P (Picket.boost C t):= by
 rw [Picket.boost,cLeft,portAngle]; exact (C.oneCabin (Commute.refl C.angle) (-t/Real.pi)).map C.Left.conjStarAlgEquiv.toStarAlgHom
lemma momentum (A B:H.Op)(F:D.Op) (h:C.Pass A F)(s:IsSelfAdjoint F)(v:B=A.adjoint)(x y:H)(p:P y=R x): P (B y)=R (A x):=by
 -- use x=P(x+y) from graph; get l with mirror;
 let u:= C.l.adjoint (x+y); have hx: C.l u=x:=(C.formulates x y p).1.symm; have hxy:C.l.adjoint y=C.r.adjoint (C.r u):= C.j (show _ from (by rw [← warmer, hx,←p]; rfl)); obtain ⟨u',d,e⟩:= h u
 have hv:C.r.adjoint (C.r u')=C.l.adjoint (B y):= by
   apply ext_inner_left ℂ; intro z
   obtain ⟨w,f,g⟩:=h z
   rw [adjoint_inner_right,e, ← through_self F s,← g,← adjoint_inner_right,← hxy,adjoint_inner_right,f,v,adjoint_inner_right,adjoint_inner_right]
 rw [←hx,←d,warmer,hv]; rfl
end YM.CrossedFrame.Clasp

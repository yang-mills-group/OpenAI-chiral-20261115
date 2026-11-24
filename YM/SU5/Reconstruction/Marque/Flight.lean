import YM.SU5.Reconstruction.Marque.Program
import YM.SU5.Reconstruction.Crease.Fountain
set_option autoImplicit false
noncomputable section
namespace YM.Marque
open Function Set Filter Metric NormedSpace ContinuousLinearMap Complex BridgeClub
open scoped ComplexOrder InnerProductSpace BigOperators Topology Classical Complex
variable {H:Hilbert} (u:Wander H.space) (a b:Bool)
abbrev Hue(b:Bool)(z:ℂ):= if b then star z else z
@[simp] lemma hue_yes(z:ℂ):Hue true z=star z:= rfl
@[simp] lemma hue_no(z:ℂ):Hue false z=z:= rfl
@[simp] lemma hue_mix(z:ℂ):Hue (a^^b) z=Hue a (Hue b z):=by cases a <;> cases b <;> simp
@[simp] lemma hue_duo(z:ℂ):Hue a (Hue a z)=z:=by simp[← hue_mix]
@[simp] lemma hue_real(z:ℝ): Hue a z = ↑z:= by cases a<;> simp
structure Fleet : Prop where -- must include arg
 plus (x y:H): u (x+y)=u x+u y
 conj (z:ℂ)(x:H):u (z • x)= Hue a z • u x
 innerP(x y:H):inner ℂ (u x) (u y)= Hue a (inner ℂ x y)
local notation "W"=>Wander H.space
variable {v u k:Wander H.space}{a b}{A B C:H.Op}
def Across (v:W)(A B:H.Op):Prop:=∀ x:H,B (v x)=v (A x)
lemma Fleet.one:Fleet (H:=H) 1 false:=⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
namespace Fleet
variable (p:Fleet (H:=H) v a)
include p
lemma times(h:Fleet u b):Fleet (H:=H) (u*v) (b^^a):= -- H inference
 ⟨fun x y=>by simp only [wander_mul,p.plus,h.plus],fun z x=> by simp only [wander_mul,hue_mix,h.conj,p.conj],fun x y=> by simp only [hue_mix,wander_mul,h.innerP,p.innerP] ⟩
lemma inv:Fleet (H:=H) v⁻¹ a:= ⟨(fun x y=>v.injective (by rw [wander_back,p.plus,wander_back,wander_back])), fun z x => v.injective (by rw [wander_back,p.conj,wander_back,hue_duo]), fun x y=> (Involutive.injective (hue_duo a)) (by rw [hue_duo,←p.innerP,wander_back,wander_back])⟩
lemma bases:v 0=0:= by
 apply add_left_cancel (a:=v 0); rw[←p.plus];simp
lemma normV (x:H): ‖v x‖= ‖x‖:= by rw [← dist_zero_right,← p.bases,v.isometry.dist_eq,dist_zero_right]
-- physical transformation resources
noncomputable def Form(A:H.Op):H.Op:=
 LinearMap.mkContinuous
  ({toFun:= fun x=>v (A (v⁻¹ x)), map_add':= fun x y=> by rw [p.inv.plus,map_add,p.plus], map_smul':=fun c x=>by simp only [RingHom.id_apply,p.inv.conj,map_smul,p.conj,hue_duo] }:H→ₗ[ℂ] H)
  ‖A‖ (fun x=> by change ‖v _‖≤_; rw [p.normV]; exact (p.inv.normV x) ▸ A.le_opNorm _)
lemma arr (A:H.Op): Across v A (Form p A) :=fun x=>by change v (A (v⁻¹ (v x)))=_; rw [wander_front]
lemma stars (h:Across v A B):Across v (star A) (star B):= by
 intro x; apply ext_inner_left ℂ; intro y; obtain ⟨y,rfl⟩:= v.surjective y
 change inner ℂ (v y) (B.adjoint _) = inner ℂ _ (v _); rw [adjoint_inner_right,h,p.innerP,p.innerP]; exact congrArg (Hue a) (adjoint_inner_right A y x).symm -- tune
lemma sub (x y:H):v (x-y)=v x-v y:= by rw [eq_sub_iff_add_eq,←p.plus]; simp
-- flight for exponential later
lemma asUnit (e:a=false) : ∃ f:H≃ₗᵢ[ℂ]H,∀ x:H,f x=v x:=⟨ { toFun:= v, invFun:= v.symm,left_inv:=v.symm_apply_apply,right_inv:=v.apply_symm_apply,map_add':=p.plus,map_smul':=fun z x=>by rw [p.conj,e];rfl, norm_map':= p.normV},fun _=>rfl⟩
end Fleet
namespace Across
variable (h:Across v A B)
lemma goesOne : Across (1:W) A A:=fun x=>rfl
lemma unique (h:Across v A B)(p:Across v A C):B=C:=by ext1 x; obtain ⟨t,rfl⟩:= v.surjective x; rw[h,p]
include h
lemma inv:Across v⁻¹ B A:=fun x=>v.injective (by rw [← h (v⁻¹ x),wander_back,wander_back]) -- tune 
lemma functor (p:Across u B C):Across (u*v) A C:=by intro x; change C (u (v x))= u (v (A x)); rw [p,h]
lemma multiply{C D:H.Op}(p:Across v C D):Across v (A*C) (B*D):=by intro x; change B (D (v x))= _; rw [p,h];rfl
lemma power (n:ℕ):Across v (A^n) (B^n):=by induction n with| zero=> rw [pow_zero,pow_zero]; exact fun x=>rfl| succ n e=>rw [pow_succ,pow_succ]; exact e.multiply h
lemma scale (p:Fleet v a) (z:ℂ):Across v (z • A) (Hue a z •B):=by intro x; rw [smul_apply,smul_apply,h,p.conj]
lemma adds{C D:H.Op}(p:Across v C D) (e:Fleet v a):Across v (A+C) (B+D):=by intro x; rw [add_apply,add_apply,p,h,e.plus]
end Across
-- Venue transport property
abbrev Conveys (u:W) (M N:Net H):Prop:=∀ A B:H.Op,Across u A B→(A∈ M ↔ B∈N)
namespace Conveys
variable {M N X:Net H}
lemma conjOf (p:Conveys v M N) (A:H.Op)(h:Fleet v a):A∈ M↔ h.Form A∈ N:=p _ _ (h.arr A)
lemma back (p:Conveys v M N): Conveys v⁻¹ N M:=fun x y h=> (p y x (by simpa only [inv_inv] using h.inv)).symm
lemma joins(p:Conveys v M N)(q:Conveys u N X)(f:Fleet v a):Conveys (u*v) M X:= by
 intro x y e; have g:= Fleet.arr f x; have hy:=p _ _ g; have hb:Across u (f.Form x) y:=by intro z; obtain ⟨t,rfl⟩:= v.surjective z; rw[g];exact e t
 exact hy.trans (q _ _ hb)
lemma first (M:Net H):Conveys 1 M M:= by intro A B p; rw [Across.unique p Across.goesOne]
end Conveys
-- linear isos from physical
open CrossedFrame Picket
variable (u:H.Op)(J:Flash H)
lemma hueInner(z y:H):inner ℂ y z=star (inner ℂ z y):= (inner_conj_symm (𝕜:=ℂ) y z).symm
-- package Pays

lemma paysPrice (p:Pays u) : ∃ f: Wander H.space, Fleet f false∧∀x:H,f x=u x:=by
 have h (x y:H):inner ℂ (u x) (u y)=inner ℂ x y:=by rw[← adjoint_inner_right]; exact congrArg _ (DFunLike.congr_fun p.1 y)
 let f: H≃ₗᵢ[ℂ] H:={ toFun:=u, invFun:=(star u:H.Op), left_inv:= DFunLike.congr_fun p.1, right_inv:= DFunLike.congr_fun p.2,map_add':=map_add u, map_smul':= map_smul u,norm_map':= fun x=> by change ‖u x‖=_; rw [@norm_eq_sqrt_re_inner ℂ,@norm_eq_sqrt_re_inner ℂ,h] }
 exact ⟨f.toIsometryEquiv, ⟨map_add u,map_smul u,h⟩,fun _=>rfl⟩
noncomputable def deal {u:H.Op}(p:Pays u) : Wander H.space:= (paysPrice u p).choose
lemma deal_fleet {u:H.Op}(p:Pays u): Fleet (deal p) false:= (paysPrice u p).choose_spec.1
lemma deal_at {u:H.Op}(p:Pays u)(x:H): deal p x=u x:= (paysPrice u p).choose_spec.2 x
lemma flashV : ∃ u:W,Fleet u true ∧ ∀x:H,u x=J.f x:=by
 let f:H≃ᵢ H:={toFun:=J.f,invFun:=J.f,left_inv:=J.twice,right_inv:=J.twice,isometry_toFun:= isometry_iff_dist_eq.mpr (fun x y=> by rw [dist_eq_norm,←map_sub,J.bill,←dist_eq_norm])} -- tune
 exact ⟨f,⟨map_add J.f,map_smulₛₗ J.f,fun x y=>(J.light x y).trans (hueInner ..)⟩,fun _=>rfl⟩
noncomputable def rain:= (flashV J).choose
lemma rainPrice: Fleet (rain J) true:= (flashV J).choose_spec.1
lemma rain_at(x:H): rain J x= J.f x:= (flashV J).choose_spec.2 x
lemma rain_mul: rain J*rain J=1:= by ext x; change rain J (rain J x)=x; rw [rain_at,rain_at,J.twice]
@[simp] lemma rain_inv : (rain J)⁻¹=rain J:=inv_eq_of_mul_eq_one_right (rain_mul J)
lemma rainAcross (A:H.Op): Across (rain J) A (J.shade A):=fun x=>by rw [rain_at,rain_at,J.shade_light]
end YM.Marque

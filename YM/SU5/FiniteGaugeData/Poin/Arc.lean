import YM.Mink.Boost
import YM.Mink.Poincare
import Mathlib.Analysis.SpecialFunctions.Arsinh
/-!
# Groups for POIN frame

 Euclidean group here `SO` as proper real isometries about origin. Same Coord units as release's Lorentz, not already postulated action on Φ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set Mink Mink.General Mink.Lorentz Real
open scoped Topology ContDiff NNReal InnerProductSpace
variable (g u:Mink.General) (L K:Mink.Lorentz)(x y:E4)
def North : Subgroup Mink.General where
 carrier := {g| stretch g=1 ∧ ∀ x:E4,‖walk g x‖=‖x‖}
 one_mem' := ⟨north,fun _=>rfl⟩
 mul_mem' H K:=⟨by rw [General.comp,H.1,K.1,one_mul],fun x=> by rw [walk_mul,H.2,K.2]⟩
 inv_mem' := by intro g h; change stretch g⁻¹=1∧∀ x, _= _; refine ⟨?_,fun x=>(h.2 (walk g⁻¹ x)).symm.trans (congrArg norm (retrace g x))⟩; rw [← one_mul (stretch g⁻¹),←show stretch g= _ from h.1, ← General.comp,mul_inv_cancel,north,h.1] -- tune motive
abbrev SO := ↥North
example : IsTopologicalGroup SO:=inferInstance
-- try Boo variables after Binders P.Body
local notation "b"=> basis timeAxis
abbrev Pin :Prop := Lorentz.act L b=b
lemma pin_iff : Pin L ↔ ∀ x,time (L.act x)=time x :=by
 constructor
 · intro h x
   have hh:= Lorentz.keeps L (b+x); rw [map_add,show L.act b=b from h] at hh; have he:= Lorentz.keeps L x; simp_rw [Mink.m] at hh he; simp only [clock_add,rest_add,roll_clock,roll_space,zero_add] at hh; linarith
 intro p; have he:=p b; rw [roll_clock] at he
 have h:= Lorentz.keeps L b; unfold Mink.m at h; rw [he,roll_clock,roll_space,norm_zero] at h; apply ext_by; rw [roll_space,←norm_eq_zero]; nlinarith [norm_nonneg (spatial (L.act b))]; rwa [roll_clock] -- tune
lemma nilBoost : ∃ e:Ray,∃ t:ℝ,∃ K:Lorentz,Pin K ∧ L=e.boost t*K:=by
 let z:=L.act b; let d:=spatial z; let H:=‖d‖; have hz:m z=1:=by unfold z; rw [Lorentz.keeps]; simp [m]
 have he:0<time z:=(strict_self z).mp ((stays L b).mpr ?_) |>.1
 swap; show b∈inside; simp [inside]
 have ht: time z = cosh (arsinh H):= (sq_eq_sq₀ he.le (cosh_pos _).le).mp (by rw [cosh_sq',sinh_arsinh]; unfold m at hz; linarith only [show time z^2-H^2=1 from hz])
 by_cases h:H=0
 · have hv:z=b:=by rw [h] at ht; apply ext_by; rw [roll_space]; exact norm_eq_zero.mp h; simpa using ht
   exact ⟨Ray.fromAxis 0,0,L,hv,by simp⟩
 have hp:0< H:=lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
 let e:Ray:=⟨H⁻¹ • d,by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]; exact inv_mul_cancel₀ h⟩
 let B:=e.boost (arsinh H); let K':Lorentz:=B⁻¹*L; have hf: B.act b=z:=by
    unfold B; rw [Ray.boost_at]; apply ext_by
    · rw [Ray.newSpace]; simp [Ray.along]; change H • (H⁻¹ • d)=_; rw [smul_smul,mul_inv_cancel₀ h,one_smul]
    rw [Ray.newClock]; simpa [Ray.along] using ht.symm -- maybe simpl cosh_arsinh
 refine ⟨e,arsinh H,K', ?_,?_⟩; exact (by unfold Pin K'; rw [Lorentz.act_mul]; change act _ z=b; rw [← hf]; exact starts B _); change L=B*(B⁻¹*L); group
-- orientation transforms.B.Matrix no assumption.An.
def polar (p:Pin L): SO := ⟨L.val,L.det,fun x=>by -- nested Subgroup proof cuts issue
    let y:=L.act x; change ‖y‖=‖x‖; have hx:=L.keeps x; apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1; have vz:=squares x; have e:time y=time x:= (pin_iff L).1 p x; have v:=squares y; unfold Mink.m at hx; dsimp only [y] at e; rw [e] at hx; unfold y at *; linarith [congrArg (·^2) e] ⟩
#print axioms nilBoost
#print axioms polar
namespace Flute
variable (e:Ray) (t s:ℝ)
def road(e:Ray): Coord := Mink.clockL.smulRight (position e.val 0) - e.alongL.smulRight (basis timeAxis)
def circleB : Coord:= (1:Coord)+ sin t • road e + (cos t-1) • e.scalesT
@[simp] lemma tt (x:E4): time (road e x) = -(e.along x):=by simp [road,sub_eq_add_neg]
@[simp] lemma ss (x:E4): spatial (road e x)=time x • e.val:=by simp [road,sub_eq_add_neg]
lemma ttake(t:ℝ):time (circleB e t x)= cos t*time x - sin t*e.along x:=by simp [circleB]; ring
lemma stake(t:ℝ):spatial (circleB e t x)=spatial x+ (sin t*time x+(cos t-1)* e.along x) • e.val:=by simp [circleB,add_smul,mul_smul,add_assoc]
lemma etake(t:ℝ):e.along (circleB e t x)= sin t*time x+ cos t*e.along x :=by unfold Ray.along; rw [stake]; simp [Ray.along,inner_add_left,inner_smul_left,e.property]; ring
lemma together(t v:ℝ): circleB e t* circleB e v= circleB e (t+v):=by
 ext1 x; change circleB e t (circleB e v x)=_; apply ext_by
 · simp_rw [stake,ttake,etake,add_assoc]; rw [← add_smul]; congr 2; rw [sin_add, cos_add]; ring
 rw [ttake,ttake,ttake,etake,cos_add,sin_add]; ring
@[simp] lemma lay : circleB e 0=1:=by ext1 x; simp [circleB]
def toll : General:=⟨circleB e t,circleB e (-t),by rw [together,add_neg_cancel,lay],by rw [together,neg_add_cancel,lay]⟩
@[simp] lemma told : walk (toll e t) x= circleB e t x:=rfl
@[simp] lemma rev : (toll e t)⁻¹=toll e (-t):= Units.ext rfl
lemma fits (t v:ℝ): toll e t*toll e v=toll e (t+v):= Units.ext (together e ..)
@[simp] lemma tiny : toll e 0=1:= Units.ext (lay e)
lemma meter : ‖circleB e t x‖=‖x‖:=by
 apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1; simp only [squares (circleB e t x),squares x]; rw [stake,ttake]; rw [norm_add_sq_real,norm_smul,Real.norm_eq_abs,e.property,mul_one,sq_abs,real_inner_smul_right]; rw [show inner ℝ (spatial x) e.val=e.along x from rfl]; linear_combination ((time x)^2+(e.along x)^2) * sin_sq_add_cos_sq t
lemma score : stretch (toll e t)=1:=by
 let D(u:ℝ):= stretch (toll e u); have hm: Lorentz.reverseL*(toll e t)*Lorentz.reverseL⁻¹= toll e (-t):= by
    apply Mink.General.ext; intro x; apply ext_by
    · simp [stake,Ray.along,sub_eq_add_neg,add_smul]; abel
    simp [ttake,Ray.along]
 have ht(u:ℝ):D u* D u= D (u+u):=by unfold D; rw [← General.comp, fits]
 have he:D (-t) =D t:=by unfold D; rw [← hm,General.comp,General.comp,mul_comm (General.stretch Lorentz.reverseL),mul_assoc,← General.comp (Lorentz.reverseL) _,mul_inv_cancel, General.north,mul_one]
 have hv:D t* D (-t)=1:= by unfold D; rw [← General.comp,fits,add_neg_cancel,tiny,north]
 have hs:= ht (t/2); rw [add_halves] at hs; rw [he] at hv; change D t=1; nlinarith [sq_nonneg (D (t/2))]
def moveB : SO:= ⟨toll e t,score e t,fun x=> meter x e t⟩ -- args lemma score maybe x included? no. 
#print axioms moveB
end Flute
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

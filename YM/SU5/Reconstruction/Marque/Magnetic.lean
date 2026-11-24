import YM.SU5.Reconstruction.Marque.Program
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Flow
open Function Set Filter Matrix Real Complex Picket
open Mink
open scoped Matrix MatrixGroups Topology InnerProductSpace Classical
variable (g h:Two)(x:E4)
local notation "A"=> Lorentz.act
local notation "ω"=> onWorld
local notation "ρ"=>Motion
-- rotations in 0,1 by any angle cos/sin
structure PlaneData (v:Two)(c s:ℝ):Prop where
   collar (x:E4): Motion v x 3=x 3 ∧ Motion v x 2=x 2
   ringXY (x:E4): Motion v x 0=c*x 0-s*x 1∧ Motion v x 1=c*x 1+s*x 0
lemma planes (c s:ℝ)(h:c^2+s^2=1):∃ v,PlaneData v c s:=by
 let T:= (c:ℂ)+(s:ℂ)*I; obtain ⟨y,q⟩:= IsAlgClosed.exists_pow_nat_eq T Nat.zero_lt_two
 have hx:normSq T=1:= by simp [T,normSq_apply,mul_re,mul_im]; linarith
 have ht:(y*star y:ℂ)=1:=by
    have hz:(normSq y)^2=1:=by rw [←map_pow,q,hx]
    have hw:normSq y=1:=by nlinarith [normSq_nonneg y]
    change y*(starRingEnd ℂ) y=_; rw [mul_conj,hw];rfl
 -- scoping
 have hz:y⁻¹=star y:= inv_eq_of_mul_eq_one_right ht; let v:= Units.mk0 y (left_ne_zero_of_mul_eq_one ht); let U:= Pole v
 have hy : val U=!![y, 0;0,star y]:=by unfold val U Pole pin v; dsimp; rw[hz]; rfl
 have hb(x:E4): ρ U x = WithLp.toLp 2 ![c*x 0-s*x 1, c*x 1+s*x 0,x 2,x 3]:=by
      apply visible; rw [atMotion]; unfold remit; rw [hy]; ext i j :1; fin_cases i <;> fin_cases j <;> simp [herm, Matrix.mul_apply, Fin.sum_univ_two]; -- to goals
      · change y * ( _ + _) * star y=_ + _; linear_combination ((x 3:ℂ)+(x 2:ℂ))*ht
      · unfold T at q; linear_combination ((x 0:ℂ)+(x 1:ℂ)* Complex.I)*q+(s:ℂ)*(x 1:ℂ)*Complex.I_sq
      · apply RingHom.injective (starRingEnd ℂ); simp; unfold T at q; linear_combination ((x 0:ℂ)+(x 1:ℂ)* Complex.I)*q + (s:ℂ)*(x 1:ℂ)*Complex.I_sq
      change star y * (_-_)*y=_-_; linear_combination ((x 3:ℂ)-(x 2:ℂ))*ht
 exact ⟨U, ⟨fun x=>by rw[hb];exact ⟨rfl,rfl⟩, fun x=>by rw [hb]; exact ⟨rfl,rfl⟩⟩⟩
private lemma point (x y:E4)(h0:x 0=y 0)(h1:x 1=y 1)(h2:x 2=y 2)(h3:x 3=y 3):x=y:=by ext i; fin_cases i <;> assumption
private lemma compass (x y:ℝ): ∃ c s:ℝ,c^2+s^2=1∧ c*x-s*y=0∧0 ≤ c*y+s*x:= by
   let t:=x^2+y^2; by_cases p:t=0; use 1,0; unfold t at p; refine ⟨?_,?_,?_⟩<;> nlinarith
   have hx:0<t:= by unfold t at *; exact lt_of_le_of_ne (by positivity) (Ne.symm p)
   let v:= Real.sqrt t; have hv:0<v:=by unfold v; positivity
   refine ⟨y/v,x/v,?_,?_,?_⟩ <;> field_simp <;> first| (solve|ring)| (have ht:x^2+y^2=v^2:=(Real.sq_sqrt hx.le).symm;nlinarith)
-- Rotate & fix clock
local notation "b"=> YM.basis clock
abbrev Preserves(g:Two):= Motion g b=b
private lemma nzB(i:Axis)(p:i≠3): YM.basis 3 i=0:=by simp [p]
local macro "xyzq" : tactic=> `(tactic| simp [show (0:Axis)≠3 from by decide,show (1:Axis)≠3 from by decide,show (2:Axis)≠3 from by decide,show (1:Axis)≠2 from by decide,show (0:Axis)≠2 from by decide,show (3:Axis)≠2 from by decide,Flow.clock])
private lemma keepPt{g:Two}{c s:ℝ}(p:PlaneData g c s): Preserves g:= point _ _ (by rw [(p.ringXY b).1]; xyzq) (by rw [(p.ringXY b).2]; xyzq) (p.collar b).2 (p.collar b).1
lemma proctor :∃ g:Two,Preserves g ∧ (Motion g x 0=0)∧ Motion g x 1=0∧ 0≤ Motion g x 2:= by
 obtain ⟨c,s,h,h0,-⟩:= compass (x 0) (x 1); obtain ⟨u,H⟩:=planes c s h
 let y:= ρ u x; have k:y 0=0:= (H.ringXY x).1.trans h0
 -- rotate similarly in yz by Nine X→ Z.POS: x→y? y→ z want y=0, z≥0. For second via Nine sends input w with x=y_z, y=y_y; want w_y=0,w_x≥0 by matrix.C.P.
 let Y:= ρ Nine⁻¹ y; have hx:= Motion_inv Nine y; have he:= Ninety Y
 have hp: Y 2=0:= by have h0:Motion Nine Y 0=0:= congrArg (fun x:E4=> x 0) hx |>.trans k; rw [he.2.1] at h0; exact neg_eq_zero.mp h0
 -- desired $c v+s u=0$. choose original compass x=v, y=u, sets C*v - s'*u where s=-s'. then other c*u+s'*v >=0
 obtain ⟨C,r,H1,z,w⟩:= compass (Y 1) (Y 0)
 obtain ⟨v,U⟩:= planes C (-r) (by simpa using H1)
 have hv(g:Two)(c s:ℝ)(e:PlaneData g c s):Preserves g:= keepPt e
 refine ⟨Nine*(v*(Nine⁻¹*u)),?_,?_,?_,?_⟩;
 · have he:(Motion Nine b)=b:=point _ _ (by rw [(Ninety ..).2.1]; xyzq) (Ninety ..).2.2.1 (by rw[(Ninety ..).2.2.2]; xyzq) (Ninety b).1
   simp only [Preserves,multiplies,hv u c s H, show ρ Nine⁻¹ b=b from (by nth_rw 1 [← he];rw [invMotion]), hv v C (-r) U, he]
 · simp only [multiplies]; change ρ Nine (ρ v Y) 0=_; rw [(Ninety _).2.1,(U.collar Y).2,hp,neg_zero]
 · simp only [multiplies]; change ρ Nine (ρ v Y) 1=_; rw [(Ninety _).2.2.1,(U.ringXY Y).2]; linarith
 simp only [multiplies]; change 0≤ρ Nine (ρ v Y) 2; rw [(Ninety _).2.2.2,(U.ringXY Y).1]; linarith
abbrev solves (g:Lorentz):Prop:=∃ v,onWorld v=g
lemma cheaper(g:Two)(k:Lorentz)(e:solves (ω g*k)): solves k:= by obtain ⟨v,hp⟩:=e; refine ⟨g⁻¹*v,mul_left_cancel (a:=ω g) ?_⟩; rw [←onWorld_mul]; simp[hp]
lemma pointwise_m (x:E4) : m x= (x 3)^2-(x 2)^2-(x 1)^2-(x 0)^2:= by
 unfold m time spatial; rw [←real_inner_self_eq_norm_sq,PiLp.inner_apply]; simp [Fin.sum_univ_castSucc,show timeAxis=(3:Axis) from rfl]; ring
-- tools sign basis extraction with explicit coefficients
variable (L:Lorentz)
lemma stick (i:Axis)(p:A L (YM.basis i)=YM.basis i)(x:E4):A L x i=x i:= by
 have hx:=L.keeps (x+YM.basis i); rw[map_add,p, pointwise_m, pointwise_m] at hx; have ht:=L.keeps x; rw[pointwise_m,pointwise_m] at ht
 have hh(r:Axis):r=0∨r=1∨r=2∨r=3:=by fin_cases r <;> decide
 rcases hh i with e|e|e|e <;> (
   subst i;
   simp (disch:=decide) [basis_eq] at hx <;> nlinarith) -- tune
lemma thin (x:E4)(p:x 0=0)(h:x 1=0)(e:x 2=0)(t:m x=1)(z:0≤ x 3): x=b:= by
 refine point _ _ ?_ ?_ ?_ ?_ <;> (simp (disch:=decide) [basis_eq,clock,p,h,e]; try decide) -- tune
 rw [pointwise_m,p,h,e] at t; nlinarith
lemma staff(v:SpaceAxis):(YM.basis v.castSucc) 3=0 ∧ m (YM.basis v.castSucc)=-1:= by fin_cases v <;> simp (disch:=decide) [basis_eq,pointwise_m]
lemma timelane : A L b ∈ inside ∧ m (A L b)=1:= by
 have hx:b=YM.basis timeAxis:= rfl
 rw [hx,Lorentz.keeps,Lorentz.stays]; exact ⟨by change ‖spatial _‖< _;simp, by simp [m]⟩
abbrev Fix(L:Lorentz)(i:Axis):Prop:=A L (YM.basis i)=YM.basis i
lemma supportCost(x:E4)(h:x∈ inside): ∃ t:ℝ, Picket.move clock 2 t x 2=0:= by
 have ht := (strict_self x).1 h|>.1; change 0<x 3 at ht; have hc:=lt_of_le_of_lt ((Ray.fromAxis 2).along_le x) (show ‖spatial x‖< time x from h); rw [Ray.onAxis] at hc; change |x 2|< x 3 at hc
 let v:=x 2/x 3; have hx:v∈ Ioo (-1:ℝ) 1:= abs_lt.mp ((abs_div ..).trans_lt (by rw [abs_of_pos ht]; exact (div_lt_one ht).mpr hc)) -- trans abs equality rewrites
 obtain ⟨y,he⟩:∃ y:ℝ,Real.sinh y / Real.cosh y = v:= ⟨Real.artanh v,(Real.tanh_eq_sinh_div_cosh _).symm.trans (Real.tanh_artanh hx)⟩
 refine ⟨-y,?_⟩; rw [eye_low (show (2:Axis)≠clock from by decide), Real.sinh_neg, Real.cosh_neg]; unfold clock; linarith [(div_eq_div_iff (Real.cosh_pos y).ne' ht.ne').mp (show _=x 2/x 3 from he)]
macro "steer" : tactic=> `(tactic| apply point <;> first| assumption| simp (disch:=decide) [basis_eq,Flow.clock] at *)
lemma plainCase (p:Fix L 3)(hb:Fix L 2)(y:Fix L 0):L=1:=by
 let w:=A L (YM.basis 1); have hw:w 2=0∧ w 3=0 ∧ w 0=0:= ⟨(stick L _ hb _).trans (by simp (disch:=decide) [basis_eq]),(stick L _ p _).trans (by simp (disch:=decide) [basis_eq]),(stick L _ y _).trans (by simp (disch:=decide) [basis_eq])⟩ -- decide ℝ?
 have hx:m w=m (YM.basis 1):= L.keeps _; rw[pointwise_m,pointwise_m,hw.2.1,hw.2.2,hw.1] at hx
 let x(i:Axis):ℝ:= if i=1 then w 1 else 1; have he(i:Axis):A L (YM.basis i)= x i • YM.basis i:= by
    have hk(i:Axis):i=0∨i=1∨i=2∨i=3:=by fin_cases i<;> decide
    rcases hk i with z|z|z|z <;> subst i
    · unfold Fix at y; simpa (disch:=decide) [x] using y
    · change w=x 1 • _; refine point _ _ ?_ ?_ ?_ ?_ <;> simp (disch:=decide) [hw.1,hw.2.1,hw.2.2,x,basis_eq] -- tune
    · unfold Fix at hb; simpa (disch:=decide) [x] using hb
    · unfold Fix at p; simpa (disch:=decide) [x] using p
 let e:= (EuclideanSpace.basisFun Axis ℝ).toBasis; have hq:LinearMap.toMatrix e e (A L).toLinearMap= Matrix.diagonal x:= by
    have ht(i:Axis):e i=YM.basis i:= by simp[e,basis] -- tune
    ext i j; rw[LinearMap.toMatrix_apply,ht]; change e.repr (A L _ ) i= _; rw [he,← ht, map_smul]; by_cases z:i=j<;> simp [Matrix.diagonal_apply,z,Finsupp.single_apply,Ne.symm] -- tune
 have h:=L.det; rw [← LinearMap.det_toMatrix e, hq,Matrix.det_diagonal] at h; simp (disch:=decide) [x,Fin.prod_univ_succ] at h;
 apply Lorentz.ext; intro u;
 have hh:(A L).toLinearMap=LinearMap.id (R:=ℝ):= by
    apply e.ext; intro i; simp [e]; rw [show EuclideanSpace.single i 1= YM.basis i from rfl]; rw [he]; simp [x,h]
 change L.act.toLinearMap u = _; rw [hh]; rfl
lemma flock(p:Fix L 3)(q:Fix L 2): solves L:= by
 let g:= A L (YM.basis 0)
 obtain ⟨c,s,h,h0,h1⟩:= compass (g 1) (g 0); obtain ⟨v,U⟩:= planes c (-s) (by simpa using h)
 let u:= ω v*L; have hp:Fix u 2:= by
    unfold Fix u; rw[Lorentz.act_mul,q,onWorld_at]; apply point <;> first|(exact (U.collar _).2)|(exact (U.collar _).1)|rw[(U.ringXY _).1]|rw[(U.ringXY _).2]
    all_goals simp (disch:=decide) [basis_eq]
 have hz:Fix u 3:=by unfold Fix u; rw[Lorentz.act_mul,p,onWorld_at]; exact keepPt U
 let V:=A u (YM.basis 0)
 have hv:V= ρ v g:= by unfold V u g; rw [Lorentz.act_mul,onWorld_at]
 have e:V 1=0:= by rw[hv,(U.ringXY _).2, neg_mul,←sub_eq_add_neg]; exact h0
 have hy:0≤V 0:=by rw[hv,(U.ringXY _).1, neg_mul, sub_neg_eq_add]; exact h1
 have H:Fix u 0:=by
    have h3: V 3=0:= (stick _ _ hz _).trans (by simp (disch:=decide) [basis_eq]); have h2:V 2=0:= (stick _ _ hp _).trans (by simp (disch:=decide) [basis_eq]); change V=_; refine point _ _ ?_ ?_ ?_ ?_ <;> simp (disch:=decide) [e,h3,h2,basis_eq]; have hy':= u.keeps (YM.basis 0); change m V=_ at hy'; simp (disch:=decide) [pointwise_m,e,h2,h3,basis_eq] at hy'; rcases hy' with e|e <;> linarith
 exact cheaper v L ⟨1,onWorld_one.trans (plainCase _ hz hp H).symm⟩
lemma roomAll(h:Fix L 3): solves L:= by
 let x:=A L (YM.basis 2); obtain ⟨p,e,q,z,w⟩:=proctor x
 refine cheaper p L (flock _ ?_ ?_)
 · unfold Fix; rw[Lorentz.act_mul,h,onWorld_at]; exact e
 have hv:Fix (ω p*L) 3:= by unfold Fix; rw [Lorentz.act_mul,h,onWorld_at]; exact e
 have ht: A (ω p* L) (YM.basis 2)=ρ p x:= by unfold x; rw[Lorentz.act_mul,onWorld_at]
 have he:ρ p x 3=0:= by rw [← ht]; rw [stick _ _ hv]; simp (disch:=decide) [basis_eq]
 have hz:m (ρ p x)=m (YM.basis 2):= ht ▸ (ω p*L).keeps _; simp (disch:=decide) [pointwise_m, he,q,z,basis_eq] at hz
 unfold Fix; rw [ht]; apply point <;> simp (disch:=decide) [basis_eq,q,z,he]; rcases hz with e|e <;> linarith
-- physical coverage
lemma onWorld_onto : Function.Surjective onWorld:= by
 intro L; let t:=A L b; obtain ⟨p,h,w,z,-⟩:= proctor t
 let x:= ρ p t; have ht:A (ω p*L) b=x:= by rw [Lorentz.act_mul,onWorld_at]
 obtain ⟨s,hs⟩:= supportCost x (ht ▸ (timelane _).1);
 let V:=Tuning (s/2); have e(y:E4): Motion V y= Picket.move clock 2 s y:= by unfold V; rw [motionZ,show 2*(s/2)=s by ring]
 let g:=ω V * (ω p*L); have he:A g b= Picket.move clock 2 s x:= by unfold g; rw[Lorentz.act_mul, ht,onWorld_at,e]
 refine cheaper p L (cheaper V _ (roomAll g ?_)); change A g b=b; apply thin
 · rw [he,Picket.others _ _ _ (by decide) (by decide)]; exact w
 · rw [he,Picket.others _ _ _ (by decide) (by decide)]; exact z
 · rw [he]; exact hs
 · exact (timelane g).2
 exact ((strict_self _).1 (timelane g).1).1.le
end YM.Marque.Flow
#print axioms YM.Marque.Flow.onWorld_onto

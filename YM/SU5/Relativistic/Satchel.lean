import YM.SU5.Relativistic.Cocoa
import YM.SU5.Relativistic.Inopportune
/-! # V origin seeds and sector. Linear exact symbol application. -/
set_option autoImplicit false
set_option maxHeartbeats 540000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet.Sorcerer
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free Asymptotics
open Laurent Bloch Fir Jill Ember Shore UnitAddTorus Fock Lat UpStart
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker ENNReal
attribute [local instance] opCStarAlgebra
local notation "I"=>Complex.I
local notation "φ"=>2*Real.pi
private lemma spin_u (x:Bin)(v:Cover)(z:Cover): mode (tmap (x+stem v)) z = mode (tmap x) z:=by rw [map_stem,mode_phase,mode_periodic,mul_one]
lemma leap (v z:Cover){g:Bin→ℂ}(t:Pouch g)(K:ℂ):
    chipPay (fun x=> K*mode (tmap x) v*g x) z = K*chipPay g (z+v):=by
 let f:=fun x=> K*mode (tmap x) v*g x; have hp:Pouch f:=fun x y=>by unfold f; rw [spin_u,t]
 change (∫ a:Dish,mFourier (- -z) a*waffles f a ∂globe Axis)=_*(∫ a:Dish,mFourier (- -(z+v)) a*waffles g a ∂globe Axis)
 rw [← integral_const_mul]; simp only [neg_neg]; refine integral_congr_ae (Eventually.of_forall fun i=>?_); obtain ⟨x,rfl⟩:=ingot_s i; dsimp only; rw [hp.wishes,t.wishes, mFourier_add, flashes x v]; unfold f; ring
lemma leap_zero (v:Cover){k:ℂ}(p:v≠ 0): chipPay (fun _=>k) v=0:=by
 let D:= mFourier (d:=Axis); -- orth
 have he:= orthonormal_iff_ite.mp (orthonormal_mFourier (d:=Axis)) (0:Cover) v; rw [if_neg p.symm] at he; unfold mFourierLp at he; rw [ContinuousMap.inner_toLp] at he; rw [mFourier_zero] at he; -- tune
 have hp:(∫ a:Dish,D v a ∂globe Axis)=0:=by simpa only [D,ContinuousMap.one_apply,map_one,mul_one, one_mul] using! he -- includes conj orientation
 change (∫ a:Dish,D (- -v) a*k ∂globe Axis)= _; rw [neg_neg,integral_mul_const,hp,zero_mul]
local notation "C" x => mFourier x
private lemma chip_add (z:Cover){X Y:Bin→ℂ}(x:Pouch X)(y:Pouch Y)(p:Continuous X)(q:Continuous Y): chipPay (fun t=> X t+Y t) z=chipPay X z+chipPay Y z:=by
 change (∫ a:Dish, mFourier (- -z) a*(waffles X a+waffles Y a)∂globe Axis)= (∫ a:Dish,mFourier (- -z) a*waffles X a∂globe Axis) + _; simp_rw [mul_add]; exact integral_add (((mFourier _).continuous.mul (toCream x p)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (((mFourier _).continuous.mul (toCream y q)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
lemma mode_smooth (v:Cover) : ContDiff ℝ ω (fun x=>mode (tmap x) v):=by unfold tmap mode; apply contDiff_iff_contDiffAt.mpr; intro i; fun_prop
lemma sparrow_at (x:Bin): sparrow 1 x= 1/2- 1/4 * (mode (tmap x) (step TA)+mode (tmap x) (-step TA)):=by
 have he: mode (tmap x) (step TA)=Complex.exp (↑(x TA)*I):=by
    unfold mode; rw [sum_eq_single TA]; congr 1; simp [tmap,mul_comm]
    · intro i _ g; simp [g]
    simp
 have ht: mode (tmap x) (-step TA)=Complex.exp (-(↑(x TA)*I)):=by
    unfold mode; rw [sum_eq_single TA]; congr 1; simp [tmap,mul_comm]
    · intro i _ g; simp [g]
    simp
 rw [he,ht]; unfold sparrow; push_cast; have hp:=Complex.cos_two_mul_eq_one_sub (↑(x TA)/2:ℂ); rw [show (2:ℂ)*(↑(x TA)/2)=↑(x TA) by ring] at hp; simp only [Complex.cos,neg_mul] at hp; linear_combination hp/2
private lemma rise_mul (d:ℕ) (x:Bin) : sparrow (d+1) x=sparrow 1 x*sparrow d x:=by unfold sparrow; rw [Nat.mul_add,mul_one,pow_add,mul_comm]
lemma spar_zone (d:ℕ)(v:Cover)(p: chipPay (sparrow d) v≠0): v∈ box d:=by
 induction d generalizing v with
 | zero=>
    by_cases x:v=0; · rw [x]; apply box_test.mpr; simp
    rw [show sparrow 0=fun _=>1 from funext (fun _=>by simp [sparrow]),leap_zero v x] at p; contradiction
 | succ d ih=>
    let f(i:Cover)(t:ℂ)(x:Bin):= t*mode (tmap x) i*sparrow d x
    let R:= (2:ℂ)⁻¹; let T:= (-((4:ℂ)⁻¹)); let u:Cover:= step TA
    have F(i t): Pouch (f i t):=fun x y=>by unfold f; rw [spin_u,sieved]
    have G(i t):Continuous (f i t):= (continuous_const.mul (mode_smooth i).continuous).mul (sats d).continuous
    rw [show sparrow (d+1)=fun x=> f 0 R x + f u T x+ f (-u) T x from (by funext x; rw [rise_mul,sparrow_at]; unfold u T R f; simp; ring), chip_add v (show Pouch (fun x=> f 0 R x + f u T x) from (fun x y=>congrArg₂ (·+·) (F 0 R x y) (F u T x y))) (F (-u) T) ((G 0 R).add (G u T)) (G (-u) T), chip_add v (F 0 R) (F u T) (G 0 R) (G u T)] at p -- simpa only
    by_contra q
    have hx(i:Cover)(t:ℂ)(x:i∈box 1):chipPay (f i t) v=0:=by
       rw [show chipPay (f i t) v=_ from leap i v (g:=sparrow d) (sieved d) t]; apply mul_eq_zero_of_right; by_contra z; obtain ⟨g,h⟩:=box_test.mp (ih _ z); have ht:=box_test.mp x; apply q; refine box_test.mpr ⟨fun i=>?_,fun i=>?_⟩
       · have hv:= g i; have he:= ht.2 i; simp only [Pi.add_apply] at hv; omega
       have hv:= h i; have he:= ht.1 i; simp only [Pi.add_apply] at hv; omega
    have he: u ∈ Lattice.box 1∧ -u∈ Lattice.box 1:=by
       simp only [box_test]; refine ⟨⟨fun i=>?_,fun i=>?_⟩,⟨fun i=>?_,fun i=>?_⟩⟩ <;> by_cases h:i=TA <;> simp [u,h]
    apply p; rw [hx 0 R (by apply box_test.mpr; simp),hx u T he.1,hx _ T he.2,zero_add,zero_add]

lemma allT (x:Bin) : ∃ (k:Behind)(t:ℝ),x=tack k t:=by
 obtain ⟨e,h⟩:=tack_equiv ℝ; obtain ⟨⟨k,t⟩,rfl⟩:=e.surjective x; exact ⟨_,_,h _ _⟩
variable {v:Cover}{d:ℕ}(x:Bin)
def countMe (v:Cover)(d:ℕ): Bin→ℂ:=fun x=> (chipPay (damper d) v)⁻¹ *mode (tmap x) v* sparrow d x
def Minty (v:Cover)(d:ℕ)(x:Bin): Ket SpinIdx:= countMe v d x • acts (1-zen (tough x)) (basisKet (0:SpinIdx))
def mintedK(v:Cover)(d:ℕ)(i:SpinIdx)(x:Bin):= (Minty v d x).ofLp i
lemma mintedMe(i:SpinIdx):Pouch (mintedK v d i):=fun x z=>by unfold mintedK Minty; rw [graze]; unfold countMe; rw [spin_u,sieved]
private lemma costs (i:SpinIdx): mintedK v d i x = countMe v d x*((if i=0 then 1 else 0)-zen (tough x) i 0):=by
 unfold mintedK Minty; simp only [WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul,basis_act,Matrix.sub_apply,Matrix.one_apply]
lemma ferret(i:SpinIdx){k:ℕ}(p:2*(1+k)+2≤2*d): ContDiff ℝ (↑k) (mintedK v d i):=by
 let S(x:Bin):= (zen (tough x) : Op SpinIdx); let l(x:Bin):= sparrow d x
 have he:ContDiff ℝ (↑k) (fun x=> l x*S x i 0):=by
    unfold S zen; simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,mul_sum]; simp_rw [←mul_assoc]; apply ContDiff.sum; intro j _; exact ((parade d k j p).mul contDiff_const).mul contDiff_const -- tune
 let f(x:Bin):= (chipPay (damper d) v)⁻¹* mode (tmap x) v
 rw [show (mintedK v d i) = fun x=> f x*(l x*(if i=0 then 1 else 0) - l x*S x i 0) from (by funext x; rw [costs]; unfold S l f countMe; ring)]
 exact (contDiff_const.mul ((mode_smooth v).of_le le_top)).mul ((((sats d).of_le le_top).mul contDiff_const).sub he)
lemma atPlus (i:SpinIdx)(p:i∈plusHalf):mintedK v d i x = (if i=0 then countMe v d x else 0):=by
 rw [costs]; obtain ⟨u,t,rfl⟩:= allT x; have hp:= fell_upper p u t; unfold fell heatLine at hp; rw [neg_eq_zero] at hp; rw [hp,sub_zero]; split_ifs <;> simp_all
lemma upperBill (i:SpinIdx)(p:i∈plusHalf)(n:Cover)(t:chipPay (mintedK v d i) n≠0): n+v∈ box d:=by
 by_cases h:i=0; · rw [show mintedK v d i=_ from funext (fun x=> (atPlus (v:=v) (d:=d) x i p).trans (if_pos h)), show chipPay (countMe v d) n=_ from leap v n (sieved d) _] at t; exact spar_zone d (n+v) (right_ne_zero_of_mul t)
 apply (t ?_).elim; rw [show mintedK v d i=fun _=>0 from funext fun x=> (atPlus x i p).trans (if_neg h)]; change (∫ x:Dish,mFourier (- -n) x*(0:ℂ)∂globe Axis)=_; simp -- tune
lemma payoff (f:chipPay (damper d) v ≠0) : chipPay (mintedK v d 2) 0=1:=by
 let F:= chipPay (damper d) v; rw [show mintedK v d 2 = fun x=> F⁻¹*mode (tmap x) v* damper d x from ?_,leap v 0 (lilt d),zero_add,inv_mul_cancel₀ f]
 funext x; obtain ⟨k,t,rfl⟩:= allT x; rw [costs,if_neg (by decide),zero_sub]; rw [show -(zen (tough (tack k t)) 2 0)=_ from face_value k t]; unfold F damper countMe; unfold faceR heatLine; ring -- UA tune
end YM.CF.Crest.Sleet.Sorcerer
#print axioms YM.CF.Crest.Sleet.Sorcerer.payoff

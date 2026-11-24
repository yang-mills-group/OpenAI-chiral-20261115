import YM.SU5.FiniteGaugeData.ArchiveK.Ghost
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local instance] opCStarAlgebra
namespace Midway
open Violas GramK LightK
variable {G:E4≃ₗᵢ[ℝ] E4}{D c:ℕ}(p:Space3)(K:ZephyrG G D c)(L:FilterK) (q w:ℕ)
local notation "T"=> Stamp q w
local notation "∆"=> depthG G
local notation "E"=> ‖p‖
local notation "ϖ"=> actor K q w
local notation "F"=> pulseG G p
local notation "Γ"=> emitX
abbrev lamp (D q w:ℕ)(p:Space3) (i:Stamp q w):ℂ:= tLab q w D i p * ((basset D p)^i.2.val:ℝ) -- error coer.
def levelE (q D:ℕ)(p:Space3):ℝ:= Real.exp (-64*q*D*‖p‖)
def axisGap (i j:Stamp q w):E4:= emitX (actor K q w i true - actor K q w j false)
local notation "A"=> axisGap K q w
lemma lampEq (i j:Stamp q w): rise F (axisGap K q w i j)= ((levelE q D p):ℂ)*(lamp D q w p i * star (lamp D q w p j)):=by
 rw [iron_q]; let u:= ϖ i true; let v:= ϖ j false; let x:=inner ℝ p (songQ (D:ℝ) (ground i.1)); let y:=inner ℝ p (songQ (D:ℝ) (ground j.1)); have ht: crestG G p (A i j)=x-y:=by
    unfold axisGap; rw [emit_sub]; unfold crestG; rw [inner_sub_right]; rw [show inner ℝ _ (emitX (actor K q w i true))= _ from collar K p q w i true, show inner ℝ _ (emitX (actor K q w j false))=_ from collar K p q w j false]; -- tune arguments
 have hv: depthG G (A i j)=beadY q D i.2.val+beadY q D j.2.val:= by unfold axisGap; rw [emit_sub]; unfold depthG; rw [inner_sub_right]; rw [show inner ℝ _ (emitX (actor K q w i true))= _ from flagplus K q w i true, show inner ℝ _ (emitX (actor K q w j false))= _ from flagplus K q w j false]; simp
 rw [ht,hv]; let b : ℝ:= basset D p; change _=((levelE q D p):ℂ)*(coastE x*((b^(i.2.val):ℝ):ℂ)*star (coastE y*((b^j.2.val:ℝ):ℂ))); rw [star_mul,coast_inv,sub_eq_add_neg,coast_add]; let z:= -(64:ℝ)*q*D*E; let ℓ:= -(D:ℝ)*E; let a:= i.2.val; let c:= j.2.val; have hp: -‖p‖*(beadY q D i.2.val+beadY q D j.2.val) = z+ a*ℓ + c*ℓ:= by unfold ℓ z a c beadY basetime; push_cast; ring
 rw [hp,Real.exp_add,Real.exp_add,Real.exp_nat_mul,Real.exp_nat_mul]; have he (x:ℝ):star (x:ℂ)=(x:ℂ):=Complex.conj_ofReal _; rw [he]; change coastE x*coastE (-y)*(((Real.exp z * b^a * b^c):ℝ):ℂ)= (((Real.exp z:ℝ):ℂ))*((coastE x*((b^a:ℝ):ℂ))*(((b^c:ℝ):ℂ)*coastE (-y))); push_cast; ring
local notation "Qν"=> garnet G L
def marketL (p:Space3)(i j:Stamp q w) :ℂ:= garnet G L p *rise (pulseG G p) (axisGap K q w i j)
def pulseQ (x:Ket (Stamp q w))(p:Space3):ℂ:=∑ i: Stamp q w,x i*star (lamp D q w p i)
def gemHW (i j:Stamp q w):ℂ:=∑ k∈L.s,L.f k * shear G (axisGap K q w i j+emitX k)
def modelK : Op (Stamp q w):= Matrix.of (gemHW K L q w)
local notation "ϒ"=> marketL K L q w -- ordering p variable?
#check @pulseQ
#check @marketL
@[fun_prop] lemma lamp_c(i:Stamp q w): Continuous (fun p=> lamp D q w p i):=by unfold lamp tLab; fun_prop
@[fun_prop] lemma pulseQ_c(x:Ket (Stamp q w)): Continuous (pulseQ (D:=D) q w x):=by unfold pulseQ; fun_prop
@[fun_prop] lemma note_c(x:Ket (Stamp q w))(v:Zpo w): Continuous (fun p=> kNote D q w p x v):=by unfold kNote; fun_prop
local notation "Ψ"=> pulseQ (D:=D) q w
include K
lemma babeEq (x:Ket (Stamp q w)) (i:Zpo w): let v:Ket (Zpo w):= WithLp.toLp 2 (fun j=> kNote D q w p x j); let t(p:Space3):= p+arrowX D w i; pulseQ (D:=D) q w x (t p) = (ract (WicketL D w p) v).ofLp i:=by
 intro v t; rw [R_at]; unfold pulseQ lamp; rw [Fintype.sum_prod_type]; rw [Finset.sum_comm]; unfold WicketL Matrix.mulVec dotProduct; refine Finset.sum_congr rfl fun j _=>?_ ; -- tune star.Power.App.
 unfold tLab t; simp_rw [star_mul,turner p i K.unitC,show ∀ x:ℝ, star (x:ℂ)=(x:ℂ) from Complex.conj_ofReal]; change ∑ i':Pix q,x (i',j)* _= ((basset D (p+arrowX D w i):ℝ):ℂ)^j.val*kNote D q w p x j; unfold kNote; push_cast; rw [mul_sum]; refine Finset.sum_congr rfl fun x _=>?_ ; ring
-- `gas` camera.
abbrev songm(x:Ket (Stamp q w))(p:Space3):= ((garnet G L p).re * levelE q D p)*‖pulseQ (D:=D) q w x p‖^2
def needLaunch(K:ZephyrG G D c)(L:FilterK)(q w:ℕ) : Prop:= ∀ i j:Stamp q w,∀ k∈L.s,20< depthG G (axisGap K q w i j + emitX k)
local notation "MK"=> modelK K L q w
lemma bbl (x:Ket (Stamp q w))(t:needLaunch K L q w): Integrable (songm (G:=G) (D:=D) L q w x) ∧ gas (modelK K L q w) x=∫ p,songm (G:=G) (D:=D) L q w x p := by
 let f:= fun i j:Stamp q w=> fun p:Space3=> marketL K L q w p i j
 have he(i j) : Integrable (f i j):= (garnet_tee G (A i j) L (t i j)).1; have hx(p:Space3): gas (helm f p) x=songm (G:=G) (D:=D) L q w x p:= by
    let Q:= garnet G L p; let Y:=Q*((levelE q D p):ℂ); let lam := lamp D q w p
    refine (chordB lam Y (helm f p) (fun i j=>?_ ) x).trans ?_; swap; · unfold Y; rw [Complex.re_mul_ofReal]; rfl
    change (marketL K L q w p i j) = Y* (lam i*star (lam j)); unfold lam marketL Y Q; rw [lampEq,←mul_assoc] -- tune f not present
 have hb: (modelK K L q w)=stageK (μ:=MeasureTheory.volume) f Set.univ:=by apply Matrix.ext; intro i j; unfold stageK; rw [Matrix.of_apply,setIntegral_univ]; exact (garnet_tee G (A i j) L (t i j)).2.symm
 rw [hb]; refine ⟨(money_I f he x).congr (Eventually.of_forall hx),?_⟩; simp_rw [← hx]; exact (receipt f he Set.univ x).trans (by rw [setIntegral_univ])
#print axioms bbl
lemma lit_cost (i:Stamp q w): ‖lamp D q w p i‖ ≤ 1:=by unfold lamp; rw [norm_mul,show ‖tLab q w D i p‖=1 from aim_cash .., one_mul]; unfold basset; rw [norm_real,Real.norm_of_nonneg (pow_nonneg (Real.exp_pos _).le _)]; exact pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by exact neg_nonpos.mpr (Nat.cast_nonneg _)) (norm_nonneg _)))
lemma lapping (x: Ket (Stamp q w)): ‖pulseQ (D:=D) q w x p‖ ≤ (Violas.page (Stamp q w):ℝ)*‖x‖:=by
 refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i: Stamp q w=>‖x‖) (fun i t=>?_)).trans (le_of_eq (by simp [page]))); rw [norm_mul,norm_star]; apply (mul_le_of_le_one_right (norm_nonneg _) (lit_cost p K q w i)).trans; apply ?_ -- tune norm_le
 -- Euclid coordinate
 have he:=norm_inner_le_norm (𝕜:=ℂ) (basisKet i) x; rw [basis_inner] at he; simpa using he
local notation "Η"=> needLaunch K L q w
lemma launch_budget : ∀ᶠ q:ℕ in atTop, needLaunch K L q w := by
 let T'(q' : ℕ):ℝ:=32*q'*D; have he: Tendsto T' atTop atTop:= ((tendsto_natCast_atTop_atTop (R:=ℝ) |>.const_mul_atTop (by norm_num : (0:ℝ)<32)).atTop_mul_const (show 0<(D:ℝ) from Nat.cast_pos.mpr K.unitC)); let f(k:Cover):= depthG G (Γ k); filter_upwards [(eventually_all_finset L.s).mpr (fun k _=> he.eventually_gt_atTop (20-f k))] with q r i j k h
 let u:=actor K q w; let s:=depthG G (axisGap K q w i j); rw [show depthG G (axisGap K q w i j+_)=s+f k from inner_add_right ..]; have hm(v:Zpo w): T' q ≤ beadY q D v.val:=by unfold beadY basetime T'; push_cast; nlinarith only [show 0≤(v.val:ℝ)*D by positivity]; -- tune
 have hh: s= beadY q D i.2.val + beadY q D j.2.val:=by unfold s depthG axisGap; rw [emit_sub,inner_sub_right]; change ∆ _-∆ _= _; rw [flagplus K q w,flagplus K q w]; simp
 have hp := r k h; rw [hh]; linarith only [hp,hm i.2,hm j.2, show 0≤T' q from (by unfold T'; positivity)]
-- opacity.Strict.Career crossing SSI.Basis read weights.
#print axioms launch_budget
end Midway
end YM.CF.Window.ArchiveK

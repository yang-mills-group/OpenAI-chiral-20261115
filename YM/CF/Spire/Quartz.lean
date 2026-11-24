import YM.CF.Spire.Lane
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Scroll
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I n:Type*}[Fintype I][DecidableEq I][LinearOrder n][Fintype n](U:UNI n)(b r:Bool)
-- lift on operators & states; scalar from sea phase; independent of interpolation
abbrev tourP (F: FC n):= if r then theta U (windX b F) else sings b (quantU U) F
def oculus :Wave n→ Wave n:=fun v=> if r then acts (screenM U).val (dove true (dove b v)) else acts (quantU U).val (dove b v)
lemma oo_globe (x y:Wave n): inner ℂ (oculus U b r x) (oculus U b r y)=cSignX (b.xor r) (inner ℂ x y):=by unfold oculus; cases r<;>simp only [Bool.false_eq_true, ite_false, ite_true, act_unit_inner,dove_dot]; simp; cases b <;> simp [cSignX]
lemma oo_norm(x:Wave n):‖oculus U b r x‖=‖x‖:=by
 have h:= oo_globe U b r x x; rw [←sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),← inner_self_eq_norm_sq (𝕜:=ℂ),← inner_self_eq_norm_sq (𝕜:=ℂ),h]; cases b.xor r; rfl
 rw [inner_self_eq_norm_sq_to_K]; simp [cSignX]
lemma oo_scale(x:Wave n)(c:ℂ):oculus U b r (c•x)=cSignX (b.xor r) c • oculus U b r x:=by unfold oculus; cases r<;>simp only [Bool.false_eq_true,ite_false,ite_true, dove_scale,map_smul]; simp; cases b<;>simp [cSignX]
lemma oo_by(A: FC n)(x:Wave n): oculus U b r (acts A x)=acts (tourP U b r A) (oculus U b r x):=by
 unfold oculus tourP; cases r<;> simp only [Bool.false_eq_true,ite_true,ite_false, dove_acts, Fock.swivel]; rfl; rfl
lemma tour_line (P Q:Op n)(h:IsStarProjection P)(g:sings b U P=swapX r Q):tourP U b r (lineOp P)=lineOp Q:=by
 cases r; swap
 · let X:=windX b P; change twist _ (cc (windX b _))=_; rw [win_lace b h]; have ht:IsStarProjection X:=by cases b; exact h; exact ccProj h
   have hh:cc (lineOp X)=lineOp (cc X):=win_lace true ht
   change twist (screenM U) (cc (lineOp X))=_; rw [hh,screenM,twin,← twist_left (ccProj ht),cc_cc,←line_twist,invFilm,twin,map_sub,map_one,rankPhase]
   congr 1; rw [show twist U X=1-Q from g]; abel
 change sings b (quantU U) _= _; rw [singT, win_lace b h, ←line_twist,← singT,g]; rfl
abbrev glaze (q:Wave n):ℂ:= inner ℂ q (oculus U b r q)
def arum (q:Wave n)(x:Wave n):= (glaze U b r q)⁻¹ • oculus U b r x
variable {q:Wave n}
lemma arum_act(x q:Wave n)(A: FC n): arum U b r q (acts A x)=acts (tourP U b r A) (arum U b r q x):=by rw [arum,arum,oo_by,map_smul]
lemma arum_scale(q x:Wave n)(c:ℂ):arum U b r q (c•x)=cSignX (b.xor r) c • arum U b r q x:=by rw [arum, arum,oo_scale,smul_comm]
variable (S:Finset n)(p:Sea (cutM S) q)(t:sings b U (cutM S)=swapX r (cutM S))
include p t
lemma glaze_act:oculus U b r q = glaze U b r q • q:=by
 let v:= oculus U b r q; change v=_; nth_rw 1 [show v=acts (lineOp (cutM S)) v from ?_]; exact p.scalar (cutM_idp _) v
 rw [←tour_line U b r _ _ (cutM_idp S) t,← oo_by U b r, p.1]
lemma gazeN: ‖glaze U b r q‖=1:=by have h:= congr_arg norm (glaze_act U b r S p t); rw [oo_norm,norm_smul,p.2,mul_one] at h; exact h.symm
lemma arum_norm(x:Wave n):‖arum U b r q x‖=‖x‖:=by rw [arum,norm_smul,oo_norm,norm_inv,gazeN U b r S p t]; simp
lemma arum_globe(x y:Wave n):inner ℂ (arum U b r q x) (arum U b r q y)=cSignX (b.xor r) (inner ℂ x y):=by
 rw [arum,arum,inner_smul_left,inner_smul_right,oo_globe,←mul_assoc]; have h:=scale_unit_self (c:=(glaze U b r q)⁻¹) (by rw [norm_inv,gazeN U b r S p t, inv_one]); change star _*_*_=_; rw [h,one_mul]
lemma arum_self:arum U b r q q=q:=by rw [arum,glaze_act U b r S p t,inv_smul_smul₀ _]; exact norm_pos_iff.mp (by rw [gazeN U b r S p t]; simp)
omit p t
lemma win_thunk(C: Op n):windX b (seedR S C)=seedR S (windX b C):=by
 unfold seedR; rw [win_c,show cSignX b (2:ℂ)⁻¹=(2:ℂ)⁻¹ from (by cases b; rfl; norm_num [cSignX]),win_a]; have he (A:Op n)(f:n→FC n)(h:∀ i,windX b (f i)=f i): windX b (dyad A f f)=dyad (windX b A) f f:=by
   unfold dyad; rw [win_sum]; apply sum_congr rfl; intro i _; rw [win_sum]; apply sum_congr rfl; intro j _; rw [win_c,win_m,h,h]; cases b<;> rfl
 rw [he _ takeF (fun i=>by rw [takeF,win_s, win_up]),he _ put (win_up b)]; simp only [win_m,win_s, win_cut]
include p
lemma arum_no {C D:Op n} (k:sings b U (cutM S)=cutM S)(H:congrC U (windX b C)=D)(e : filled (cutM S) C=q)(h:filled (cutM S) D=q): arum U b false q (pairWave C)=pairWave D:=by
 let W:=oculus U b false; have ht: W (pairWave C)=pairWave D:=by rw [show W _=acts (quantU U).val (dove b (pairWave C)) from rfl,win_duo]; change acts (quant U.val) _=_; rw [pair_cov]; exact congrArg pairWave H
 have hv:=congr_arg W e
 have hh:W q=q:=by
   rw [←hv,filled]; unfold W; rw [oo_by,tour_line U b false (cutM S) (cutM S) (cutM_idp _) k, show oculus U b false _= _ from ht]; exact h
 rw [arum, glaze, show oculus U b false q=q from hh,inner_self_eq_norm_sq_to_K,p.2]; simp only [one_pow, map_one,Complex.ofReal_one,inv_one,one_smul]; exact ht -- tune
include t
lemma arum_pair (C D:UNI n)(e: C.valᵀ= -C.val)(u:D.valᵀ= -D.val)(H: Commute (cutM S) C.val)(T:Commute (cutM S) D.val)(x:filled (cutM S) C.val=q)(y:filled (cutM S) D.val=q)(V:congrC U (windX b C.val)=D.val): arum U b r q (pairWave C.val)=pairWave D.val:=by
 cases r; exact arum_no U b S p t V x y
 have hv: twist U (cutM Sᶜ)=cutM S:=by rw [dim_cut,map_sub,map_one,show twist U (cutM S)=1-cutM S from ?_]; abel; rw [singT,win_cut] at t; exact t
 have hz:(windX b C.val)ᵀ= -(windX b C.val):=by rw [show (windX b C.val)ᵀ=windX b C.valᵀ from (by cases b <;> rfl),e,win_n]
 rw [show pairWave C.val=acts (exp (seedR S C.val)) q from ?_, arum_act, arum_self U b true S p t]; change acts (theta U (windX b (exp (seedR S C.val)))) q=_
 rw [whisper,win_thunk]; have hp (A: FC n) :theta U (exp A)=exp (theta U A):=by rw [theta, show cc (exp A)=_ from whisper true A, breeze_exp]; rfl -- tune
 rw [hp,theta_seed S U _ hv hz,V,ripe S D u T]; rw [filled,cutLine,cut_oneAct] at y; exact congrArg _ y.symm -- tune
 rw [ripe S C e H]; rw [filled,cutLine,cut_oneAct] at x; exact congrArg _ x
end YM.CF.Spire

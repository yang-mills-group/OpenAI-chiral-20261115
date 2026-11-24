import YM.SU5.Velvet.LowTide
import YM.SU5.FiniteGaugeData.Pannier.Veldt
/-!
 # Tilt costs with arbitrary unit CAR rolls. Use `Yep` on actual p.n.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 190000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Velvet
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
open Function Filter NormedSpace Metric Fock Flare Finset Pannier.Chancel Pannier.Damask
attribute [local instance] opCStarAlgebra
variable {n:Type*} [LinearOrder n][Fintype n][Nonempty n]{P T:Op n}{z:ℝ}
-- tilt pronounces any `use`
def readW (T:Op n)(z:ℝ)(b:Bool)(x:Ket n) : Ket n := acts (castV T (if b then z⁻¹ else z)) x
def readB(T:Op n)(z:ℝ)(t: Token n) := creed t.val.1 (readW T z t.val.1 t.val.2)
/-- conjugated operators. Open because scalar, singular piece; no analytic. -/
def modifyB(T:Op n)(z:ℝ)(A:FC n):= quant (castV T z) * A * quant (castV T z⁻¹)
def flowCost (z:ℝ):= z⁻¹*(2+z^2+(z⁻¹)^2)
lemma flow_pos(p:0<z):0<flowCost z:=by unfold flowCost; positivity
lemma pushV (h:IsStarProjection T)(c:0<z): quant (castV T z)* quant (castV T z⁻¹)=1:= by rw [←quant_mul,cast_back h c,quant_one]
lemma crew_law (h:IsStarProjection T)(p:0<z)(x:Ket n)(t:Bool): quant (castV T z)*creed t x=creed t (readW T z t x)* quant (castV T z):=by
 cases t; · exact quant_create ..
 let Y:= castV T z; let W:= castV T z⁻¹; change quant Y * remove x=remove (acts W x)*quant Y; rw [quant_ann,cast_shine h,←act_mul,cast_back h p,act_one]
lemma modifies_creed (h:IsStarProjection T)(p:0<z)(x:Ket n)(t:Bool): modifyB T z (creed t x)=creed t (readW T z t x):=by unfold modifyB; rw [crew_law h p,mul_assoc,pushV h p,mul_one]
lemma tide_pond (A:FC n)(h:IsStarProjection T)(p:0<z): quant (castV T z)*A=modifyB T z A* quant (castV T z):=by unfold modifyB; rw [mul_assoc (quant _*A),mul_eq_one_comm.mp (pushV h p),mul_one]
lemma hurt (h:IsStarProjection T)(p:0<z)(t:z≤1): ‖castV T z‖≤ flowCost z ∧ ‖castV T z⁻¹‖≤ flowCost z:=by
 let A(x:ℝ):= 1+x^2; have ht(x):‖gate T x‖≤ A x:=by unfold gate; apply (norm_add_le ..).trans; rw [norm_smul,Real.norm_of_nonneg (sq_nonneg _)]; exact add_le_add (h.norm_le _) (mul_le_of_le_one_right (sq_nonneg _) (h.one_sub.norm_le _))
 unfold castV flowCost; rw [norm_smul,norm_smul, inv_inv,Real.norm_of_nonneg (inv_nonneg.mpr p.le),Real.norm_of_nonneg p.le]; constructor
 · exact mul_le_mul_of_nonneg_left ((ht _).trans (by unfold A; linarith [sq_nonneg z⁻¹])) (inv_nonneg.mpr p.le)
 exact mul_le_mul (t.trans ((one_le_inv₀ p).mpr t)) ((ht _).trans (by unfold A; linarith [sq_nonneg z])) (norm_nonneg _) (inv_nonneg.mpr p.le)
lemma wave_opy(B:FC n)(k:Wave n): ‖acts B k‖≤ ‖B‖*‖k‖:=by nth_rw 1 [← Matrix.l2_opNorm_toEuclideanCLM B]; exact (acts B).le_opNorm _
lemma token_le (b:Bool) (x:Ket n):‖x‖≤‖creed b x‖:=by
 suffices hp: ‖x‖≤‖create x‖ by cases b; exact hp; exact hp.trans_eq (norm_star _).symm
 apply le_trans (b:=‖acts (create x) (vacuum n)‖)
 · have ht:=snow x (vacuum n); simp only [vacuum_take,norm_zero,zero_pow (by decide : (2:ℕ)≠0),add_zero,show ‖vacuum n‖=1 from (by unfold vacuum; simp [basisKet]),one_pow,mul_one] at ht; apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1; exact ht.ge
 exact (wave_opy (create x) (vacuum n)).trans_eq (by rw [show ‖vacuum n‖=1 from (by unfold vacuum; simp [basisKet]),mul_one])
lemma reader_price (h:IsStarProjection T)(v:z≤1)(p:0<z)(u:Token n): ‖readW T z u.val.1 u.val.2‖ ≤ flowCost z:=by
 unfold readW; apply (opy ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) ((token_le u.val.1 u.val.2).trans u.property)).trans; split; exact (hurt h p v).2; exact (hurt h p v).1
lemma crew_turn (h:IsStarProjection T)(p:0<z)(L:List (Token n)): quant (castV T z) * rollC use L= rollC (readB T z) L*quant (castV T z):=by
 induction L with
 | nil=> simp [rollC]
 | cons i L ih=>
    let Q:=quant (castV T z); let W:=rollC (readB T z) L; change Q*(use i * rollC use L) = (readB T z i * W)*Q; rw [← mul_assoc,show Q*use i=readB T z i*Q from crew_law h p _ _,mul_assoc,ih,mul_assoc]
lemma credits (h:IsStarProjection T)(p:0<z)(t:z≤1)(L:List (Token n)): ‖rollC (readB T z) L‖ ≤ flowCost z ^ L.length:=by
 induction L with
 | nil=> simp [rollC]
 | cons i L ih=>
    rw [List.length_cons,pow_succ']; apply (norm_mul_le ..).trans; exact mul_le_mul ((cost_pe ..).trans (reader_price h t p i)) ih (norm_nonneg _) (flow_pos p).le
-- basic quantity evaluation; for use in marks
variable {S:Finset n}{y x:Wave n}
lemma wager (h:Sea (cutM S) y)(p:0<z)(L:List (Token n))(Q:FC n)(x:Wave n):let T:=cutM S; let W:=castV T z
 inner ℂ (acts (star Q) y) (acts (rollC use L) x)=((ante T z:ℝ):ℂ)* inner ℂ y (acts (modifyB T z Q*rollC (readB T z) L*quant W) x) :=by
 intro T W; let D:=ante T z • quant W; obtain ⟨(g:star D=D), (q: acts D y=y)⟩:= free_ante S p y h
 rw [act_inner]; nth_rw 1 [←q, ←g]; rw [act_inner,←act_mul,←act_mul]; let Y:=ante T z; let U:=modifyB T z Q; unfold D; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rw [Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,act_smul, inner_smul_right,tide_pond Q (cutM_idp S) p,mul_assoc (modifyB _ _ _),crew_turn (cutM_idp S) p, ←mul_assoc]; rfl
lemma issue (e:IsStarProjection P)(p:0<z)(v:z≤1)(h:Sea (cutM S) y)(t: Sea P x) (Q:FC n):let T:=cutM S
 Yep (flowCost z) (acts (star Q) y) x (‖modifyB T z Q‖ * Real.exp (trade P T z)):=by
 let T:=cutM S; let W:=castV T z; let M:=modifyB T z Q; change Yep _ _ _ (‖M‖ * _); intro l; let D:= ‖rollC (readB T z) l‖; let k:ℝ:=flowCost z ^l.length
 rw [wager h p,norm_mul,Complex.norm_real,Real.norm_of_nonneg (show 0≤ante (cutM S) z from Real.exp_pos _|>.le),trace_price e (cutM_idp _) p v x t,act_mul];
 let X:=acts (quant W) x; let Y:=ante T z; let R:=rollC (readB T z) l; change Y*‖inner ℂ y (acts (M*R) X)‖ ≤ ‖M‖*(Y*‖X‖)*k
 rw [act_mul, show ‖M‖ * (Y*‖X‖) * k= Y * (‖M‖* (k* ‖X‖)) by ring]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _|>.le); apply (norm_inner_le_norm y _).trans; rw [h.2,one_mul]; exact (wave_opy ..).trans (mul_le_mul_of_nonneg_left ((wave_opy ..).trans (mul_le_mul_of_nonneg_right (credits (cutM_idp _) p v _) (norm_nonneg _))) (norm_nonneg _))
end YM.CF.Velvet
#print axioms YM.CF.Velvet.issue

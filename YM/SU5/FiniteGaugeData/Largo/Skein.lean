import YM.SU5.FiniteGaugeData.Largo.Sweep
import Mathlib.LinearAlgebra.Matrix.SchurComplement
set_option autoImplicit false
set_option maxHeartbeats 160000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory
open scoped Topology BigOperators Pointwise ENNReal Matrix
variable (o:Rim)(p:Slab o)(t u v:ℤ)(j k:SpinIdx)
abbrev conduct (f:ℝ→Momentum)(x:ℝ)(t:ℤ)(j k:SpinIdx):ℂ:= Complex.exp (t*(Complex.I*x)) * (-zen (f x)) j k
def Tempo (F:ℝ→Momentum)(t u:ℤ)(i j:SpinIdx):ℂ:= chamber (fun r=> conduct F r (t-u) i j)
local notation "ℳ" => Tempo (fun r=> melody (floorPin o r))
local notation "τg" x:max=> conduct (fun r=> melody (floorPin o r)) x
-- Finite version effective symbol. approximations are to continuous hash. Room support uses `t-u` where upper-lower. seam phases not included (buy via cut signs embedding).
def berth (o:Rim)(m N:Side) (t u:ℤ)(i j:SpinIdx):ℂ:= approach (fun x=> conduct (fun r=> mixL 4 m (floorPin o r)) x (t-u) i j) N
private lemma dualCont : Continuous (fun x:ℝ×Momentum => Complex.exp (t*(Complex.I*x.1)) * (- Fir.zen x.2) j k):= by unfold Fir.zen; simp_rw [Matrix.neg_apply,Matrix.sum_apply,Matrix.smul_apply]; fun_prop
include p
lemma hutC : ContinuousOn (fun x:ℝ=> conduct (fun r=> melody (floorPin o r)) x t j k) bright:=by
 have hm:ContinuousOn (fun y:ℝ=> (melody (floorPin o y):Momentum)) bright:= by
    refine continuousOn_pi.mpr fun i=> ?_; let g(y:ℝ):=(o,y); rw [show (fun x:ℝ=> melody (floorPin o x) i)=(fun x:Rim×ℝ=> melody (floorPin x.1 x.2) i) ∘ g from rfl]; exact (inSession i).comp (by unfold g; fun_prop) (fun u v=> (show (o,u)∈ Foyer from ⟨p,abs_le.mpr v⟩))
 let f:= fun x:ℝ×Momentum => Complex.exp (t*(Complex.I*x.1)) * (- Fir.zen x.2) j k; change ContinuousOn (fun x=>f (x, melody (floorPin o x))) _; simpa only [Function.comp_def,id] using (dualCont t j k).continuousOn (s:=Set.univ)|>.comp (continuousOn_id.prodMk hm) (fun i _=>Set.mem_univ _)
lemma recurr_b : (ℳ) (t+u) u 0 2+(ℳ) (t+u) u 1 3= (-2*Complex.I)*literal o p (-t):=by
 let f(x):= melody (floorPin o x); let g(a b)(x:ℝ):= conduct f x t a b; let Y:= -2*Complex.I; let T(x:ℝ):= Y*(Complex.exp (t*(Complex.I*x)) * hymn o x)
 have hp(A B): IntegrableOn (g A B) arena:= ((hutC o p t A B).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self; have hx(x:ℝ): g 0 2 x+g 1 3 x=T x:=by
    have hb(x:Momentum): (-zen x) 0 2+(-zen x) 1 3=Y*x 3:=by unfold zen gammaOp Y; norm_num [Matrix.sum_apply,Matrix.smul_apply, Axis, Fin.sum_univ_succ,Tang,SpinIdx]; change -(x 2+x 3*Complex.I) + -(-x 2+x 3*Complex.I)=-(2*I*x 3); ring -- tune
    unfold g conduct T; rw [←mul_add,hb]; change _ *(Y* f x 3)= Y *_; unfold f; rw [moanHeight o p]; ring
 change chamber _ + chamber _ =_; unfold chamber; rw [add_sub_cancel_right]; rw [←mul_add,←integral_add (hp 0 2) (hp 1 3)]; change (τ:ℂ)⁻¹ * (∫ x in arena, g 0 2 x+g 1 3 x)= _; simp_rw [hx]; unfold T; rw [integral_const_mul]; unfold literal; letI : Fact (0 < τ):=⟨tau_pos⟩; rw [fourierCoeff_eq_intervalIntegral (tag o p) (-t) (-Real.pi)]; rw [show -Real.pi+τ= Real.pi from (by unfold τ; ring),intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi≤ Real.pi),neg_neg]; simp_rw [tag_eq, fourier_coe_apply,smul_eq_mul]; simp_rw [show ∀ x:ℝ, 2*(Real.pi:ℂ)*Complex.I*t*x/ τ=t*(Complex.I*x) from (by intro i; unfold τ; push_cast; field_simp [Real.pi_ne_zero] )]; rw [Complex.real_smul]; simp only [one_div]; unfold Y arena; push_cast; ring
lemma chance_b {π M₁:ℕ→Side}(h:∀ i,Even (π i).val)(pv:Tendsto (fun i=>(π i).val) atTop atTop) (v':∀ i,Odd (M₁ i).val)(p':Tendsto (fun i=>(M₁ i).val) atTop atTop) (s:ℕ→Rim)(q:∀ i,Slab (s i))(z:Tendsto s atTop (𝓝 o)) : Tendsto (fun i=>berth (s i) (M₁ i) (π i) t u j k) atTop (𝓝 ((ℳ) t u j k)):= by
 refine moneyL _ (hutC o p (t-u) j k) h pv (fun i x=> conduct (fun r=> mixL 4 (M₁ i) (floorPin (s i) r)) x (t-u) j k) ?_; intro x hx a c s' b Q; let w:= reelG; let R(i):=floorPin (s (a i)) (s' i); have he:Tendsto R atTop (𝓝 (floorPin o x)):= w.continuousAt (x:=(o,x))  |>.tendsto.comp ((z.comp c.tendsto_atTop).prodMk_nhds Q)
 let Y(i):= mixL 4 (M₁ (a i)) (R i); have hp:Tendsto Y atTop (𝓝 (melody (floorPin o x))):= (by apply tendsto_pi_nhds.mpr; intro i; change Tendsto (fun x=> mixL 4 (M₁ (a x)) (R x) i) atTop (𝓝 (melody (floorPin o x) i)); exact harmony (M:=M₁∘a) (fun i=>v' _) (p'.comp c.tendsto_atTop) he (fun i=> never_pin o p x i) _ (Eventually.of_forall fun i=> town_quote _ (q _) (abs_le.mpr (b i))))
 let f:=fun z:ℝ×Momentum=>Complex.exp ((t-u:ℤ)*(Complex.I*z.1)) *(-Fir.zen z.2) j k; change Tendsto (fun n=>f (s' n,Y n)) atTop (𝓝 (f (x, melody (floorPin o x)))); simpa only [Function.comp_def] using! (dualCont (t-u) j k).continuousAt.tendsto.comp (Q.prodMk_nhds hp)
section det
omit p
private lemma tributary {X Y:Type*}(K:X→Y→ℂ) {n:ℕ} (x:Fin n→X)(y:Fin n→ Y)
    (v: (Matrix.of fun i j=> K (x i) (y j)).det≠0)
    (p:∀ (x:Fin (n+1)→X) (y:Fin (n+1)→Y), (Matrix.of fun i j=> K (x i) (y j)).det=0):
    ∃ F:X→Fin n→ℂ,∀ x' y', K x' y'=∑ i:Fin n,F x' i*K (x i) y':=by
 let A:= Matrix.of fun i j=> K (x i) (y j); let R(X':X): Matrix (Fin 1) (Fin n) ℂ:= Matrix.of fun _ j=> K X' (y j); let B(y'):Matrix (Fin n) (Fin 1) ℂ:= Matrix.of fun i _=> K (x i) y'
 letI := (show IsUnit A from (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr v)).invertible
 refine ⟨fun x' i=>(R x' *⅟A) 0 i,fun x' y'=> ?_⟩; let D:Matrix (Fin 1) (Fin 1) ℂ:=!![K x' y']; let f:= (Matrix.fromBlocks A (B y') (R x') D); let J:Fin n ⊕ Fin 1 ≃ Fin (n+1):= finSumFinEquiv
 have he: f.det=0:=by
    rw [←Matrix.det_submatrix_equiv_self J.symm f]; let x'' := Sum.elim x (fun (_:Fin 1)=> x') ∘ J.symm; let y'':= Sum.elim y (fun (_:Fin 1)=>y') ∘ J.symm; rw [show f.submatrix J.symm J.symm = Matrix.of (fun i j=>K (x'' i) (y'' j)) from ?_,p x'' y'']; ext i j; unfold Matrix.submatrix x'' y''; simp only [Matrix.of_apply, Function.comp_apply]; cases J.symm i <;> cases J.symm j <;> first| rfl| simp [f,D, Fin.eq_zero]
 unfold f at he; rw [Matrix.det_fromBlocks₁₁] at he; have hw:=(mul_eq_zero.mp he).resolve_left v; rw [Matrix.det_fin_one] at hw; exact sub_eq_zero.mp hw
open LinearMap Module
private lemma alters (n:ℕ)(F:Fin (2*n+1)→Bool×Fin n→ℂ):∃ x:Fin (2*n+1)→ℂ, x≠0∧ ∀ j:Bool× Fin n, ∑ i,x i*F i j=0:=by
 let Y:= Matrix.of fun (a:Bool× Fin n) i=>F i a; let V:=Y.mulVecLin; have hp:¬ Function.Injective V:= fun p=>Nat.not_succ_le_self (2*n) (by simpa [V] using finrank_le_finrank_of_injective p) -- order
 obtain ⟨x,h,v⟩: ∃ x, V x=0∧x≠0:= by by_contra! u; apply hp (LinearMap.ker_eq_bot.mp ?_); exact LinearMap.ker_eq_bot'.mpr u -- names
 refine ⟨x,v,fun j=>?_⟩; have hi:=congr_fun h j; simpa only [V,Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct, Matrix.of_apply,Y, mul_comm,Pi.zero_apply] using hi
end det
abbrev Flight:= ℕ×Bool
private def ribbon(b:Bool)(i:ℤ):ℤ:= if b then i else -i
private lemma ride_t (b:Bool)(i j:ℤ): ribbon b i+ribbon b j=ribbon b (i+j):=by cases b <;> simp [ribbon] <;> ring
def instant (l:ℕ)(b:Bool)(i:ℕ):ℤ:= ribbon b (l+i:ℕ)
def upperL (i:Bool):SpinIdx:= if i then 1 else 0
def lowerL (i:Bool):SpinIdx:= if i then 3 else 2
-- indices of B_L orientation b and B_R=!b. sign. require h when refreeze. 
abbrev loan (T:ℤ→ℤ→SpinIdx→SpinIdx→ℂ)(l:ℕ)(b:Bool)(x y:Flight):ℂ:= T (instant l b x.1) (instant l (!b) y.1) (upperL x.2) (lowerL y.2)
variable (l n:ℕ)(b:Bool)
local notation "Φ"=> loan (Tempo (fun r=> melody (floorPin o r))) l b
set_option maxHeartbeats 360000 in
include p in
theorem inch : ∃ x y:Fin n→Flight, (Matrix.of (fun i j=> loan (Tempo (fun r=> melody (floorPin o r))) l b (x i) (y j))).det ≠ 0:=by
 induction n with
 | zero => exact ⟨Fin.elim0,Fin.elim0,by simp⟩
 | succ n ih=>
    obtain ⟨x,y,v⟩:= ih
    by_contra! k
    obtain ⟨F,H⟩:= tributary (loan (Tempo (fun r=> melody (floorPin o r))) l b) x y v k; let q(g: Bool)(s:ℕ):ℕ:= s; let W:= Fin (2*n+1); let U:= Fin n; obtain ⟨x',t',y'⟩:=alters n (fun i w=> F (i.val,w.1) w.2); let r:=2*n+1; have hw(u:ℕ)(b':Bool): ∑ i:W,x' i*Φ ((i.val),b') (u,b')=0:=by
       let z:Flight:=(u,b'); change ∑ i:W,x' i * Φ (_,b') z=0; -- rewrite H inside LHS only not all Φ recursively
       let G:W→Flight:=fun i=>(i.val,b'); change ∑ i:W, x' i * Φ (G i) z = _; rw [sum_congr rfl (g:=fun i:W=> x' i * ∑ j:Fin n,F (G i) j*Φ (x j) z) fun i h=> congrArg _ (H (G i) z)]; simp_rw [mul_sum, ←mul_assoc]; rw [sum_comm]; refine sum_eq_zero fun i p => ?_; rw [←sum_mul,show ∑ j:W,x' j * F (G j) i=0 from y' (b',i), zero_mul]
    -- identity orientation. total t−u = ribbon (b) (2l+t+u). so - exponent. sequential taps.
    have he(t s:ℕ): (Φ (t,true) (s,true)+Φ (t,false) (s,false))=(-2*Complex.I) * literal o p (-ribbon b (2*l+t+s:ℕ)):=by
       let x:= instant l b t; let y:= instant l (!b) s; rw [add_comm]; have φ : x=ribbon b (2*l+t+s:ℕ)+y:=by unfold x y instant; cases b <;> simp [ribbon] <;> omega
       change (ℳ) x y 0 2+(ℳ) x y 1 3=_; rw [φ]; exact (show (ℳ) (ribbon b (2*l+t+s:ℕ)+y) y 0 2+(ℳ) (ribbon b (2*l+t+s:ℕ)+y) y 1 3 =_ from recurr_b o p ..)
    have hv(s:ℕ):∑ j:W,x' j * literal o p (-ribbon b (2*l+j.val+s:ℕ))=0:= by
       apply mul_left_cancel₀ (show -2*Complex.I≠0 by simp); rw [mul_zero, Finset.mul_sum,sum_congr rfl (g:=fun i:W=> x' i * ((-2*Complex.I) * literal o p (-ribbon b (2*l+i.val+s:ℕ)))) (fun i _=>mul_left_comm ..)]; simp_rw [←he,mul_add,sum_add_distrib,hw,add_zero]
    let g:=fun i:W=>i.val; have hp := (show Injective g from Fin.val_injective)
    cases b
    · obtain ⟨i,f',hz⟩:= ((reachG o p g hp x' t').and_eventually (eventually_ge_atTop (2*l:ℤ))).exists; let n:= (i-2*l).toNat; apply f' ((sum_congr rfl (fun j m=> congrArg (fun i=> x' j *literal o p i) (show i+g j=_ from ?_))).trans (hv n)); simp only [ribbon,Bool.false_eq_true,↓reduceIte,neg_neg]; unfold n g; omega
    · obtain ⟨i,f',hz⟩:= ((sends o p g hp x' t').and_eventually (eventually_le_atBot (-(2*l):ℤ))).exists; let n:=(-i-2*l).toNat; apply f' ((sum_congr rfl (fun j m=> congrArg (fun i=> x' j *literal o p i) (show i-g j=_ from ?_))).trans (hv n)); unfold n g ribbon; rw [if_pos rfl]; omega
end YM.CF.Window.Largo

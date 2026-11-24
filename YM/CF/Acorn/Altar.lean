import YM.CF.Acorn.Engels
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Matrix NormedSpace Finset Fock Jet Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {n Y D:Type}[LinearOrder n][Fintype n][Fintype Y][DecidableEq Y][TopologicalSpace D]
variable {X:Master D Y}{O:n→Y}{a c h v K:ℝ}{R:Seal Y}{F G:D→ Op (I n)}{A B W:D→ FC n}
lemma earned_t (t:R.Nonempty)(r:Grove X.frame R)(hc:0≤a)(hl:0≤h)(hp:0≤v)(H:∀x,UnitR (A x))(u:A+B=mix ∘ F)(p:PairX X O R a (mix ∘ F) c) (L:∀ i:I n, Drop X O a i (fun x=>unitL (A x) (pen i)) v) (g:∀ x,nilX (B x)) : Carries X O R a h (fun x=>exp (A x)*exp (B x)) (Real.exp (3*(worth X.k*(2*DriftX a h v c X.k)))):=by
 let D':= 2*DriftX a h v c X.k; let T:=worth X.k*D'
 have he:1≤ worth X.k:=one_w _; have ht:0≤T:=by unfold T D' DriftX; have h':= p.pos; positivity
 let f(k:ℕ)(x:D):= sent (liftL (A x) (B x)) k 1; let K:= plume T 1
 have P (k:ℕ):Carries X O R a h (f k) (K k):=by
    induction k using Nat.strong_induction_on with
    | h m ih=>
      cases m with
      | zero=> rw [show K 0=1 from by unfold K; rw [plume], show f 0 = 1 from funext fun x=>sent_zero ..]; apply Carries.identity r
      | succ k=>
        have hk(i:D):=cascade (A i) (B i) (F i) (congr_fun u i) k (H i)
        let Q(z:ℕ×ℕ)(x:D):=sent (unitL (A x)) z.1 (mix (F x))* f z.2 x
        let c:= ((k+1:ℕ):ℂ); have ho:c≠0:=Nat.cast_ne_zero.mpr (by omega)
        have hE: f (k+1)= c⁻¹ • (fun x=> ∑ i∈ pairs k,Q i x):=by funext x; rw [Pi.smul_apply, show (∑ i∈ pairs k, Q i x)=c • f (k+1) x from by rw [show c=(k:ℂ)+1 from Nat.cast_add_one k]; exact (hk x).symm,smul_smul, inv_mul_cancel₀ ho, one_smul]
        rw [hE]; have hm (i:ℕ × ℕ) (q:i∈ pairs k):Carries X O R a h (Q i) (T*K i.2):=by
          apply (motion_k hc hp p H L i.1 ((mem_filter.mp q).2)).product (ih i.2 ?_) t hc hl
          have hg:=mem_antidiagonal.mp (mem_filter.mp q).1; omega
        apply ((Carries.all_s (pairs k) _ Q hm).sMul c⁻¹).more
        apply le_of_eq; rw [show K (k+1)= (∑ i∈ pairs k, T*K i.2)/(k+1:ℝ) from p_eq _,norm_inv, Complex.norm_natCast]; push_cast; ring
 let S:= 2*Fintype.card n
 rw [show (fun x=> exp (A x)*exp (B x))=fun x=>∑ i∈ range (S+1),f i x from funext fun x=> by simpa only [mul_one] using rotor (H x).exhaust (g x) 1]
 apply (Carries.all_s _ _ _ (fun i (_:i∈range (S+1))=>P i)).more
 simpa only [mul_one] using out_proc S ht (show (0:ℝ)≤1 from zero_le_one)
lemma ticket_exp (t:R.Nonempty)(r:Grove X.frame R)(hc:0≤a)(hl:0≤h)(e:Carries X O R a h W K)(p:∀ x,nilX (W x)) : Carries X O R a h (fun x=> exp (W x)) (Real.exp (worth X.k*K)) :=by
 let T:=worth X.k*K; have ht:0≤T:=mul_nonneg (zero_le_one.trans (one_w _)) (e.pos hl)
 let d k:=T^k/((k.factorial:ℕ):ℝ)
 have H(k:ℕ):Carries X O R a h (fun i=> W i ^ k) (T^k):=by
    induction k with
    | zero=> simp only [pow_zero]; exact Carries.identity r
    | succ k ih=> simp only [pow_succ']; exact e.product ih t hc hl
 have Q(k:ℕ):Carries X O R a h (fun x=> drum k (W x)) (d k):=by
   have hh:= (H k).sMul ((k.factorial:ℂ)⁻¹); unfold d; rw [show T^k/(k.factorial:ℕ) = ‖(k.factorial:ℂ)⁻¹‖*T^k by rw [norm_inv,Complex.norm_natCast]; ring]; exact hh
 rw [show (fun x=>exp (W x))=(fun x=>∑ i∈ range (Fintype.card n+1), drum i (W x)) from funext fun x=> (rotary (W x) (p x) (Fintype.card n) le_rfl).symm]; apply (Carries.all_s _ d _ (fun i _=> Q i)).more
 rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
 have he:= NormedSpace.norm_expSeries_summable' (𝕂:=ℝ) T; change Summable (fun i:ℕ=> ‖(i.factorial:ℝ)⁻¹ • T^i‖) at he
 dsimp only; apply le_trans (le_of_eq (sum_congr rfl (fun i (_:i∈range (Fintype.card n+1))=> show d i=(i.factorial:ℝ)⁻¹ • T^i from ?_))) (he.of_norm.sum_le_tsum _ ?_)
 · intro i _; rw [smul_eq_mul]; positivity
 unfold d; rw [smul_eq_mul]; ring
lemma ga_pow (K J:FC n) (i:ℕ): (exp K*J*exp (-K))^i= exp K*J^i * exp (-K) :=by
 induction i with
 | zero=> simp [wind_inv]
 | succ i ih=>
   have he:exp (-K)*exp K=1:= mul_eq_one_comm.mp (wind_inv K)
   rw [pow_succ',pow_succ',ih]; simp only [←mul_assoc]; rw [mul_assoc _ (exp (-K)) (exp K),he,mul_one]
lemma ga_expn (K J:FC n)(h:nilX J): exp (exp K*J*exp (-K))=exp K* exp J*exp (-K) :=by
 let n':= Fintype.card n
 have he:nilX (exp K*J*exp (-K)):=fun i g=> by rw [ga_pow,h i g,mul_zero,zero_mul]
 rw [←rotary _ he n' le_rfl,←rotary _ h n' le_rfl,mul_sum,sum_mul]; exact sum_congr rfl fun i _=>by rw [drum,ga_pow,drum, Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
lemma paidJ (t:R.Nonempty)(r:Grove X.frame R)(hc:0≤a)(hl:0≤h)(hv:0≤v)(H:∀ x,UnitR (A x))(f:PairX X O R a W c)(u:∀x,nilX (W x))(L:∀ i:I n, Drop X O a i (fun x=>unitL (A x) (pen i)) v) : Carries X O R a h (fun x=> exp (A x)*exp (W x)*exp (-A x)) (Real.exp (worth X.k*(6*DriftX a h v c X.k))) :=by
  rw [show _=(fun x=> exp (exp (A x)*W x*exp (-A x))) from funext fun i=> (ga_expn _ _ (u i)).symm]; exact ticket_exp t r hc hl (shook hc hv f H L) (fun i k p=>by rw [ga_pow,u i k p,mul_zero,zero_mul])
end YM.CF.Acorn

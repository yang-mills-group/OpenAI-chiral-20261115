import ZecaSeafoam
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open Real
open scoped Classical
structure Gait (g:ℝ→ℝ):Prop where
 pos : ∀t,0<t → 0<g t
 anti : ∀{t u},0<t → t ≤ u → g u ≤ g t
 poly : ∃ (B:ℝ)(p:ℕ),0<B ∧ ∀t:ℝ,0<t→t≤1 → g t ≤ B/t^p

def spur (p:ℕ)(u:ℝ):ℝ:=1+(1/u)^p

def dyadG (g:ℝ→ℝ)(n:ℕ):ℝ:=log (g ((1/2:ℝ)^n))

lemma Gait.stride {g:ℝ→ℝ} (l:Gait g) :
  Monotone (dyadG g) ∧ ∃ (D m:ℝ),0≤ m ∧ ∀ n, dyadG g n ≤ D+m*n := by
 have hp:0<(1/2:ℝ):=one_half_pos
 have hp':(1/2:ℝ)≤1:=by norm_num
 have h(n:ℕ):0<(1/2:ℝ)^n:=pow_pos hp _
 refine ⟨fun n k u=> Real.log_le_log (l.pos _ (h _))
       (l.anti (h k) (pow_le_pow_of_le_one hp.le hp' u)),?_⟩
 have v:0<log 2:= Real.log_pos (by norm_num)
 have w:log (1/2:ℝ)= -log 2:=by rw [one_div,Real.log_inv]
 obtain ⟨B,p,u,t⟩:=l.poly
 refine ⟨log B,↑p*log 2, by positivity, fun n=>?_⟩
 have b:=Real.log_le_log (l.pos _ (h n)) (t _ (h n) (pow_le_one₀ hp.le hp'))
 rw [Real.log_div u.ne' (pow_pos (h n) _).ne', log_pow,log_pow,w] at b
 exact le_trans b (le_of_eq (by ring))

lemma Gait.shell {g:ℝ→ℝ} (l:Gait g)
 {T M δ:ℝ}(h:0<T)(k:0<δ)
 (n:ℕ)(v:δ*T≤(1/2:ℝ)^n) (w:(1/2:ℝ)^n ≤ δ*M)
 (d:ℕ) (q:Amble (dyadG g) (d*log 2) n)
 (u:ℝ) (hp:0<u): 
 g (δ*u) ≤ g (δ*T) * (1+(2*M)^d)* spur d u:=by
  have a0:= l.pos _ (mul_pos k h)
  have hT:T ≤ M := (mul_le_mul_iff_right₀ k).mp (v.trans w)
  have e:0<M:= h.trans_le hT
  have z:0<1+(2*M)^d:=by positivity
  have z':1≤ spur d u:=by unfold spur; exact le_add_of_nonneg_right (by positivity)
  rcases le_total M u with hu|hu
  · refine (l.anti (mul_pos k h) (mul_le_mul_of_nonneg_left (hT.trans hu) k.le)).trans ?_
    rw [mul_assoc]
    apply le_mul_of_one_le_right a0.le
    exact one_le_mul_of_one_le_of_one_le (by linarith [(pow_nonneg (mul_nonneg zero_le_two e.le) d)]) z'
  obtain ⟨i,j,r⟩:=exists_nat_pow_near ((one_le_div hp).mpr hu) (by norm_num :1<(2:ℝ))
  let p:=i+1
  have s0:0<(1/2:ℝ)^(n+p):=pow_pos one_half_pos _
  have t0:(1/2:ℝ)^(n+p)≤δ*u:=by
    have l0:= le_of_lt ((div_lt_iff₀ hp).mp r)
    have l1:= (mul_le_mul_of_nonneg_left l0 k.le)
    have g0: (2:ℝ)^p*(1/2:ℝ)^p=1:=by rw [← mul_pow];norm_num
    apply (mul_le_mul_iff_right₀ (pow_pos (by norm_num : (0:ℝ)<2) p)).mp
    rw [pow_add (1/2:ℝ),
      show (2:ℝ)^p*((1/2:ℝ)^n*(1/2:ℝ)^p)=(2^p*(1/2)^p)*(1/2)^n by ring,g0, one_mul]
    change δ*M ≤ δ*(2^p*u) at l1
    exact w.trans (l1.trans_eq (by ring))
  refine (l.anti s0 t0).trans ?_
  have qi:= q p
  rw [dyadG,dyadG] at qi
  have aq:=Real.exp_monotone qi
  have aq2:0<(1/2:ℝ)^n:=pow_pos one_half_pos _
  have eq:↑d*log 2 * (p:ℝ)= log (((2:ℝ)^p)^d):=by rw [log_pow,log_pow];ring
  rw [exp_add,eq,exp_log (l.pos _ s0),exp_log (l.pos _ aq2),
     exp_log (pow_pos (pow_pos (by norm_num) _) _)] at aq
  refine aq.trans ?_
  rw [mul_assoc]
  apply mul_le_mul (l.anti (mul_pos k h) v) _ (by positivity) a0.le
  have q2:(2:ℝ)^p ≤ 2*M * (1/u):=by
    unfold p; rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right j zero_le_two).trans_eq (by ring)
  refine (pow_le_pow_left₀ (pow_nonneg (by norm_num) _) q2 d).trans ?_
  rw [mul_pow]
  unfold spur
  gcongr <;> linarith

lemma Wavefront.groom
 {v:ℕ→ℕ→ℝ} (e:Wavefront v)
 (δ:ℕ→ℝ) {T M:ℝ} (pos:∀n,0<δ n) (h:0<T)(b:0<M)
 (w:∀ᶠ n:ℕ in atTop, δ n*T ≤ (1/2:ℝ)^n ∧ (1/2:ℝ)^n≤δ n*M)
 (g:ℝ→ℝ) (l:Gait g):
 ∃ (z:ℕ→ℕ), Tendsto z atTop atTop ∧
    (∀ i,Tendsto (fun j=>v i (z j)) atTop (𝓝 0)) ∧
    ∃ (d:ℕ)(K:ℝ),0<K ∧ ∀ n t,0<t → 
         g (δ (z n)*t) ≤ g (δ (z n)*T) * K * spur d t := by
 obtain ⟨hm,D,m,c,q⟩:= l.stride
 have u:=Real.log_pos (show (1:ℝ)<2 by norm_num)
 obtain ⟨d,w'⟩:= exists_nat_gt (8*m/log 2)
 obtain ⟨z,f,r,p⟩:= e.beach _ D m _ c ((div_lt_iff₀ u).mp w') hm q
 have v0 : 0<1+(2*M)^d :=by positivity
 obtain ⟨i₀,p'⟩:= eventually_atTop.mp (r.and (f.eventually w))
 have iz := tendsto_add_atTop_nat i₀
 refine ⟨_, f.comp iz,fun i=>(p i).comp iz,d,_,v0,fun n t pt=>?_⟩
 obtain ⟨r',v',w''⟩:= p' (n+i₀) (Nat.le_add_left ..)
 exact l.shell h (pos _) _ v' w'' _ r' t pt
#print axioms Wavefront.groom

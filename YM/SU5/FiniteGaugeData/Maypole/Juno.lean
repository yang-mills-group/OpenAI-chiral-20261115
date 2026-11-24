import YM.SU5.FiniteGaugeData.Maypole.Rimbaud
/-! # Diagonal spectrum: time-skew tilt, moment poles -/
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.CF.Buffered.Afterglow.Hierarchy.Vp.Juno
open Function Set MeasureTheory OS OS.Semigroup Complex Filter NormedSpace Metric Bornology Rimbaud
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {X:Type*} [MeasurableSpace X] {A U:X→ℝ} {n i j k:ℕ}{μ:Measure X}[IsFiniteMeasure μ]{r s t e x C:ℝ} {z:ℂ}
-- scalar energies. slope with both directions, measured.P_Eq (OS proof later)
local notation "D"=> 𝓝 (0:ℂ)
local notation "W"=> 𝓝 (0:ℝ)
local notation "D₁"=> 𝓝[>] (0:ℝ)
local notation "D₂"=> 𝓝[<] (0:ℝ)
abbrev Lot (u:ℝ):= closedBall (0:ℂ) u
def kin(t a:ℝ):= Real.exp (-t*a)
@[fun_prop] lemma kin_m(r:ℝ){t:X→ℝ}(hm: Measurable t): Measurable (fun x=>kin r (t x)):=by unfold kin; fun_prop
abbrev Ar(z p:ℝ):ℂ:= -(z:ℂ) + (p:ℂ)*Complex.I
abbrev shape(z:ℂ)(a p:ℝ): ℂ:=Complex.exp (z*Ar a p)
abbrev keyi(A U:X→ℝ)(q s t:ℝ)(x:X):ℂ:= (kin t (A x):ℂ)* shape s (A x) (q*U x)
@[fun_prop] lemma keyi_m(A U:X→ℝ)(ha:Measurable A)(ht:Measurable U)(s t q:ℝ): Measurable (keyi A U q s t):=by unfold keyi shape Ar; fun_prop
structure Payer (μ: Measure X) (A U:X→ℝ) :Prop where
 air: ∀ᵐ x ∂μ, 0 ≤ A x
 u_m : Measurable U
 a_m : Measurable A
variable (P:Payer μ A U)
-- price cut.T
omit [MeasurableSpace X] in
lemma shape_fee(A U:X→ℝ)(z:X)(q s t:ℝ): ‖keyi A U q s t z‖=kin (t+s) (A z):=by
 rw [keyi,norm_mul,shape,norm_exp,Complex.norm_real]; unfold kin; rw [Real.norm_of_nonneg (Real.exp_pos _).le,←Real.exp_add]; simp [Ar]; ring_nf -- tune
omit [MeasurableSpace X] in
lemma shape_pick(x:X)(q s t:ℝ)(h:0≤ t+s) (e:0≤ A x): ‖keyi A U q s t x‖ ≤ 1:= (shape_fee ..).trans_le (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) e))
include P
lemma atkin (q s t:ℝ)(h:0≤t+s) : Integrable (keyi A U q s t) μ:= Integrable.of_bound (keyi_m _ _ P.a_m P.u_m .. |>.aestronglyMeasurable) 1 (P.air.mono (fun x p=> shape_pick x _ _ _ h p))
omit P
structure Chunk(t C:ℝ)(μ:Measure X)(A U:X→ℝ):Prop where
 live : 0<t
 memo(q:ℝ)(h: |q|≤1): ∃ f:ℂ→ℂ, AnalyticOnNhd ℂ f (Lot (t/8)) ∧ (∀ x∈Lot (t/8),‖f x‖≤C) ∧ ∀ r:ℝ, |r|≤t/8 → f r=∫ p:X, keyi A U q r t p ∂μ
abbrev burn(t:ℝ)(n:ℕ):ℝ:= t/(64*((n:ℝ)+1))
variable (g:Chunk t C μ A U)
-- $m_n t,s`
local notation "U°" z:max=> U z
local notation "A°" z:max=> A z
abbrev sVal(A U:X→ℝ)(r:ℝ)(z:X):= shape r (A z) (U z)
def power (A U:X→ℝ)(s:ℝ)(n:ℕ)(x:X):ℝ:= ‖1- shape s (A x) (U x)‖^(2*n)
def life(A U:X→ℝ)(t s:ℝ)(i j n:ℕ)(x:X):ℂ:= ((((kin t (A x)):ℂ)*(sVal A U s x)^i* star (sVal A U s x)^j):ℂ) * ↑(power A U s n x)
omit [MeasurableSpace X] in
private lemma sPow(A U:X→ℝ)(t s:ℝ)(i j:ℕ)(x:X): life A U t s i j 0 x= keyi A U (((i:ℝ)-j)/((i:ℝ)+j)) (((i:ℝ)+j)*s) t x:=by
 unfold life keyi power; simp only [Nat.mul_zero,pow_zero,ofReal_one,mul_one]; rw [mul_assoc]; apply congrArg; unfold sVal shape; let Q:= shape (s:ℂ) (A x) (U x); by_cases p:(i:ℝ)+j=0
 · have he:(i=0 ∧ j=0):=by exact Nat.add_eq_zero_iff.mp (by exact_mod_cast p)
   rw [he.1,he.2]; simp
 rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,←Complex.exp_add]; congr 1; unfold Ar; push_cast; simp [map_mul]; let P:= (i:ℂ)+j; have hx: P≠0:= by unfold P; exact_mod_cast p
 change (i:ℂ)+(j:ℂ) ≠0 at hx; field_simp; ring
omit [MeasurableSpace X] in
private lemma rebuy(i j n:ℕ)(s t:ℝ): life A U t s i j (n+1) = life A U t s i j n + life A U t s (i+1) (j+1) n - life A U t s (i+1) j n - life A U t s i (j+1) n:=by
 funext x; let w:=sVal A U s x; have hp: (power A U s (n+1) x:ℂ)= (power A U s n x:ℂ)*((1-w)*(1-star w)):=by
    have he:(1-w)*(1-star w)=(↑(‖1-w‖^2):ℂ):=by rw [← show star (1-w)=1-star w from (by rw [star_sub,star_one])]; exact (Complex.mul_conj _).trans (by rw [Complex.normSq_eq_norm_sq])
    rw [he,← Complex.ofReal_mul]; unfold power; rw [Nat.mul_add,Nat.mul_one,pow_add]; -- tune w reducible
 simp only [Pi.sub_apply,Pi.add_apply,life,pow_succ]; rw [hp]; unfold w; ring
-- measure permit
include g
lemma bore : 0 < burn t n:=by unfold burn; exact div_pos g.live (by positivity)
private lemma snap {i k:ℕ}(h: i+k≤2*n)(v:‖z‖≤ burn t n): ‖((i:ℂ)+k)*z‖ ≤ t/8:=by
 let u:=(i:ℕ)+(k:ℕ); let e:= burn t n; rw [norm_mul,← Nat.cast_add, show ‖(↑u:ℂ)‖=(u:ℝ) by simp]; refine (mul_le_mul_of_nonneg_left v (by positivity)).trans ?_; have he : (u:ℝ) ≤ 2*((n:ℝ)+1):=by exact_mod_cast (by unfold u; omega : u≤ 2*(n+1)) -- exact_mod_cast trouble
 have hp:= g.live; have hq:0<=(burn t n):=(bore g).le; apply le_trans (mul_le_mul_of_nonneg_right he hq); unfold burn; field_simp; nlinarith only [hp]
omit g
structure Warp (μ:Measure X)(F:ℝ→ X→ℂ)(Dt C:ℝ)(f:ℂ→ℂ):Prop where
 hol: AnalyticOnNhd ℂ f (Lot Dt)
 price: ∀ z:ℂ, ‖z‖≤Dt→ ‖f z‖≤C
 deed: ∀ z:ℝ, |z|≤Dt→ Integrable (F z) μ ∧ f z=∫ p,F z p ∂μ
namespace Warp
variable {F G:ℝ→ X→ℂ} {f y:ℂ→ℂ}{Dt C':ℝ} (uG:Warp μ F Dt C f) (v:Warp μ G Dt C' y)
include uG v
lemma plusM : Warp μ (F+G) Dt (C+C') (f+y):=⟨fun z p=> (uG.hol z p).add (v.hol z p),fun z p=>(norm_add_le ..).trans (add_le_add (uG.price z p) (v.price z p)),fun z p=> let S:=uG.deed z p; let T:=v.deed z p; ⟨S.1.add T.1, Eq.trans (congrArg₂ (·+·) S.2 T.2) (integral_add S.1 T.1).symm⟩⟩
lemma minusM : Warp μ (F-G) Dt (C+C') (f-y):=⟨fun z p=> (uG.hol z p).sub (v.hol z p),fun z p=>(norm_sub_le ..).trans (add_le_add (uG.price z p) (v.price z p)),fun z p=> let S:=uG.deed z p; let T:=v.deed z p; ⟨S.1.sub T.1, Eq.trans (congrArg₂ (·-·) S.2 T.2) (integral_sub S.1 T.1).symm⟩⟩
end Warp
abbrev mint(i j n:ℕ)(A U:X→ℝ)(t C B:ℝ)(μ:Measure X):= ∃ f:ℂ→ℂ, Warp μ (fun s=>life A U t s i j n) B C f
include g P
private lemma till (h:i+j≤2*n): mint i j 0 A U t C (burn t n) μ:=by
 let q:ℝ:= (i+j:ℕ); let p:=((i:ℝ)-j)/q; have he:q=(i:ℝ)+j:= Nat.cast_add ..; have hu:0≤q:= Nat.cast_nonneg _; obtain ⟨f,hf,w,Y⟩:= g.memo p (by
   rcases eq_or_lt_of_le hu with e|e; · simp [p,← e]
   unfold p; rw [abs_le]; constructor; · rw [le_div_iff₀ e,he]; linarith [Nat.cast_nonneg (α:=ℝ) i]
   rw [div_le_iff₀ e,he]; linarith [Nat.cast_nonneg (α:=ℝ) j]) -- indent tune
 let F(z:ℂ):=(q:ℂ)*z; have hF:AnalyticOnNhd ℂ F (Lot (burn t n)):= (fun z _=> analyticAt_const.mul analyticAt_id); have hv(z:ℂ)(k: z∈Lot (burn t n)): F z∈Lot (t/8):=by unfold F; rw [he]; push_cast; exact mem_closedBall_zero_iff.mpr (snap g h (mem_closedBall_zero_iff.mp k))
 refine ⟨f ∘ F,fun z k=> (hf _ (hv z k)).comp (hF z k), fun z t=> w _ (hv z (mem_closedBall_zero_iff.mpr t)),fun s k=>?_⟩; let m:=q*s; have hx:F (s:ℂ)= (m:ℂ):=(ofReal_mul ..).symm; have hy: |m|≤ t/8:=( ((Complex.norm_real _).symm).trans_le ?_) -- tune
 have hp:life A U t s i j 0 = keyi A U p m t:= by unfold p m; rw [he]; exact funext fun x=>sPow A U t s i j x -- sPow .. in funext tune
 rw [hp,Function.comp_apply,hx]; refine ⟨atkin P p m t (by linarith only [g.live,(abs_le.mp hy).1]),Y m hy⟩
 rw [←hx]; exact mem_closedBall_zero_iff.mp (hv _ (mem_closedBall_zero_iff.mpr ((Complex.norm_real _).trans_le k)))
set_option maxHeartbeats 380000 in
lemma wimp (e:i+j+2*k≤2*n): mint i j k A U t (C*4^k) (burn t n) μ:=by
 induction k generalizing i j with
 | zero=> rw [pow_zero,mul_one]; exact till P g (by omega)
 | succ k ih=>
    obtain ⟨F,hF⟩:=ih (i:=i) (j:=j) (by omega); obtain ⟨T,hT⟩:=ih (i:=i+1) (j:=j+1) (by omega); obtain ⟨J,hJ⟩:=ih (i:=i) (j:=j+1) (by omega); obtain ⟨M,hM⟩:=ih (i:=i+1) (j:=j) (by omega); let uℓ:= C*4^k; have he:= ((hF.plusM hT).minusM hM).minusM hJ; have hg(k i j:ℕ): (fun s=>life A U t s i j (k+1))=(fun s=>life A U t s i j k)+(fun s=>life A U t s (i+1) (j+1) k)-(fun s=>life A U t s (i+1) j k)-(fun s=>life A U t s i (j+1) k):=funext fun s=> rebuy i j k s t
    exact ⟨_,hg k i j ▸ (show C*4^(k+1) = uℓ+uℓ+uℓ+uℓ from (by unfold uℓ; ring)) ▸ he⟩
lemma bloomG(n:ℕ): ∃ f:ℂ→ℂ,Warp μ (fun s z=>↑((kin t (A z))*power A U s n z)) (burn t n) (C*4^n) f :=by
 obtain ⟨f,h⟩:= wimp (i:=0) (j:=0) (k:=n) (n:=n) P g (by omega); refine ⟨f,?_⟩; rw [show (fun s z=> (↑((kin t (A z))*power A U s n z):ℂ))=(fun s=>life A U t s 0 0 n) from funext fun s=>funext fun z=>by simp [life]]; exact h
#print axioms bloomG
end YM.CF.Buffered.Afterglow.Hierarchy.Vp.Juno

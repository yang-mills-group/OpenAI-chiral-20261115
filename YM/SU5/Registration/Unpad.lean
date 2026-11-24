import YM.SU5.Registration.Smeared

/-!
# Unpadding a coherent family

At strictly positive symmetric left/right pad, operator norm estimates. Then
as (also independently left/right) padding goes to zero, *smeared* operator
convergence in energy budgets. Width of the stencil has to go first in this
passage! Use power-growth bounds only for the resulting coherent family.
We don't infer either the positive-pad operator convergence or its norm price
from a vacuum price. Later instantiate with the M4 experiment and show which
limits are licensed already, and make the remaining physical estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinRegistration
open Set Filter Function MeasureTheory Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexOrder Classical
open OS OS.Semigroup SatinEdge.RealSheet Boundary Probe Multiplier Roy CF.Buffered.Afterglow.Hierarchy.Seld
open Grading
variable {H : Hilbert} {a : Axis} (S : OS.Semigroup H a)
local notation "G" => bands S
local notation "D" => radial S
local notation "T" => S.E
local notation "P" => cell S

/-- Padded operators at symmetric pad. No use of `B 0`. -/
def Sound (B : ℝ≥0 → H.Op) : Prop := ∀ t : ℝ≥0, 0<t → ∀ s : ℝ≥0, B (t+s)=T s * B t * T s
def PadBound (B : ℝ≥0→H.Op) (k : ℕ) (C : ℝ) : Prop :=
   ∀ t : ℝ≥0, 0<t→ t≤1→ (t:ℝ)^k * ‖B t‖≤C
def PadPaid (B : ℝ≥0→H.Op) : Prop := ∃ k C, 0≤C ∧ PadBound B k C
variable (B : ℝ≥0→H.Op)
-- Two-sided cut charge
local notation "R" => rewarm S
lemma invRewarm (k : ℕ) (s t : ℝ≥0) : R (t+s) k * T s = R t k:=by
  refine Registers.single ((rewarm_reads S (t+s) k).times (costT S s)) ?_
  have h: charging a (t+s) k * (fun p=> (favor a s p:ℂ)) = charging a t k:= by
    funext p
    by_cases h:p∈foldBand a k
    · simp only [Pi.mul_apply, charging, indicator_of_mem h, ← Complex.ofReal_mul, ←Real.exp_add,favor,timeOf,NNReal.coe_add]
      congr 2; ring
    simp [charging,h]
  rw [h]; exact rewarm_reads S t k

abbrev coldAt (t : ℝ≥0) (m n : ℕ) := R t m * B t * R t n
lemma routes (m n : ℕ) {s : ℝ≥0} (u : 0<s) (t : ℝ≥0) (h : Sound S B) :
    coldAt S B (s+t) m n=coldAt S B s m n := by
  unfold coldAt; rw [h s u t]
  let U:=R (s+t) n
  have hv:T t* U=R s n:= ((costT S t).jointly (rewarm_reads S (s+t) n)).eq.trans (invRewarm S n t s)
  simp only [mul_assoc]; rw [show T t*R (s+t) n=R s n from hv,←mul_assoc (R (s+t) m),invRewarm]
lemma band_fixed (m n : ℕ) {s t : ℝ≥0} (p : 0<s) (q : 0<t) (h : Sound S B) : coldAt S B s m n = coldAt S B t m n :=
  (routes S B m n p t h).symm.trans ((add_comm t s) ▸ routes S B m n q s h)

def rawBlocks : (G).Blocks where
  op := fun m n=> coldAt S B 1 m n
  out := fun m n=> show P m*(R 1 m*B 1*R 1 n)=_ from by rw [←mul_assoc,←mul_assoc, incell_rewarm]
  inlet := fun m n=> show R 1 m*B 1*R 1 n*P n=_ from by rw [mul_assoc, ((rewarm_reads S 1 n).comm (foldBand_meas n)).eq, incell_rewarm]

lemma cold_price {k : ℕ} {C : ℝ} (p : PadBound B k C) (h : Sound S B) :
    PowerPrice S (rawBlocks S B) k (Real.exp 1*C* Real.exp 1) := by
  intro m n; let u := ((m+1:ℕ)*(n+1):ℕ)
  let t : ℝ≥0:= (u:ℝ≥0)⁻¹; let V:ℝ:=u; have hV₁:1≤V:= by
    have he:0<u:=(Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)); change 1≤(u:ℝ); exact_mod_cast (show 1≤u from he)
  have hV:0<V:=zero_lt_one.trans_le hV₁
  have ht: (t:ℝ)=V⁻¹ := by unfold t V; push_cast; rfl
  have hT: (0:ℝ≥0)<t := by change (0:ℝ) < (t:ℝ); rw [ht]; positivity
  have h1:t≤1:= by change (t:ℝ)≤(1:ℝ); rw [ht]; exact inv_le_one_of_one_le₀ hV₁
  let L:= Real.exp 1; have hL:0≤L:=(Real.exp_pos _).le
  have e(i)(u' : ((i+1:ℕ):ℝ)≤V) : ‖R t i‖≤L := by
    refine (rewarm_pays S t i).trans (Real.exp_monotone ?_)
    rw [ht]; exact le_trans (mul_le_mul_of_nonneg_left u' (inv_nonneg.mpr hV.le)) (inv_mul_cancel₀ hV.ne').le
  have hm:‖R t m‖≤L:=e m (Nat.cast_le.mpr (Nat.le_mul_of_pos_right _ (by omega)))
  have hn:‖R t n‖≤L:=e n (Nat.cast_le.mpr (Nat.le_mul_of_pos_left _ (by omega)))
  have hp: ‖B t‖≤ C*V^k:= by
    have he:= p t hT h1; rw [ht,inv_pow, inv_mul_eq_div] at he; exact (div_le_iff₀ (pow_pos hV k)).1 he
  change ‖coldAt S B 1 m n‖≤_
  rw [band_fixed S B m n zero_lt_one hT h]
  apply le_trans (b:=L*(C*V^k)*L)
  · exact (norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans (mul_le_mul hm hp (norm_nonneg _) hL)) hn (norm_nonneg _) (mul_nonneg hL ((norm_nonneg _).trans hp)))
  apply le_of_eq; unfold Grading.weight V u L; rw [Nat.cast_mul,mul_pow]; ring
lemma cold_paid (p : PadPaid B) (h : Sound S B) : PowerPaid S (rawBlocks S B):= by
  obtain ⟨k,C,u,p⟩:=p; refine ⟨k, _,mul_nonneg (mul_nonneg (Real.exp_pos _).le u) (Real.exp_pos _).le, cold_price S B p h⟩

/-- Blocks of any receipt at positive pad. -/
lemma recover (m n : ℕ) {t : ℝ≥0} (u : 0<t) (h : Sound S B) :
    ((bands S).dissect (B t)).op m n = T t*(rawBlocks S B).op m n*T t := by
  change P m*B t*P n= T t*coldAt S B 1 m n*T t
  have ht:R t n*T t=P n:= ((rewarm_reads S t n).jointly (costT S t)).eq.trans (forward_cell S t n)
  rw [band_fixed S B m n zero_lt_one u h]; unfold coldAt; rw [←mul_assoc,←mul_assoc, forward_cell, mul_assoc _ (R t n), ht]

/-- Frame with *asymmetric* positive pads. -/
def bothPads (u v : ℝ≥0) := T (u-min u v) * B (min u v) * T (v-min u v)
lemma arbitrary_pad {s u v : ℝ≥0} (p : 0<s) (hu : s≤u) (hv : s≤v) (h : Sound S B) :
    bothPads S B u v=T (u-s)* B s * T (v-s):= by
  let k:= min u v
  have hk:s≤k:=le_min hu hv
  unfold bothPads; change T (u-k)* B k*T (v-k)=_
  have he:B k=T (k-s)* B s *T (k-s):= by nth_rw 1 [← add_tsub_cancel_of_le hk]; exact h s p _
  rw [he];
  have hl: T (u-k)* T (k-s)=T (u-s):= (S.time (u-k) (k-s)).symm.trans (congrArg T (tsub_add_tsub_cancel (min_le_left ..) hk))
  have hr: T (k-s)* T (v-k)=T (v-s):= (S.time (k-s) (v-k)).symm.trans (congrArg T ((add_comm ..).trans (tsub_add_tsub_cancel (min_le_right ..) hk)))
  simp only [mul_assoc]; rw [hr,← mul_assoc (T (u-k)), hl]

lemma both_recover (m n : ℕ) {u v : ℝ≥0} (hu : 0<u) (hv : 0<v) (h : Sound S B) :
    ((bands S).dissect (bothPads S B u v)).op m n = T u*(rawBlocks S B).op m n * T v := by
  let t:= min u v; have ht: 0<t:= lt_min hu hv
  let A:=T (u-t); let C:=T (v-t)
  have he: A*T t=T u:= (S.time (u-t) t).symm.trans (congrArg T (tsub_add_cancel_of_le (min_le_left ..)))
  have hC: T t*C=T v:= (S.time t (v-t)).symm.trans (congrArg T (add_tsub_cancel_of_le (min_le_right ..)))
  let D':=(rawBlocks S B).op m n
  calc P m*(A*B t*C)*P n = A*(P m*B t*P n)*C:=by
                        rw [mul_assoc _ (B t),←mul_assoc (P m), (heat_cell S (u-t) m).symm.eq]; simp only [mul_assoc]; rw [(heat_cell S (v-t) n).eq]
       _ = A*(T t*D'*T t)*C:= by rw [show P m*B t*P n=T t*D'*T t from YM.SatinRegistration.recover S B m n ht h]
       _ = T u * D'* T v:= by rw [← mul_assoc A,←mul_assoc A,he,mul_assoc _ (T t),hC]

lemma both_price {r : ℕ} {C : ℝ} {u v : ℝ≥0} (hu : 0<u) (hv : 0<v) (h : Sound S B)
    (p : PowerPrice S (rawBlocks S B) r C) : PowerPrice S ((bands S).dissect (bothPads S B u v)) r C := by
  intro m n; rw [both_recover S B m n hu hv h]; apply le_trans _ (p m n); refine (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (S.shrinks v)).trans ?_); exact (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks u))

/-- Adjoints licensed without any right-sector vacuum column hypothesis. -/
lemma other_sound (h : Sound S B) : Sound S (fun t=> (B t).adjoint) := by
  intro t p s; dsimp only; rw [h t p s]; rw [← ContinuousLinearMap.star_eq_adjoint, star_mul, star_mul]; simp only [ContinuousLinearMap.star_eq_adjoint,S.sym,mul_assoc]
lemma other_price (p : PadPaid B) : PadPaid (fun t=> (B t).adjoint) := by
  obtain ⟨k,C,u,p⟩:=p; refine ⟨k,C,u,fun t v w=>?_⟩; rw [ContinuousLinearMap.adjoint.norm_map]; exact p t v w
lemma raw_other (m n : ℕ) : ((rawBlocks S B).op m n).adjoint= (rawBlocks S (fun t=> (B t).adjoint)).op n m:=by
  unfold rawBlocks coldAt; dsimp only; rw [← ContinuousLinearMap.star_eq_adjoint,star_mul,star_mul]; simp only [ContinuousLinearMap.star_eq_adjoint,band_inverse_sym,mul_assoc]

variable (h : Sound S B) (p : PadPaid B)
def field := enact S (rawBlocks S B) (cold_paid S B p h)
def adj := field S (fun t=>(B t).adjoint) (other_sound S B h) (other_price B p)

lemma field_distribution (x : D) : Continuous (fun f:Test4=> (field S B h p f x).1) := distribution ..
lemma field_adjoint (f : Test4) (x y : D) :
    inner ℂ (field S B h p f x).1 y.1 = inner ℂ x.1 (adj S B h p (bar f) y).1 :=
  flip_inner S _ (cold_paid S B p h) _ (cold_paid S _ (other_price B p) (other_sound S B h)) (raw_other S B) f x y
lemma field_closable (f : Test4) : ((bands S).asPartial (field S B h p f)).IsClosable :=
  (bands S).closable _ (adj S B h p (bar f)) (fun x y=> (field_adjoint S B h p f x y).symm)
lemma field_translate (f : Test4) (u : E4) (x : D) : shift S u (field S B h p f x) = field S B h p (ahead u f) (shift S u x) := covariance ..

abbrev stoveAt (t : ℝ≥0) := onDomain S (T t) (heat_cell S t)
lemma stove_price (k : ℕ) (t : ℝ≥0) (x : radial S) :
    (bands S).budget k (stoveAt S t x).1 ≤ (bands S).budget k x.1 :=
  (onDomain_tariff S _ (heat_cell S t) k x).trans (mul_le_of_le_one_left ((bands S).budget_nonneg k _) (S.shrinks t))

/-- Padding identity even before the composed-map limit, on the common domain. -/
lemma exact_stove {u v : ℝ≥0} (hu : 0<u) (hv : 0<v) (f : Test4) (x : D) :
    warm S (bothPads S B u v) f x= stoveAt S u (field S B h p f (stoveAt S v x)) := by
  let V:=smearedBlocks S (rawBlocks S B) f
  let A:=(bands S).dissect (bothPads S B u v)
  have ht:= usableBlocks S _ f (cold_paid S B p h)
  apply Subtype.ext
  change (smearedBlocks S A f).reach x = T u (V.reach (stoveAt S v x))
  unfold Blocks.reach
  rw [(T u).map_tsum (V.series_usable ht _)]
  apply tsum_congr
  rintro ⟨m,n⟩
  change valise S (((bands S).dissect _).op m n) f x.1= T u (valise S ((rawBlocks S B).op m n) f (T v x.1))
  rw [both_recover S B m n hu hv h, overlap_R, overlap]; · rfl
  all_goals exact fun p=> (heat_commutes S _ p).symm

/- Precised radial limits, including independent left/right padding schedules. -/
variable {ι : Type*} (l : Filter ι)

lemma heat_due (t : ℝ≥0) (k n : ℕ) (x : D) : (bands S).due (stoveAt S t x).1 k n ≤ (bands S).due x.1 k n:= by
  unfold Grading.due; rw [band]; change weight k n*‖cell S n (T t x.1)‖≤ _; rw [warm_project]; exact mul_le_mul_of_nonneg_left (((T t).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks t))) (weight_pos k n).le
lemma through_heat (t : ι→ℝ≥0) {a' : ℝ≥0} (e : Tendsto t l (𝓝 a')) {X : ι→D} {x : D} (u : (bands S).Approaches l X x) :
    (bands S).Approaches l (fun i=> stoveAt S (t i) (X i)) (stoveAt S a' x) := by
  refine (bands S).approaches_apply (fun i=> stoveAt S (t i)) (stoveAt S a') (fun k=> ⟨k,1,Eventually.of_forall fun i z=>by rw [one_mul]; exact stove_price S k (t i) z⟩) ?_ u
  intro z k
  let y(i): H:= T (t i) z.1; let w:= T a' z.1
  let F(i:ι)(n:ℕ):= (bands S).due (y i-w) k n
  change Tendsto (fun i=>∑' n,F i n) l (𝓝 0); rw [show (0:ℝ)=∑' _n:ℕ,(0:ℝ) from tsum_zero.symm]
  have hp:Tendsto (fun i=> y i-w) l (𝓝 0):= by simpa only [w,y,Function.comp_apply,sub_self] using (((S.continuousE z.1).tendsto a').comp e).sub_const (T a' z.1)
  refine tendsto_tsum_of_dominated_convergence ((rapid z.2 k).mul_left 2) ?_ (Eventually.of_forall ?_)
  · intro n; unfold F Grading.due; rw [band]; simpa only [Function.comp_apply, map_zero,norm_zero,mul_zero] using (((cell S n).continuous.tendsto 0).comp hp|>.norm|>.const_mul (weight k n))
  intro i n; rw [Real.norm_of_nonneg ((bands S).due_nonneg (y i-w) k n)]; rw [sub_eq_add_neg]; rw [two_mul]; exact ((bands S).due_add _ _ k n).trans (add_le_add (heat_due S (t i) k n z) (((bands S).due_neg _ k n).trans_le (heat_due S a' k n z)))
@[simp] lemma stoveAt_zero (x : radial S) : stoveAt S 0 x=x:= Subtype.ext (DFunLike.congr_fun S.eZero x.1)

lemma enact_through (f : Test4) {X : ι→D} {x : D} (e : (bands S).Approaches l X x) :
    (bands S).Approaches l (fun i=> field S B h p f (X i)) (field S B h p f x):= by
  let V:=field S B h p f
  refine (bands S).approaches_apply (fun _=> V) V ?_ ?_ e
  · intro k
    obtain ⟨r,C,hc,ht⟩:= cold_paid S B p h
    exact ⟨_,_, Eventually.of_forall fun i z=> enact_tariff S _ (cold_paid S B p h) ht _ z k⟩
  intro z k; simp only [sub_self,Grading.budget,Grading.due,map_zero,norm_zero,mul_zero,tsum_zero]; exact tendsto_const_nhds
lemma passes_lim (f : Test4) (s t : ι→ℝ≥0) (e : Tendsto s l (𝓝[>] 0)) (u : Tendsto t l (𝓝[>] 0))
    {X : ι→D} {x : D} (q : (bands S).Approaches l X x) :
    (bands S).Approaches l (fun i=> warm S (bothPads S B (s i) (t i)) f (X i)) (field S B h p f x) := by
  have he:= through_heat S l s (e.mono_right nhdsWithin_le_nhds) (enact_through S B h p l f (through_heat S l t (u.mono_right nhdsWithin_le_nhds) q))
  rw [stoveAt_zero,stoveAt_zero] at he
  intro k
  refine (he k).congr' ?_
  filter_upwards [e.eventually self_mem_nhdsWithin,u.eventually self_mem_nhdsWithin] with i ht hs
  rw [exact_stove S B h p ht hs]
end YM.SatinRegistration

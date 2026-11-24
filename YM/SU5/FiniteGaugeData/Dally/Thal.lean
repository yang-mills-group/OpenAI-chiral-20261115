import YM.SU5.FiniteGaugeData.Dally.Surf
import YM.SU5.FiniteGaugeData.Dally.Inlay
/-!
 # The tensor paper. Opening joint real analyticity with strictly one-dimensional complex price.
 -/
noncomputable section
open Metric Polynomial Function
open scoped Topology NNReal ENNReal
namespace YM.Dally.Thal
open Inlay
variable {D : Type*} [Fintype D] [DecidableEq D]
local notation "Χ" => D → ℂ
local notation "Ξ" => D → ℝ
set_option linter.unusedSectionVars false

def steel (n : ℕ) (r : ℝ) (F : Χ → ℂ) : List D → Χ → ℂ
| [] => F
| a::L => fun x => buzz n r (x a) fun i => steel n r F L (update x a (nail n r i))

def One (n : ℕ) (a : D) (F : Χ → ℂ) : Prop :=
  ∀ x, ∃ p : Polynomial ℂ, p.degree ≤ (n : WithBot ℕ) ∧ ∀ z, F (update x a z) = p.eval z
lemma One.extend {n m : ℕ} {a : D} {F : Χ → ℂ} (hp : One n a F) (hn : n ≤ m) : One m a F :=
  fun x => by obtain ⟨p,h,u⟩ := hp x; exact ⟨p,h.trans (by exact_mod_cast hn),u⟩
lemma One.minus {n : ℕ} {a : D} {F G : Χ → ℂ} (hp : One n a F) (hq : One n a G) :
    One n a (fun x => F x - G x) := by
  intro x
  obtain ⟨p,A,U⟩ := hp x
  obtain ⟨q,B,V⟩ := hq x
  exact ⟨p-q,(degree_sub_le _ _).trans (max_le A B), fun z => by simp only [eval_sub, U, V]⟩
lemma oneQ (n : ℕ) {r} (hr : 0 < r) (F : Χ → ℂ) (L : List D) {a : D} (ha : a ∈ L) :
    One n a (steel n r F L) := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
    intro x
    by_cases h : a = b
    · subst b
      let v i := steel n r F L (update x a (nail n r i))
      use Lagrange.interpolate (pier n) (nail n r) v
      constructor
      · simpa only [pier_card, Nat.add_sub_cancel] using Lagrange.degree_interpolate_le v (inject n hr)
      · intro z
        simp [steel, buzz, v, capstan, Lagrange.interpolate_apply, eval_finsetSum]
    · have A i := ih (List.mem_cons.mp ha |>.resolve_left h) (update x b (nail n r i))
      choose p he ht using A
      let q i := C ((capstan n r i).eval (x b)) * p i
      use ∑ i ∈ pier n, q i
      constructor
      · apply (degree_sum_le _ _).trans
        refine Finset.sup_le fun i hi => ?_
        refine (degree_mul_le ..).trans ?_
        calc
          _ ≤ 0 + (n : WithBot ℕ) := add_le_add degree_C_le (he i)
          _ = _ := zero_add _
      · intro z
        simp only [steel, buzz, update_of_ne (Ne.symm h), eval_finsetSum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [update_comm ?_ _ _ _, ht]
        · simp [q, mul_comm]
        · exact h
lemma repose (n : ℕ) {r} (hr : 0 < r) (F : Χ → ℂ) (L : List D) (h : ∀ a ∈ L, One n a F) :
    steel n r F L = F := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    funext x
    obtain ⟨p,A,U⟩ := h a (by simp) x
    rw [steel, ih fun b hb => h b (by simp [hb])]
    simp_rw [U, buzz_pol hr p A]
    rw [← U, update_eq_self]
lemma shore (n : ℕ) (r) (F : Χ → ℂ) (L : List D) (g : Χ → Χ) (x)
    (hf : AnalyticAt ℂ g x) (h : ∀ i ∉ L, ∀ y, g y i = g x i) :
    AnalyticAt ℂ (fun y => steel n r F L (g y)) x := by
  induction L generalizing g with
  | nil =>
    have : g = fun _ => g x := funext fun i => funext fun a => h a (by simp) i
    simp only [steel]; rw [this]
    exact analyticAt_const
  | cons a L ih =>
    simp only [steel, buzz]
    refine Finset.analyticAt_fun_sum _ fun i _ => .mul (ih _ ?_ ?_) ?_
    · apply analyticAt_pi_iff.mpr
      intro b
      by_cases H : b = a
      · subst b
        simpa only [update_self] using (analyticAt_const : AnalyticAt ℂ (fun _ : Χ => nail n r i) x)
      · simpa [update_of_ne H] using analyticAt_pi_iff.mp hf b
    · intro j hj y
      by_cases H : j = a
      · subst j; simp
      · simp only [update_of_ne H, h j (by simp [H, hj]) y]
    · exact (analyticAt_pi_iff.mp hf a).aeval_polynomial (capstan n r i)

lemma roof {E : Type*} [NormedAddCommGroup E] (x : D → E) (i : D) {r : ℝ} {z : E}
    (hx : ‖x‖ ≤ r) (hz : ‖z‖ ≤ r) : ‖update x i z‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg <| (norm_nonneg _).trans hz).2 ?_
  intro j
  by_cases h : j = i
  · subst j; rwa [update_self]
  rw [update_of_ne h]
  exact (norm_le_pi_norm _ _).trans hx
lemma stapled (F : Χ → ℂ) (n : ℕ) {r} (hr : 0 < r) (L : List D) {K : ℝ} (hk : 0 ≤ K)
    {x : Χ} (hx : ‖x‖ ≤ r) (h : ∀ y, ‖y‖ ≤ r → (∀ i ∉ L, y i = x i) →
      (∀ i ∈ L, (y i).im = 0) → ‖F y‖ ≤ K) :
    ‖steel n r F L x‖ ≤ K * (pine^n)^L.length := by
  induction L generalizing x with
  | nil => simpa [steel] using h x hx (by simp) (by simp)
  | cons a L ih =>
    rw [steel]
    have p := (zero_le_one.trans pine_le)
    refine (buzz_expense hr ((norm_le_pi_norm x a).trans hx) _ (hp := show 0 ≤ K*(pine^n)^L.length from by positivity)
      (fun i hi => ih (roof _ a hx ?_) ?_)).trans (le_of_eq ?_)
    · simpa [nail] using port hi hr
    · intro y hy o u
      refine h y hy (fun j hj => ?_) ?_
      · rw [o _ (by simp at hj; tauto), update_of_ne (by simp at hj; tauto)]
      · intro j hj
        by_cases H : j ∈ L
        · exact u j H
        have e : j = a := by simpa [H] using hj
        rw [o j H, e, update_self]; simp [nail]
    · simp [pow_succ, mul_assoc]
def WickR (y : Ξ) : Χ := fun i => y i
def rim (y : Χ) : Ξ := fun i => (y i).re
@[simp] lemma rim_WickR (y : Ξ) : rim (WickR y) = y := rfl
lemma WickR_rim {x : Χ} (h : ∀ i, (x i).im = 0) : WickR (rim x) = x := by
  funext i; apply Complex.ext <;> simp [WickR, rim, h]
lemma rim_le (y : Χ) : ‖rim y‖ ≤ ‖y‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  fun i => ((Complex.abs_re_le_norm (y i)).trans (norm_le_pi_norm y i))
lemma WickR_up (y : Ξ) (i : D) (z : ℝ) :
    WickR (update y i z) = update (WickR y) i (z:ℂ) :=
  Function.comp_update _ _ _ _
lemma WickR_norm (y : Ξ) : ‖WickR y‖ = ‖y‖ :=
  le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    (fun i => by simpa [WickR] using norm_le_pi_norm y i)) (rim_le (WickR y))
/-- Separate pricing at one fixed R, K. Need one common cost with the other arguments
    also displaced in the real cube. -/
def Yare (R K : ℝ) (f : Ξ → ℂ) : Prop :=
  ∀ x, ‖x‖ ≤ R → ∀ a : D, ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (closedBall 0 R) ∧
    (∀ z ∈ closedBall (0 : ℂ) R, ‖F z‖ ≤ K) ∧ ∀ z : ℝ, |z| ≤ R → F z = f (update x a z)
/-- interpolate over stencil of order n (list contains every coordinate eventually). -/
def aging (f : Ξ → ℂ) (n : ℕ) (r : ℝ) (L : List D) (x : Χ) : ℂ := steel n r (f ∘ rim) L x
lemma ledgers {R K r : ℝ} {f : Ξ → ℂ} (h : Yare R K f) (hr : 0 < r) (hl : r < R)
    (hk : 0 ≤ K) (n : ℕ) (L : List D) {x : Ξ} (hx : ‖x‖ ≤ r) :
    ‖aging f n r L (WickR x) - f x‖ ≤
     (2*plume K R r*L.length) * ((pine*(r/R))*pine^L.length)^n := by
  let b := pine^n
  let u := 2*plume K R r*(pine*(r/R))^n
  have H (d:ℕ) : (2*plume K R r*d) * ((pine*(r/R))*pine^d)^n = d*u*b^d := by
    dsimp [b,u]
    ring
  have Bs : 1 ≤ b := one_le_pow₀ pine_le
  have B : 0 ≤ b := zero_le_one.trans Bs
  have U : 0 ≤ u := by
    dsimp [u]; have := plume_nn hk hr hl; have := hr.trans hl; have := zero_le_one.trans pine_le; positivity
  rw [H]
  induction L generalizing x with
  | nil => simp [aging, steel]
  | cons a L ih =>
    let y i := update x a (joist n r i)
    have Y i hi : ‖y i‖ ≤ r := roof _ a hx (port hi hr)
    obtain ⟨F,A,I,O⟩ := h x (hx.trans hl.le) a
    let q i := aging f n r L (WickR (y i))
    have Q : aging f n r (a :: L) (WickR x) = buzz n r ((x a:ℝ):ℂ) q := by
      simp [aging, steel, q, y, WickR_up, nail]; rfl
    have M : |x a| ≤ r := (norm_le_pi_norm x a).trans hx
    have N : ‖((x a:ℝ):ℂ)‖ ≤ r := by simpa using M
    have X : F (x a) = f x := by rw [O _ (M.trans hl.le), update_eq_self]
    have Fp : buzz n r ((x a:ℝ):ℂ) (fun i => f (y i)) = buzz n r (x a:ℂ)
        (fun i => F (nail n r i)) := buzz_congr _ _ (fun i hi => (O _ ((port hi hr).trans hl.le)).symm)
    have V : ‖buzz n r (x a:ℂ) (fun i => q i-f (y i))‖ ≤ (L.length*u*b^L.length)*b :=
      buzz_expense hr N _ (by positivity) fun i hi => ih (Y i hi)
    have ν := hiss n hr hl A hk I N
    rw [buzz_sub] at V
    rw [Q, ← X, List.length_cons]
    calc
      _ = ‖(buzz n r ((x a:ℝ):ℂ) q - buzz n r (x a:ℂ) (fun i => f (y i))) +
          (buzz n r (x a:ℂ) (fun i => F (nail n r i)) - F (x a))‖ := by rw [Fp, sub_add_sub_cancel]
      _ ≤ (L.length*u*b^L.length)*b + u := (norm_add_le ..).trans (add_le_add V ν)
      _ ≤ (L.length*u*b^L.length)*b + u*b^(L.length+1) := add_le_add le_rfl
        (le_mul_of_one_le_right U (one_le_pow₀ Bs))
      _ = _ := by push_cast; ring
def roller (f : Ξ → ℂ) (r : ℝ) (L : List D) (n : ℕ) (x : Χ) : ℂ :=
  aging f (n+1) r L x - aging f n r L x
def sate (f : Ξ → ℂ) (r : ℝ) (L : List D) (x : Χ) : ℂ :=
  (∑' n, roller f r L n x) + aging f 0 r L x

lemma peak {R K r : ℝ} {f : Ξ → ℂ} (h : Yare R K f) (hr : 0 < r) (hl : r < R)
    (hk : 0 ≤ K) {L : List D} (hs : ∀ i, i ∈ L)
    (hrR : ((pine*(r/R))*pine^L.length)*pine^L.length < 1)
    (n) {x : Χ} (hx : ‖x‖ ≤ r) :
    ‖roller f r L n x‖ ≤ (4*plume K R r*L.length*pine^L.length)*
      (((pine*(r/R))*pine^L.length)*pine^L.length)^n := by
  let c := pine * (r/R)*pine^L.length
  let M : ℝ := 2*plume K R r*L.length
  have p := zero_lt_one.trans_le pine_le
  have c0 : 0 ≤ c := by dsimp [c]; have := hr.trans hl; positivity
  have c1 : c < 1 := lt_of_le_of_lt (le_mul_of_one_le_right c0 (one_le_pow₀ pine_le (n:=L.length))) hrR
  have m : 0 ≤ M := by dsimp [M]; have := plume_nn hk hr hl; positivity
  have E y (hy : ‖(y:Ξ)‖ ≤ r) : ‖roller f r L n (WickR y)‖ ≤ 2*(M*c^n) := by
    have A : ‖aging f (n+1) r L (WickR y) - f y‖ ≤ M*c^n := le_trans
      (ledgers h hr hl hk (n+1) L hy) (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one c0 c1.le (Nat.le_succ _)) m)
    have B := ledgers h hr hl hk n L hy
    unfold roller
    rw [← sub_sub_sub_cancel_right _ _ (f y), two_mul]
    exact (norm_sub_le ..).trans (add_le_add A B)
  have H : steel (n+1) r (roller f r L n) L = roller f r L n := repose _ hr _ _ fun a ha =>
    (oneQ (n+1) hr (f ∘ rim) L ha).minus ((oneQ n hr (f ∘ rim) L ha).extend (by omega))
  have A := stapled (roller f r L n) (n+1) hr L (show 0 ≤ 2*(M*c^n) from by positivity) hx
    fun y hy _ h' => by
      have Z := E (rim y) ((rim_le y).trans hy)
      rwa [WickR_rim (fun i => h' i (hs i))] at Z
  rw [H] at A
  refine A.trans (le_of_eq ?_)
  dsimp [M,c]
  ring
lemma sate_glove {R K r : ℝ} {f : Ξ → ℂ} (h : Yare R K f) (hr : 0 < r) (hl : r < R)
    (hk : 0 ≤ K) {L : List D} (hs : ∀ i, i ∈ L)
    (hrR : ((pine*(r/R))*pine^L.length)*pine^L.length < 1) :
    AnalyticOnNhd ℂ (sate f r L) (ball 0 r) ∧
      ∀ y : Ξ, ‖y‖ ≤ r → sate f r L (WickR y) = f y := by
  let c := pine*(r/R)*pine^L.length
  have p := zero_lt_one.trans_le pine_le
  have c0 : 0 ≤ c := by dsimp [c]; have := hr.trans hl; positivity
  let M := 4*plume K R r*L.length*pine^L.length
  let u n := M*(c*pine^L.length)^n
  have U : Summable u := (summable_geometric_of_lt_one (r := c*pine^L.length) (by positivity)
    hrR).mul_left _
  have ν (n y) (hy : ‖y‖ ≤ r) : ‖roller f r L n y‖ ≤ u n := peak h hr hl hk hs hrR _ hy
  have Λ n x : AnalyticAt ℂ (aging f n r L) x :=
    shore n r _ _ id x analyticAt_id (by intro i hi; exact False.elim (hi (hs i)))
  constructor
  · intro x hx
    have X : ‖x‖ < r := by simpa [mem_ball, dist_eq_norm] using hx
    apply AnalyticAt.add (f := fun z => ∑' n, roller f r L n z) _ (Λ 0 x)
    apply Surf.amber _ u (R := r - ‖x‖) (sub_pos.mpr X) U (fun i y _ => (Λ (i+1) y).sub (Λ i y))
    intro n y hy
    refine ν n y ?_
    have := dist_triangle y x 0
    simp only [dist_zero_right, mem_closedBall] at *
    linarith
  intro y hy
  let a (n : ℕ) := aging f n r L (WickR y)
  have A : Filter.Tendsto a Filter.atTop (nhds <| f y) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero (fun _ => norm_nonneg _)
      (fun n => ledgers h hr hl hk n L hy) ?_
    have C1 := lt_of_le_of_lt (le_mul_of_one_le_right c0 (one_le_pow₀ pine_le (n:=L.length))) hrR
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one c0 C1).const_mul
      (2*plume K R r*L.length)
  have hab : Summable fun n => roller f r L n (WickR y) := (U.of_nonneg_of_le
    (fun _ => norm_nonneg _) fun n => ν n (WickR y) (by rwa [WickR_norm])).of_norm
  unfold sate
  refine eq_sub_iff_add_eq.mp <| tendsto_nhds_unique hab.hasSum.tendsto_sum_nat ?_
  have HA n : ∑ i ∈ Finset.range n, roller f r L i (WickR y) = a n - a 0 :=
    Finset.sum_range_sub a n
  simp_rw [HA]
  exact A.sub_const _
lemma gulf {R K : ℝ} {f : Ξ → ℂ} (h : Yare R K f) (hr : 0 < R) (hk : 0 ≤ K) :
    AnalyticAt ℝ f 0 := by
  let L := (Finset.univ : Finset D).toList
  let r := R/(4*pine*pine^L.length*pine^L.length)
  have p := zero_lt_one.trans_le pine_le
  have r0 : 0 < r := by dsimp [r]; positivity
  have rR : r < R := by
    have H := one_le_pow₀ (n:=L.length) pine_le
    apply div_lt_self hr
    calc
      1 < 4*(1:ℝ)*1*1 := by norm_num
      _ ≤ 4*pine*pine^L.length*pine^L.length := by gcongr; first|exact H|exact pine_le
  obtain ⟨A,B⟩ := sate_glove (r:=r) h r0 rR hk (L:=L) (by simp [L]) (by
    dsimp only [r]
    field_simp
    nlinarith [pow_pos p L.length])
  have t := A 0 (mem_ball_self r0)
  have H : AnalyticAt ℂ (sate f r L) (WickR 0) := by
    rw [show WickR (0:Ξ) = 0 by ext i; simp [WickR]]
    exact t
  have V : AnalyticAt ℝ (sate f r L ∘ WickR) 0 := H.restrictScalars.comp
    (analyticAt_pi_iff.mpr fun i => (Complex.ofRealCLM.analyticAt _).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ:=fun _ => ℝ) i).analyticAt _))
  apply V.congr
  filter_upwards [ball_mem_nhds (0:Ξ) r0] with y hy
  exact B y (by simpa [mem_ball, dist_eq_norm] using (ball_subset_closedBall hy))
end YM.Dally.Thal

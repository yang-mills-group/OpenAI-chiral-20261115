import GaugeFieldConstruction.Gap
import GaugeFieldConstruction.ProductData

/-!
# Linear equations hold off the point for the W2 curls and two chirals
  germs are in z=y-x, with x for *first* leg.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Wick
open Gap Finset Filter Set Complex Cauchy Row
open YM.Maxwell (Green normal)
open scoped Topology ContDiff BigOperators

def stone := lit Green fun _ px=> YM.Maxwell.freeSmooth px
lemma flashStone (i : Axis) {x} (p : x≠0) : eye x (Gap.step i stone)=((YM.Maxwell.grad i Green x:ℝ):ℂ) := by
  unfold stone; rw [light]; exact lap _ (fun y h=> YM.Maxwell.grad_smooth i (YM.Maxwell.freeSmooth h) (by simp)) p
lemma sumD : ∑ i : Axis, Gap.step i (Gap.step i stone)=0 := by
  apply eyes; intro z hz
  rw [map_sum,map_zero]; unfold stone
  simp_rw [light]
  have he (i) : eye z (lit (YM.Maxwell.grad i (YM.Maxwell.grad i Green)) (fun x p=> YM.Maxwell.HessSmooth p i i))=_ := lap _ (fun x p=> YM.Maxwell.HessSmooth p i i) hz
  simp_rw [he]; norm_cast
  exact YM.Maxwell.harmonic hz
lemma even : opp stone=stone := by
  apply individuated; intro z hz
  change stone.val _=stone.val z; unfold stone; rw [lap _ _ (neg_ne_zero.mpr hz),lap _ _ hz,YM.Maxwell.even_Green]

/-- angle identity without paying spin or Slot basis. -/
lemma flash₁ (i j : Axis) (a b : Spin) : (∑ c:Spin, Hij i a c*star (Hij j b c))+
    (∑ c:Spin,Hij j a c*star (Hij i b c))= if i=j ∧ a=b then 2 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;> norm_num [Hij]
lemma flash₂ (i j : Axis) (a b : Spin) : (∑ c:Spin,Hij i c a *star (Hij j c b))+
    (∑ c:Spin,Hij j c a *star (Hij i c b))= if i=j ∧ a=b then 2 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;> norm_num [Hij]

/-- W2 right order C at x, R at y. Slot suppressed. -/
def blend (a b : Spin) : SmoothGap := ∑ i : Axis, (-(16:ℂ) * star (Hij i a b)) • Gap.step i stone

lemma revision (a b : Spin) : opp (blend a b) = -blend a b := by
  unfold blend; simp only [map_sum, map_smul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro i _
  have h := recur i stone; rw [even] at h
  nth_rw 2 [h]; rw [smul_neg,neg_neg]

def thread (b : Bool) (a c : Spin) := if b then -opp (blend c a) else blend a c
lemma thread_un (a c : Spin) : thread false a c=blend a c := rfl
lemma thread_on (a c : Spin) : thread true a c=blend c a := by simp only [thread,if_true,revision,neg_neg]

lemma present (t : Bool) (a b : Spin) : thread t a b= ∑ j :Axis,(-16 * star (coeffCR t j b a)) • Gap.step j stone := by
  cases t
  · rw [thread_un]; unfold blend; rfl
  rw [thread_on]; unfold blend; rfl

lemma flip_braid (t : Bool) (i j : Spin) : -opp (thread (!t) j i) = thread t i j := by
  cases t <;> simp [thread,revision]

/-- pay Dirac at left leg. -/
lemma braid (b : Bool) (a h : Spin) : (∑ i:Axis, ∑ c:Spin, coeffCR b i a c • Gap.step i (thread b c h))=0 := by
  let L (i j : Axis) := Gap.step i (Gap.step j stone)
  have hw (i j) : L i j=L j i:=LinearMap.congr_fun (Gap.collide i j) _
  let X (i j : Axis) := ∑ c:Spin, coeffCR b i a c * star (coeffCR b j h c)
  have ht (i j) : X i j+X j i=if i=j ∧ a=h then 2 else 0 := by
    cases b
    · exact flash₂ ..
    exact flash₁ ..
  have he (i) : ∑ c:Spin, coeffCR b i a c • Gap.step i (thread b c h)=
      (-16:ℂ) • ∑ j:Axis,X i j • L i j := by
    simp_rw [present, map_sum,map_smul, Finset.smul_sum]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    dsimp only [X]; rw [smul_smul,Finset.mul_sum, Finset.sum_smul]; apply Finset.sum_congr rfl; intro c _
    rw [smul_smul]; dsimp only [L]; congr 1; ring
  simp_rw [he,← Finset.smul_sum]
  suffices A : ∑ i:Axis, ∑ j:Axis,X i j • L i j=0 by rw [A,smul_zero]
  have hv : (2:ℂ) • (∑ i:Axis, ∑ j:Axis,X i j • L i j) = 0 := by
    rw [two_smul]; nth_rw 2 [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]; simp_rw [← Finset.sum_add_distrib]
    have hk (i j) : X i j • L i j+ X j i • L j i= (if i=j ∧ a=h then (2:ℂ) else 0) • L i j := by rw [hw j,← add_smul,ht]
    simp_rw [hk]; by_cases p:a=h
    · simp only [p,and_true,ite_smul,zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      rw [← Finset.smul_sum]; change (2:ℂ) • (∑ i:Axis, Gap.step i (Gap.step i stone)) = (0:SmoothGap); rw [sumD,smul_zero]
    simp [p]
  exact (smul_eq_zero.mp hv).resolve_left (by norm_num)
lemma second (b : Bool) (c a : Spin) :
    ∑ i:Axis, ∑ d:Spin, coeffCR (!b) i a d • Gap.step i (thread b c d)=0 := by
  cases b <;> simp only [thread_on,thread_un,Bool.not_false,Bool.not_true]
  · simpa only [thread_on] using braid true a c
  simpa only [thread_un] using braid false a c

/-- W2, g kernel. bareCurl is even so use at the same gap as everything. -/
def curl (a b k m : Axis) := lit (YM.Maxwell.bareCurl a b k m) fun _ p=> YM.Maxwell.Bare.curl_diff p a b k m
lemma swirl (a b k m : Axis) {x} (p : x≠0) : (opp (curl k m a b)).val x=(curl a b k m).val x := by
  change (curl k m a b).val _=_; unfold curl; rw [lap _ _ (neg_ne_zero.mpr p),lap _ _ p,YM.Maxwell.Bare.even p, YM.Maxwell.Bare.exchange p a b]

/-- independent of our coordinates. -/
structure Solution (t : Axis→Axis→SmoothGap) : Prop where
  sign :∀ a b, t a b = - t b a
  closes :∀ i j k, Gap.step i (t j k)+Gap.step j (t k i)+Gap.step k (t i j)=0
  sum :∀ j, ∑ i : Axis, Gap.step i (t i j) = 0

lemma from_WaveOn {t : YM.Maxwell.Field ℝ} (h : YM.Maxwell.WaveOn YM.Maxwell.away t) :
    Solution fun a b => lit (t a b) (h.smooth a b) := by
  constructor
  · intro a b; apply individuated; intro z hz
    change (lit _ _).val z= -(lit _ _).val z
    rw [lap _ _ hz, lap _ _ hz,h.form a b z hz]; simp
  · intro i j k; apply eyes; intro z hz
    have he (a b c : Axis) (hf) : eye z (Gap.step a (lit (t b c) hf)) = ((YM.Maxwell.grad a (t b c) z:ℝ):ℂ) := by
      rw [light]; exact lap _ (fun x p=> YM.Maxwell.grad_smooth _ (hf x p) (by simp)) hz
    simp_rw [map_add,map_zero,he, ← ofReal_add,h.cycle i j k z hz] -- cycle
    simp
  intro j; apply eyes; intro z hz
  have he (a b c : Axis) (hf) : eye z (Gap.step a (lit (t b c) hf)) = ((YM.Maxwell.grad a (t b c) z:ℝ):ℂ) := by
    rw [light]; exact lap _ (fun x p=> YM.Maxwell.grad_smooth _ (hf x p) (by simp)) hz
  simp_rw [map_sum,map_zero,he,← ofReal_sum, h.divergence j z hz]; simp

lemma curlLeft (k m : Axis) : Solution (fun i j => curl i j k m):= from_WaveOn (YM.Maxwell.Bare.equation k m)
lemma curlRight (k m : Axis) : Solution (fun i j => curl k m i j):= from_WaveOn (YM.Maxwell.Bare.equation_right k m)
end YM.GaugeFieldConstruction.Wick

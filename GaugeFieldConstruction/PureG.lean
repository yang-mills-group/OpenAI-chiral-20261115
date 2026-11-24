import GaugeFieldConstruction.ShellReg

/-!
# U3 g normalized shell flux, singular contraction to one leg
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.Photo
open Gap Complex Function Filter Set YM.Analysis MeasureTheory
open YM.Maxwell YM.Maxwell.Free
open scoped Topology BigOperators ContDiff
variable {U : Set E4} {χ : E4→ℝ}

-- U,V are already scalar contractions (vectors complex values)
local notation "S" => YM.Maxwell.Field ℂ
local notation "CV" => YM.Maxwell.Free.cure

/-- Complex contractions (no conjugation!). g flux linear each input. -/
def bip (F G : S) (a b : Axis) (x : E4) :=
    (∑ c : Axis, (F a c x * G b c x + F b c x * G a c x)) -
       (if a=b then (1/2:ℂ) * ∑ i : Axis, ∑ j : Axis, F i j x * G i j x else 0)
lemma flipped (F G : S) (a b : Axis) (x : E4) : bip F G a b x=bip F G b a x := by
  unfold bip; simp only [add_comm (F b _ x*_ : ℂ), eq_comm (a:=b) (b:=a)]
lemma regular {F G : S} {x : E4} (H : ∀ a b,ContDiffAt ℝ ∞ (F a b) x) (K : ∀ a b,ContDiffAt ℝ ∞ (G a b) x) (i j : Axis) :
    ContDiffAt ℝ ∞ (bip F G i j) x := by
  unfold bip
  by_cases p:i=j <;> simp only [p, ↓reduceIte]
  all_goals
    apply ContDiffAt.sub; apply ContDiffAt.sum; intro c _
    exact ((H _ _).mul (K _ _)).add ((H _ _).mul (K _ _))
  exact contDiffAt_const.mul (ContDiffAt.sum (fun i _=> ContDiffAt.sum (fun j _=> (H _ _).mul (K _ _))))
  exact contDiffAt_const

lemma varias (F G : S) (H : Bianchi U F) (K : Bianchi U G) (hU : IsOpen U) (b : Axis) {x : E4} (p : x∈U) :
    ∑ a : Axis,∑ c:Axis,F a c x* grad a (G b c) x=(1/2:ℂ)* ∑ a:Axis,∑ c:Axis,F a c x* grad b (G a c) x := by
  have he (a c): grad a (G b c) x = grad b (G a c) x - grad c (G a b) x := by
    have hw:= K.cycle a b c x p; nth_rw 1 [grad_skew K hU b c a p] at hw
    linear_combination hw
  let R:= ∑ a:Axis, ∑ c:Axis,F a c x* grad a (G b c) x
  have hk : ∑ a:Axis, ∑ c:Axis,F a c x*grad c (G a b) x=R := by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro c _
    rw [H.skew c a x p, grad_skew K hU a c b p,neg_mul_neg]
  have ht : R=(∑ a:Axis,∑ c:Axis,F a c x* grad b (G a c) x)-R := by
    conv_lhs=> unfold R; rhs; intro i; rhs; intro c; rw [he]
    simp_rw [mul_sub,Finset.sum_sub_distrib,hk]
  change R=_; linear_combination ht / 2

lemma turns {F G : S} (H : Bianchi U F) (K : Bianchi U G) (hU : IsOpen U) (b : Axis) {x : E4} (p : x∈U) :
    div (bip F G) b x = ∑ c:Axis,(F b c x*divF G c x + G b c x*divF F c x) := by
  let CF (a) (T L : S) := bip (fun c d=>grad a (T c d)) L a b x
  have hb (a : Axis) : grad a (bip F G a b) x = CF a F G + CF a G F := by
    unfold bip
    have h (a c d j): grad a (fun z=> ∑ i:Axis,(F c i z*G d i z+F d i z*G j i z)) x=
        ∑ i : Axis,(grad a (F c i) x * G d i x + F c i x*grad a (G d i) x+
          (grad a (F d i) x * G j i x+F d i x*grad a (G j i) x)) := by
      have he (a b c d):ContDiffAt ℝ ∞ (fun z=> F a b z*G c d z) x:= (H.smooth a b x p).mul (K.smooth c d x p) -- adjust syntax
      rw [here_sum (f:=fun i z=>F c i z*G d i z+F d i z*G j i z) (fun i _=>(he c i d i).add (he d i j i))]
      apply Finset.sum_congr rfl; intro i _
      rw [← here_mul a (H.smooth c i x p) (K.smooth d i x p),← here_mul a (H.smooth d i x p) (K.smooth j i x p)]
      unfold grad D
      rw [fderiv_fun_add ((he c i d i).differentiableAt (by simp)) ((he d i j i).differentiableAt (by simp))]; rfl
    let Z (a b : Axis) (z:E4):= ∑ i:Axis,(F a i z*G b i z+F b i z*G a i z)
    let V (z : E4):= (1/2:ℂ)* ∑ i:Axis, ∑ j:Axis,F i j z*G i j z
    have pc (a b) :ContDiffAt ℝ ∞ (Z a b) x:= ContDiffAt.sum fun i _=> ((H.smooth a i x p).mul (K.smooth b i x p)).add ((H.smooth b i x p).mul (K.smooth a i x p))
    have pd : ContDiffAt ℝ ∞ V x:= contDiffAt_const.mul (ContDiffAt.sum (fun i _=>ContDiffAt.sum (fun j _=> (H.smooth i j x p).mul (K.smooth i j x p))))
    have pw : grad a V x= (1/2:ℂ)* ∑ i:Axis,∑ j :Axis,(grad a (F i j) x*G i j x+ F i j x*grad a (G i j) x) := by
      let g i j z:= F i j z * G i j z
      have ph (i j): ContDiffAt ℝ ∞ (g i j) x:= (H.smooth i j x p).mul (K.smooth i j x p)
      have pg i:ContDiffAt ℝ ∞ (fun z=>∑ j:Axis,g i j z) x:= ContDiffAt.sum (fun j _=> ph i j)
      have pe:= here_mul a (contDiffAt_const (x:=x) (c:=(1/2:ℂ))) (show ContDiffAt ℝ ∞ (fun z=>∑ i:Axis, ∑ j:Axis,g i j z) x from ContDiffAt.sum fun i _=> pg i)
      change grad a V x=_ at pe
      rw [pe, show grad a (fun _ : E4=> (1/2:ℂ)) x=0 from by simp [grad,D],zero_mul,zero_add]
      rw [here_sum (v:=Finset.univ) (fun i _=>pg i)]
      simp_rw [here_sum (v:=Finset.univ) (fun j _=> ph _ j)] -- tweak infer
      congr 1; apply Finset.sum_congr rfl; intro i _; exact Finset.sum_congr rfl fun j _=> here_mul _ (H.smooth _ _ x p) (K.smooth _ _ x p)
    have hp : grad a (Z a b) x=_:=h a a b a
    dsimp only [CF]; simp only [bip]
    by_cases hv:a=b
    · simp only [if_pos hv]; rw [here_sub a (pc a b) pd,hp,pw]; simp only [Finset.sum_add_distrib,mul_comm]; ring
    simp only [if_neg hv,sub_zero]; change grad a (Z a b) x=_; rw [hp]; simp only [Finset.sum_add_distrib,mul_comm]; ring
  have hw (F G:S) (H:Bianchi U F) (K:Bianchi U G) : ∑ a:Axis, CF a F G = ∑ c:Axis,G b c x*divF F c x := by
    dsimp only [CF,bip]; simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _),divF,Finset.mul_sum]
    have h := varias G F K H hU b p
    -- identity catches G a c * d_a F b c
    simp_rw [Finset.mul_sum] at h; rw [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f:=fun a c=> grad a (F a c) x * G b c x)]
    simp only [mul_comm] at h ⊢
    linear_combination h
  simp_rw [YM.GaugeFieldConstruction.Flux.div,sumD,hb, Finset.sum_add_distrib]; rw [hw F G H K,hw G F K H,add_comm]
end YM.GaugeFieldConstruction.Flux.Photo

namespace YM.GaugeFieldConstruction.Flux.Photo
open Gap Complex Function Filter Set YM.Analysis MeasureTheory
open YM.Maxwell YM.Maxwell.Free
open scoped Topology BigOperators ContDiff
variable {U : Set E4} {χ : E4→ℝ} {F : Forms} (K : Dollars)

-- electric/magnetic probe any leg.
def powerPay (k l : Axis) (F : Forms) (x : E4) :=
    ∑ i : Axis,(K i x • grad i (F k l) x + grad k (K i) x • F i l x + grad l (K i) x • F k i x)

def fire (F : Forms) (j : Axis) (z : E4) := ∑ i:Axis,K i z • F i j z

lemma add_shift {f : FunC} {x y : E4} {a : Axis} (H :ContDiffAt ℝ ∞ f (y-x)) :
    grad a (fun y=> f (y-x)) y = grad a f (y-x) := by
  change fderiv ℝ (f ∘ ((·-x) : E4→E4)) y _ = _
  have ht: HasFDerivAt ((·-x) : E4→ E4) (ContinuousLinearMap.id ℝ E4) y:= (hasFDerivAt_id y).sub_const _
  rw [fderiv_comp y (H.differentiableAt (by simp)) ht.differentiableAt,ht.fderiv]; rfl
lemma blare {f : E4→ℝ} (j : Axis) {x : E4} (p : ContDiffAt ℝ ∞ f x) : grad j (fun y=>(f y:ℂ)) x = ((grad j f x:ℝ):ℂ) := by
  unfold grad D; rw [show (fun y=>(f y:ℂ))=ofRealCLM ∘ f from rfl,fderiv_comp _ ofRealCLM.differentiableAt (p.differentiableAt (by simp)), ofRealCLM.fderiv]; rfl

lemma buds (v : Course K) (p : WaveOn U F) (hU : IsOpen U) {x} (hx : x∈U) (a b : Axis) :
    grad a (fire K F b) x-grad b (fire K F a) x=powerPay K a b F x := by
  have he (a b : Axis) : grad a (fire K F b) x=∑ i : Axis,(grad a (K i) x • F i b x+ K i x • grad a (F i b) x):= (here_sum (v:=Finset.univ) (f:=fun i z=> K i z • F i b z) (fun i _=>(v.health i).contDiffAt.smul (p.smooth i b x hx)) _).trans (Finset.sum_congr rfl (fun i _=>here_dollar (v.health i).contDiffAt (p.smooth i b x hx) a))
  rw [he,he,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _
  have ht: grad a (F i b) x-grad b (F i a) x= grad i (F a b) x:= by
    have H := p.cycle a b i x hx; nth_rw 1 [grad_skew (wave_closed p) hU a b i hx] at H; linear_combination -H
  rw [← ht,smul_sub]; rw [p.form i a x hx,smul_neg]; abel

def placed (t : ℝ) (x : E4) (k l : Axis) : Forms := fun a b y => ((cure t k l a b (y-x)):ℂ)
lemma pose (t : ℝ) (ht : 0<t) (k l a b : Axis) (x z:E4):ContDiffAt ℝ ∞ (fun y=> cure t k l a b (y-x)) z := ((cure_law ht k l).smooth a b (z-x) (mem_univ _)).comp z (g:=cure t k l a b) (f:=fun y=>y-x) (contDiffAt_id.sub contDiffAt_const)
lemma placedG {t : ℝ} (h : 0<t) (x : E4) (k l a b s : Axis) (z) : grad s (placed t x k l a b) z = ((grad s (cure t k l a b) (z-x):ℝ) : ℂ) := by
  unfold placed; rw [blare s (pose t h k l a b x z),shift_gradient ((cure_law h k l).smooth a b _ (mem_univ _))]
lemma placedB {t : ℝ} (h : 0<t) (x : E4) (k l) : Bianchi U (placed t x k l) := by
  have he:=cure_law h k l
  refine ⟨fun i j z _=> ofRealCLM.contDiff.contDiffAt.comp z (pose t h k l i j x z),?_,?_⟩
  · intro a b y hy; unfold placed; rw [he.skew a b _ (mem_univ _)]; simp
  intro a b c y hy; rw [placedG h,placedG h,placedG h]; norm_cast; exact he.cycle a b c (y-x) (mem_univ _)
lemma placedD {t:ℝ} (h : 0<t) (x : E4) (k l i) (z : E4):
    divF (placed t x k l) i z=(↑(kr l i) * ↑(grad k (soul t x) z:ℝ) - ↑(kr k i)* ↑(grad l (soul t x) z:ℝ):ℂ) := by
  have he (i : Axis):grad i (soul t x) z = grad i (source t) (z-x) := shift_gradient ((source_diff h).contDiffAt.of_le le_top)
  unfold divF; simp_rw [placedG h,he]; norm_cast; exact cure_charge h ..

def fused (F : Forms) (k l i : Axis) (y:E4):=(if i=k then fire K F l y else 0)-(if i=l then fire K F k y else 0)
lemma fromG {t:ℝ} (h : 0<t) (x) (H : Course K) (A : WaveOn U F) (u : IsOpen U) (k l : Axis) {z} (p : z∈U):
    sumD (currentZ K (bip F (placed t x k l))) z = ∑ i:Axis,(grad i (soul t x) z:ℝ) • fused K F k l i z := by
  have B:=placedB (U:=U) h x k l
  rw [submitting p H (fun i j z hz=>regular (fun r s=>A.smooth r s z hz) (fun r s=> B.smooth r s z hz) _ _) (fun i j=>flipped ..)]
  simp_rw [turns (wave_closed A) B u _ p]
  have e (a : Axis): divF F a z=0 := A.divergence a z p
  simp_rw [placedD h, e]
  unfold fused kr; simp [smul_sub,Finset.sum_sub_distrib,mul_sub,smul_ite] -- see
  have h (a b : Axis) : (↑(if a=b then (1:ℝ) else 0) : ℂ)=if a=b then 1 else 0 := by split_ifs <;> simp
  simp [h,ite_mul,mul_ite, fire,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc]

lemma solder (x : E4) (b : Cost χ) (r : tsupport χ ⊆ U) (w : χ =ᶠ[𝓝 x] fun _=>1) (H : Course K) (A : WaveOn U F) (k l):
    Continuous (fun t : ℝ=>Flux χ (currentZ K (bip F (placed t x k l)))) := by
  apply circles b; intro a z hz
  have h : x≠z.2 := fun ht=> collar w (ht ▸ gradient_part χ a hz)
  have h' (i j): ContinuousAt (fun y : ℝ × E4 => placed y.1 x k l i j y.2) z := by
    have H : ContinuousAt (fun y : ℝ×E4=> (y.1,y.2-x)) z := by fun_prop
    exact ofRealCLM.continuous.continuousAt.comp ((cure_continuous k l i j (z:=(z.1,z.2-x)) (sub_ne_zero.mpr h.symm)).comp (f:=fun y : ℝ × E4 => (y.1,y.2-x)) H)
  have U i j : ContinuousAt (fun y : ℝ×E4=> F i j y.2) z := (A.smooth _ _ _ (r (tsupport_fderiv_subset ℝ (gradient_part χ a hz)))).continuousAt.comp continuousAt_snd
  unfold currentZ bip
  have sum {q : Axis→ ℝ × E4→ℂ} (e : ∀ i ∈ (Finset.univ:Finset Axis),ContinuousAt (q i) z): ContinuousAt (fun y=> ∑ i : Axis,q i y) z := tendsto_finsetSum _ e
  apply sum; intro j _; apply ((H.health j).continuous.comp continuous_snd).continuousAt.smul
  by_cases hp:a=j <;> simp only [hp, ↓reduceIte]
  all_goals apply ContinuousAt.sub; exact sum (fun c _=> ((U _ _).mul (h' _ _)).add ((U _ _).mul (h' _ _)))
  exact continuousAt_const.mul (sum (fun i _=> sum fun j _=> (U i j).mul (h' i j)))
  exact continuousAt_const

/-- Maxwell shell, singular at leg x, complex value. -/
theorem arc_pay (x : E4) (b : Cost χ) (H : Course K) (A : WaveOn U F) (u : IsOpen U)
    (r : tsupport χ ⊆ U) (w : χ =ᶠ[𝓝 x] fun _=>1) (k l : Axis) :
    Flux χ (currentZ K (bip F (placed 0 x k l)))=powerPay K k l F x := by
  let T t:=bip F (placed t x k l)
  have hv (a z) (h : z∈tsupport χ): ContDiffAt ℝ ∞ (fire K F a) z:= ContDiffAt.sum fun i _=> (H.health i).contDiffAt.smul (A.smooth i a z (r h))
  let p:= fused K F k l
  have he (j z) (g : z∈tsupport χ) : ContDiffAt ℝ ∞ (p j) z:= by unfold p fused; split_ifs <;> apply ContDiffAt.sub <;> first|exact contDiffAt_const| apply hv _ _ g
  have hx:= rates b x w (fun t=>currentZ K (T t)) 0 p (fun _ _=>contDiffAt_const) he (solder K x b r w H A k l)
    (fun t ht a z v=> daily H (T t) (fun i => regular (fun i j=> A.smooth i j z (r v)) (fun i j=> (placedB ht x k l).smooth i j z (r v)) a i)) (fun t ht z hz=>by rw [Pi.zero_apply,smul_zero,zero_add]; exact fromG K ht x H A u k l (r hz))
  rw [← buds K H A u (r (enclosed x w))]; change Flux χ (currentZ K (T 0))= _; rw [hx]; change sumD p x-0=_; rw [sub_zero]
  have ep (i):grad i (p i) x=(if i=k then grad i (fire K F l) x else 0)-(if i=l then grad i (fire K F k) x else 0):= by
    have eh (q : Prop) [Decidable q] (a):ContDiffAt ℝ ∞ (fun z=> if q then fire K F a z else 0) x := by
      split_ifs
      · exact hv a x (enclosed x w)
      exact contDiffAt_const -- layout
    unfold p fused; rw [here_sub i (eh (i=k) l) (eh (i=l) k)]
    split_ifs <;> simp [grad,D]
  unfold sumD; simp_rw [ep]; simp [Finset.sum_sub_distrib]
end YM.GaugeFieldConstruction.Flux.Photo

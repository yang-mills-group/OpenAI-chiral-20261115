import GaugeFieldConstruction.PureG
/-!
# Divergence of f currents for equations on legs. Both kinds paid alike.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.Tissue
open Gap Complex Function Filter Set Finset YM.Analysis MeasureTheory
open YM.Maxwell (grad)
open Cauchy Row
open scoped Topology BigOperators ContDiff
variable {U : Set E4} {B : Dollars}
abbrev Rtil := Spin → FunC
/-- M direction writes smooth leg a, singular b,
 transpose matrix when paying variation on R. -/
abbrev M (b : Bool) (i a c) := coeffCR b i c a
def sig (b : Bool) (U : Rtil) (c : Spin) (x : E4) := ∑ i:Axis,∑ a:Spin,M b i a c * grad i (U a) x
structure Law (b : Bool) (f : Rtil) (U : Set E4) : Prop where
  health (i : Spin) (x : E4) : x∈U→ContDiffAt ℝ ∞ (f i) x
  way (i : Spin) (x : E4) : x∈U→ sig b f i x=0

lemma even_M (b i a c) : M (!b) i a c=M b i c a:= by cases b <;> rfl
lemma flashM (b i j a d) : (∑ c :Spin, M b i a c * star (M b j d c))+ (∑ c:Spin,M b j a c*star (M b i d c))= if i=j∧a=d then 2 else 0 := by
  cases b
  · exact Wick.flash₁ ..
  exact Wick.flash₂ ..

lemma ko {f : FunC} {x} (h : ContDiffAt ℝ ∞ f x) (k) : ContDiffAt ℝ ∞ (grad k f) x := YM.Maxwell.grad_smooth _ h (by simp)
lemma flip (i j : Axis) {f : FunC} {x} (h : ContDiffAt ℝ ∞ f x) : grad i (grad j f) x= grad j (grad i f) x:= YM.Maxwell.grad_comm (h.of_le (show ((↑(2 : ℕ)) : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) ..
lemma const_add {f : FunC} {x} (r : ℂ) (h : ContDiffAt ℝ ∞ f x) (i): grad i (fun x=> r*f x) x = r* grad i f x := by
  rw [here_mul i contDiffAt_const h]; simp [YM.Maxwell.grad,D]
lemma sigGrad {f : Rtil} (b) (i c) {z} (p : ∀ a,ContDiffAt ℝ ∞ (f a) z): grad i (sig b f c) z=
    ∑ j:Axis, ∑ a:Spin, M b j a c* grad i (grad j (f a)) z := by
  let x (j a) (z:E4):=M b j a c * grad j (f a) z
  have h (j a):ContDiffAt ℝ ∞ (x j a) z:=contDiffAt_const.mul (ko (p a) j)
  change grad i (fun z=> ∑ j:Axis, ∑ a:Spin,x j a z) z=_
  rw [here_sum (f:= fun j z=>∑ a:Spin,x j a z) (fun j _=>ContDiffAt.sum (fun a _=> h j a))]
  apply Finset.sum_congr rfl; intro j _; rw [here_sum (f:=x j) (fun a _=>h j a)]; exact Finset.sum_congr rfl fun a _=>const_add _ (ko (p a) j) i
lemma sigma (b : Bool) (g : Axis → Axis → ℂ) (h : ∀ i j,g i j=g j i) (a d : Spin) :
    ∑ i : Axis, ∑ c : Spin,M b i a c * ∑ j : Axis,star (M b j d c)*g i j=if a=d then ∑ i:Axis,g i i else 0 := by
  let P (i j:Axis):= ∑ c : Spin, M b i a c * star (M b j d c)
  have hp (i j) : P i j + P j i = _ := flashM b i j a d
  have he (i): (∑ c:Spin,M b i a c*∑ j : Axis,star (M b j d c)*g i j)=∑ j:Axis,P i j*g i j := by
    simp_rw [Finset.mul_sum,P, Finset.sum_mul,mul_assoc] -- syntax
    exact Finset.sum_comm
  simp_rw [he]
  apply mul_left_cancel₀ (show (2:ℂ)≠0 from by norm_num)
  rw [two_mul]; nth_rw 2 [Finset.sum_comm]; rw [← Finset.sum_add_distrib]; simp_rw [← Finset.sum_add_distrib]
  have hh (i j):P i j * g i j + P j i * g j i= if i=j ∧ a=d then 2*g i j else 0 := by rw [h j i,← add_mul,hp]; split_ifs <;> simp
  simp_rw [hh]; by_cases p:a=d <;> simp [p,Finset.mul_sum]

lemma dh (b : Bool) {f : Rtil} {z} (h :∀ a,ContDiffAt ℝ ∞ (f a) z) (k : Spin) :
    ∑ i:Axis, ∑ a:Spin,star (M b i k a)*grad i (sig b f a) z=∑ i:Axis,grad i (grad i (f k)) z := by
  have he (i a) :star (M b i k a)*grad i (sig b f a) z=
      ∑ p:Spin,∑ j:Axis, star (M b i k a)*(M b j p a*grad i (grad j (f p)) z) := by
    rw [sigGrad b i a h]; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
  have eg (y : Spin) :
      ∑ i:Axis,∑ a:Spin,∑ j:Axis,star (M b i k a)*(M b j y a*grad i (grad j (f y)) z)=if y=k then ∑ i:Axis,grad i (grad i (f y)) z else 0 := by
    rw [← sigma b (fun i j=> grad i (grad j (f y)) z) (fun i j=> flip _ _ (h y)) y k]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm,Finset.sum_comm (f:=fun i (a:Spin)=> ∑ j:Axis, M b i y a *(star (M b j k a)*grad i (grad j (f y)) z))]
    apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _
    rw [flip i j (h y)]; ring
  simp_rw [he, Finset.sum_comm (f:=fun a p : Spin=> ∑ j:Axis, star (M b _ k a)* (M b j p a* grad _ (grad j (f p)) z))] -- pattern underscores
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single k]
  · rw [eg,if_pos rfl]
  · intro y _ p; rw [eg,if_neg p]
  simp

def shape (b : Bool) (u v : Rtil) (i j : Axis) (x : E4) := ∑ a : Spin,∑ c:Spin,M b i a c * (u a x * grad j (v c) x-grad j (u a) x * v c x)
def force (b) (u v : Rtil) (i j : Axis) (x : E4) := (-1/64:ℂ)*(shape b u v i j x+shape b u v j i x)
lemma healthy (b) {u v : Rtil} {x} (p : ∀ i,ContDiffAt ℝ ∞ (u i) x) (q : ∀ i,ContDiffAt ℝ ∞ (v i) x) (i j) :ContDiffAt ℝ ∞ (shape b u v i j) x := ContDiffAt.sum fun a _=> ContDiffAt.sum (fun c _=>contDiffAt_const.mul (((p a).mul (ko (q c) j)).sub ((ko (p a) j).mul (q c))))
lemma fresh (b) {u v : Rtil} {x} (p : ∀ i,ContDiffAt ℝ ∞ (u i) x) (q : ∀ i,ContDiffAt ℝ ∞ (v i) x) (i j) : ContDiffAt ℝ ∞ (force b u v i j) x := contDiffAt_const.mul ((healthy b p q i j).add (healthy b p q j i))
lemma switch (b : Bool) (u v i j x) : force b u v i j x= force b u v j i x := by simp [force,add_comm]
lemma ortho {x} (i j) (b : Bool) {u : Rtil} (l : Law b u U) (hU : IsOpen U) (p : x∈U) :
    grad i (sig b u j) x = 0 := by
  apply Eq.trans (GermD (basis i) (show sig b u j=ᶠ[𝓝 x] fun _=>0 from ?_))
  · simp [D]
  filter_upwards [hU.mem_nhds p] with z hz; exact l.way j z hz

lemma variation (b) {u v : Rtil} {x : E4} (p : ∀ i,ContDiffAt ℝ ∞ (u i) x) (q : ∀ i, ContDiffAt ℝ ∞ (v i) x) (i j k) :
    grad i (shape b u v j k) x = shape b (fun a=>grad i (u a)) v j k x + shape b u (fun c=>grad i (v c)) j k x := by
  unfold shape
  let f (a c : Spin) (x : E4) := u a x*grad k (v c) x-grad k (u a) x * v c x
  let F (a c : Spin) x := M b j a c*f a c x
  have hp a c : ContDiffAt ℝ ∞ (f a c) x := ((p a).mul (ko (q c) k)).sub ((ko (p a) k).mul (q c))
  have ht a c :ContDiffAt ℝ ∞ (F a c) x:= contDiffAt_const.mul (hp a c)
  change grad _ (fun x=> ∑ a:Spin,∑ c:Spin,F a c x) x=_
  rw [here_sum (v:=Finset.univ) (fun a _=> show ContDiffAt ℝ ∞ (fun y=>∑ c:Spin,F a c y) x from ContDiffAt.sum fun c _=> ht a c),← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro a _
  rw [here_sum (f:=F a) (fun c _=> ht a c),← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro c _
  unfold F
  rw [const_add _ (hp a c), show grad i (f a c) x=_ from here_sub i ((p a).mul (ko (q c) k)) ((ko (p a) k).mul (q c)),here_mul i (p a) (ko (q c) k), here_mul i (ko (p a) k) (q c)]
  rw [flip i k (p a),flip i k (q c)]; ring
lemma first (b) {u v : Rtil} {x : E4} (p : Law b u U) (q : ∀ i,ContDiffAt ℝ ∞ (v i) x) (hU : IsOpen U) (h : x∈U) (j) :
    ∑ i:Axis, grad i (shape b u v i j) x= ∑ a:Spin, (u a x * grad j (sig (!b) v a) x-grad j (u a) x * sig (!b) v a x) := by
  have hu a:=p.health a x h
  have he (c): ∑ i:Axis,∑ a:Spin,M b i a c * grad j (grad i (u a)) x=0 := by rw [← sigGrad b j c hu,ortho j c b p hU h]
  have hf: ∑ i:Axis, shape b (fun a=>grad i (u a)) v i j x=0 := by
    unfold shape; simp_rw [Finset.sum_comm (f:=fun a c : Spin=> M b _ a c * _)] -- maybe includes others
    rw [Finset.sum_comm]; apply Finset.sum_eq_zero; intro c _
    have k : (∑ i:Axis,∑ a:Spin,M b i a c*(grad i (u a) x*grad j (v c) x-grad j (grad i (u a)) x*v c x)) = sig b u c x*grad j (v c) x-grad j (sig b u c) x * v c x := by
      simp only [mul_sub,Finset.sum_sub_distrib,sigGrad _ _ _ hu,sig, ← mul_assoc,Finset.sum_mul]
    rw [k,p.way c x h,ortho j c b p hU h]; simp
  simp_rw [variation b hu q]; rw [Finset.sum_add_distrib,hf,zero_add]; unfold shape; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _
  rw [sigGrad _ j a q]; unfold sig
  have ht (i : Axis) (c : Spin) (y:ℂ) : M b i a c * (grad j (u a) x*y)=grad j (u a) x*(M (!b) i c a*y) := by rw [even_M]; ring
  have hw (i : Axis) (c : Spin) (y:ℂ) : M b i a c * (u a x * y)=u a x* (M (!b) i c a*y):= by rw [even_M]; ring
  simp_rw [mul_sub,Finset.sum_sub_distrib,ht,hw,Finset.mul_sum]
lemma last (b) {u v : Rtil} {x : E4} (p : Law b u U) (q : ∀ i,ContDiffAt ℝ ∞ (v i) x) (hU : IsOpen U) (h : x∈U) (j) :
    (∑ i:Axis,grad i (shape b u v j i) x) = ∑ a:Spin,∑ c:Spin,M b j a c*(u a x * ∑ k : Axis, grad k (grad k (v c)) x) := by
  have hu a:=p.health a x h
  simp_rw [variation b hu q] -- syntax we need i j i
  have he (a : Spin) : ∑ k:Axis,grad k (grad k (u a)) x=0 := by rw [← dh b hu a]; simp [ortho _ _ b p hU h]
  simp only [shape]; simp_rw [← Finset.sum_add_distrib]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro c _
  have ht (i : Axis) : M b j a c*(grad i (u a) x * grad i (v c) x-grad i (grad i (u a)) x*v c x)+
      M b j a c*(u a x*grad i (grad i (v c)) x-grad i (u a) x*grad i (v c) x)= M b j a c*(u a x*grad i (grad i (v c)) x-grad i (grad i (u a)) x*v c x):=by ring
  simp_rw [ht,← Finset.mul_sum,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,he]; simp

def eta : ℂ := -16
def bud (a b :Spin) (s : FunC) : FunC:= if a=b then fun x=>eta*s x else 0
/-- spin motion matrix upper indices; (M transposed when hitting R). -/
def payP (b : Bool) (K : Dollars) (a : Spin) (u : Rtil) (x : E4) :=
    ∑ i : Axis, (K i x • grad i (u a) x + (1/4:ℂ)*∑ j:Axis, grad i (K j) x • (∑ r:Spin,∑ c:Spin, u r x*M b j r c*star (M b i a c)))

lemma force_law {u v : Rtil} (b) (p : Law b u U) (q : ∀ c y,y∈U→ContDiffAt ℝ ∞ (v c) y) (s : FunC)
    (g : ∀ y∈U, ContDiffAt ℝ ∞ s y) (a : Spin) (t : ∀ i x,x∈U→sig (!b) v i x = bud i a s x)
    (w : IsOpen U) {x} (h : x∈U) (j) :
    YM.GaugeFieldConstruction.Flux.div (force b u v) j x = (1/4:ℂ)*(u a x*grad j s x-grad j (u a) x*s x+
      ∑ i:Axis,grad i s x*(∑ r:Spin,∑ c:Spin, u r x*M b j r c*star (M b i a c))) := by
  have hu i:=p.health i x h; have hv i:=q i x h
  have hp (i : Axis) (c:Spin): grad i (sig (!b) v c) x=if c=a then eta*grad i s x else 0 := by
    rw [show grad i (sig (!b) v c) x= grad i (bud c a s) x from GermD _ (by filter_upwards [w.mem_nhds h] with z hz; exact t c z hz)]
    unfold bud; split_ifs; exact const_add _ (g x h) _
    simp [YM.Maxwell.grad,D]
  have hQ (i : Axis): grad i (force b u v i j) x= (-1/64:ℂ)*(grad i (shape b u v i j) x +grad i (shape b u v j i) x):= by
    unfold force; rw [const_add _ ((healthy b hu hv i j).add (healthy b hu hv j i))]; unfold YM.Maxwell.grad D; rw [fderiv_fun_add ((healthy b hu hv i j).differentiableAt (by simp)) ((healthy b hu hv j i).differentiableAt (by simp))]; rfl
  have ha (c) : sig (!b) v c x = if c=a then eta*s x else 0 := by rw [t c x h,bud]; split_ifs <;> rfl
  simp_rw [YM.GaugeFieldConstruction.Flux.div,sumD,hQ,← Finset.mul_sum, Finset.sum_add_distrib, first b p hv w h j, last b p hv w h j,← dh (!b) hv]
  simp_rw [hp,ha]
  have ht (i c): M (!b) i c a=M b i a c:= even_M ..
  simp only [mul_ite,mul_zero,sum_ite_eq', Finset.mem_univ,↓reduceIte,ite_self,ht, sub_zero, Finset.sum_sub_distrib]
  have H : (∑ r:Spin,∑ c:Spin,M b j r c * (u r x * ∑ i:Axis,star (M b i a c)*(eta*grad i s x)))= eta * ∑ i:Axis,grad i s x * ∑ r:Spin, ∑ c:Spin, u r x*M b j r c*star (M b i a c) := by
    simp_rw [Finset.mul_sum, Finset.sum_comm (f:=fun c i=> M b j _ c*(_*(star (M b i a c)*(eta*grad i s x))))]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro r _; exact Finset.sum_congr rfl fun c _=>by ring
  rw [H]; unfold eta; ring
end YM.GaugeFieldConstruction.Flux.Tissue

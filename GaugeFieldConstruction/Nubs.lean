import GaugeFieldConstruction.PureF
/-!
# Portals in singular spin shell, both types.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.Tissue
open YM.Analysis MeasureTheory Set Filter Complex Function Cauchy
open YM.Maxwell (grad)
open YM.Maxwell.Free (soften source)
open scoped ContDiff Topology BigOperators
variable {U : Set E4} {χ : E4→ℝ} {x : E4} {u : Rtil} {K : Dollars} {b : Bool}

def jewel (b : Bool) (x : E4) (k : Spin) (t : ℝ) : Rtil := fun a z=>16*∑ i :Axis, star (M b i k a)*↑(grad i (soften t) (z-x) : ℝ)
lemma gems {t : ℝ} {b a k} (h : 0<t) (x y : E4) : ContDiffAt ℝ ∞ (jewel b x k t a) y := by
  have he (i : Axis) := YM.Maxwell.grad_smooth i (YM.Maxwell.Free.soften_diff h |>.contDiffAt (x:=y-x)) (m:=∞) le_top
  exact contDiffAt_const.mul (ContDiffAt.sum fun i _=> contDiffAt_const.mul (ofRealCLM.contDiff.contDiffAt.comp _ ((he i).comp y (f:=fun z=>z-x) (contDiffAt_id.sub contDiffAt_const))))

lemma jewelG {t : ℝ} (b a k i) (x y:E4) (hs : ContDiffAt ℝ ∞ (soften t) (y-x)) :
    grad i (jewel b x k t a) y = 16 *∑ j : Axis,star (M b j k a)* ↑(grad i (grad j (soften t)) (y-x):ℝ) := by
  let f (j : Axis) z:= grad j (soften t) (z-x)
  have hg j :ContDiffAt ℝ ∞ (grad j (soften t)) (y-x):= YM.Maxwell.grad_smooth _ hs (by simp)
  have hh j:ContDiffAt ℝ ∞ (f j) y:= (hg j).comp y (f:=fun z=>z-x) (contDiffAt_id.sub contDiffAt_const)
  have he j:ContDiffAt ℝ ∞ (fun z => ((f j z):ℂ)) y:= ofRealCLM.contDiff.contDiffAt.comp y (hh j)
  have hp j : ContDiffAt ℝ ∞ (fun z:E4=> star (M b j k a)*↑(f j z)) y := contDiffAt_const.mul (he j)
  change grad i (fun z=>16*∑ j:Axis,star (M b j k a) * ↑(f j z)) y=_
  rw [const_add 16 (ContDiffAt.sum (fun j _=> hp j)),here_sum (fun j _=>hp j) i]
  congr 1; apply Finset.sum_congr rfl; intro j _
  rw [const_add _ (he j),Photo.blare _ (hh j)]; dsimp only [f]; rw [YM.Maxwell.Free.shift_gradient (hg j)]

lemma jewel_in (b x k y t) (h : 0 < t) (a) : sig (!b) (jewel b x k t) a y= bud a k (fun z=> ↑(soul t x z)) y := by
  have hs : ContDiffAt ℝ ∞ (soften t) (y-x):= (YM.Maxwell.Free.soften_diff h).contDiffAt.of_le le_top
  let Q (i j : Axis) := ↑(grad i (grad j (soften t)) (y-x):ℝ) + (0:ℂ) -- simplify
  have he := sigma b (fun i j=>((grad i (grad j (soften t)) (y-x):ℝ):ℂ)) (fun i j=> congr_arg ((↑):ℝ→ℂ) (YM.Maxwell.grad_comm (hs.of_le (show ((↑(2 : ℕ)) : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) i j)) a k
  unfold sig; simp_rw [jewelG b _ k _ x y hs,even_M, mul_left_comm (M b _ a _) (16:ℂ), ← Finset.mul_sum]; rw [he]
  have ht: ∑ i:Axis,grad i (grad i (soften t)) (y-x)= -soul t x y := congr_fun (YM.Maxwell.Free.minus_lap h) (y-x)
  by_cases p:a=k <;> simp only [bud,p,↓reduceIte, ← ofReal_sum]; rw [ht]; simp [eta]
  simp

/-- local along cut-support, including t=0. -/
lemma polish {z : ℝ × E4} (h : x≠z.2) (b k a) :
    ContinuousAt (fun z : ℝ × E4=> jewel b x k z.1 a z.2) z := by
  apply continuousAt_const.mul
  refine tendsto_finsetSum _ (fun i _=> ?_)
  let F := fun z : ℝ × E4=> grad i (soften z.1) (z.2-x)
  have he: ContinuousAt F z := by
    let L := fun z : ℝ × E4=> -2 * YM.Maxwell.normal * (z.2-x) i * (z.1^2+‖z.2-x‖^2)⁻¹^2
    have hh : ContinuousAt (fun z : ℝ × E4 => (z.1^2+‖z.2-x‖^2)⁻¹) z := by
      have p':0< ‖z.2-x‖:= norm_pos_iff.mpr (sub_ne_zero.mpr h.symm)
      apply ContinuousAt.inv₀; fun_prop
      positivity
    have hv : ContinuousAt L z := by unfold L; fun_prop
    refine hv.congr ?_; filter_upwards [continuousAt_snd.eventually_ne h.symm] with y hy
    have p :0< ‖y.2-x‖:= norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    unfold F; rw [YM.Maxwell.Free.soften_first (by positivity)]
  exact continuousAt_const.mul (ofRealCLM.continuous.continuousAt.comp he)
lemma spin_polish {z : ℝ × E4} (h:x≠z.2) (b k a i) :
    ContinuousAt (fun z : ℝ × E4 => grad i (jewel b x k z.1 a) z.2) z := by
  let L j (z : ℝ × E4) := grad i (grad j (soften z.1)) (z.2-x)
  have hh (j : Axis) : ContinuousAt (L j) z := by
    let X := fun w : ℝ × E4=> -2 * YM.Maxwell.normal * basis i j * (w.1^2+‖w.2-x‖^2)⁻¹^2 +
      8*YM.Maxwell.normal * (w.2-x) i * (w.2-x) j * (w.1^2+‖w.2-x‖^2)⁻¹^3 -- parentheses formula inspect
    have ht : ContinuousAt (fun w : ℝ × E4 => (w.1^2+‖w.2-x‖^2)⁻¹) z := by
      have p':0< ‖z.2-x‖:= norm_pos_iff.mpr (sub_ne_zero.mpr h.symm)
      apply ContinuousAt.inv₀; fun_prop
      positivity
    have hp: ContinuousAt X z:= by unfold X; fun_prop
    refine hp.congr ?_; filter_upwards [continuousAt_snd.eventually_ne h.symm] with y hy
    have p:0< ‖y.2-x‖:=norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    unfold L X; rw [YM.Maxwell.Free.soften_second (by positivity)]
  have he:ContinuousAt (fun w=> 16 * ∑ j:Axis,star (M b j k a) * ↑(L j w)) z := continuousAt_const.mul (show ContinuousAt (fun w=> ∑ j:Axis,star (M b j k a)* ↑(L j w)) z from tendsto_finsetSum _ (fun j _=> (continuousAt_const.mul (ofRealCLM.continuous.continuousAt.comp (hh j))) )) -- tweak
  apply he.congr; filter_upwards [continuousAt_snd.eventually_ne h.symm] with y hy
  have p:0< ‖y.2-x‖:=norm_pos_iff.mpr (sub_ne_zero.mpr hy)
  refine Eq.symm (jewelG b a k i _ _ ?_)
  exact contDiffAt_const.mul ((contDiffAt_const.add (contDiff_norm_sq ℝ).contDiffAt).inv (f:=fun v:E4=> y.1^2+‖v‖^2) (by positivity))

lemma f_circles (h : Law b u U) (v : Cost χ) (d : tsupport χ ⊆ U) (p : χ =ᶠ[𝓝 x] fun _=>1) (sk : Course K) (k) : Continuous (fun t=>Flux χ (currentZ K (force b u (jewel b x k t)))) := by
  apply circles v; intro a z hz
  have hn:x≠z.2 := fun e=> YM.Maxwell.Free.collar p (e ▸ YM.Maxwell.Free.gradient_part χ a hz)
  have hu:= d (tsupport_fderiv_subset ℝ (YM.Maxwell.Free.gradient_part χ a hz))
  have sum {α : Type} [Fintype α] {g : α → ℝ × E4 → ℂ} (h : ∀ i,ContinuousAt (g i) z): ContinuousAt (fun w=> ∑ i,g i w) z:= tendsto_finsetSum _ (fun i _=> h i)
  have he i j : ContinuousAt (fun w : ℝ×E4 =>shape b u (jewel b x k w.1) i j w.2) z:=by
    unfold shape; apply sum; intro c; apply sum; intro d
    exact continuousAt_const.mul ((((h.health c _ hu).continuousAt.comp continuousAt_snd).mul (spin_polish hn b k d j)).sub (((ko (h.health c _ hu) j).continuousAt.comp continuousAt_snd).mul (polish hn b k d)))
  unfold currentZ force; apply sum; intro j; exact ((sk.health j).continuous.comp continuous_snd).continuousAt.smul (continuousAt_const.mul ((he a j).add (he j a)))

def spin (b : Bool) (u : Rtil) (j i : Axis) (a : Spin) (z : E4) :=∑ r:Spin,∑ c:Spin,u r z*M b j r c*star (M b i a c)
lemma spin_h (b) (p :∀ i,ContDiffAt ℝ ∞ (u i) x) (i j k) : ContDiffAt ℝ ∞ (spin b u i j k) x:= ContDiffAt.sum (fun r _=> ContDiffAt.sum fun c _=> ((p r).mul contDiffAt_const).mul contDiffAt_const)
lemma dot_sp (h : Law b u U) (p : x∈U) (a j) : ∑ i:Axis, grad i (spin b u j i a) x=2*grad j (u a) x := by
  have H r c d i : ContDiffAt ℝ ∞ (fun y=>u r y*M b j r c*star (M b i d c)) x:= ((h.health r x p).mul contDiffAt_const).mul contDiffAt_const
  have he (i): grad i (spin b u j i a) x=∑ r:Spin,∑ c:Spin, grad i (u r) x * M b j r c * star (M b i a c) := by
    unfold spin; rw [here_sum (v:=Finset.univ) (f:=fun r z=> ∑ c:Spin,u r z*M b j r c*star (M b i a c)) (fun r _=> ContDiffAt.sum fun c _=>H r c a i)]
    apply Finset.sum_congr rfl; intro r _; rw [here_sum (f:=fun c y=>u r y*M b j r c * star (M b i a c)) (fun c _=> H r c a i)]
    apply Finset.sum_congr rfl; intro c _; rw [here_mul i (((h.health r x p).mul contDiffAt_const)) contDiffAt_const,here_mul i (h.health r x p) contDiffAt_const]; simp [YM.Maxwell.grad,D]
  let P (j i:Axis) (r a:Spin):= ∑ c: Spin,M b j r c*star (M b i a c)
  have z: ∑ i:Axis,∑ r:Spin,grad i (u r) x*P i j r a = 0 := by
    unfold P; simp_rw [Finset.mul_sum,← mul_assoc]; simp_rw [Finset.sum_comm (f:=fun r c : Spin=>grad _ (u r) x * M _ _ r c * _)]
    rw [Finset.sum_comm]; apply Finset.sum_eq_zero; intro c _
    have hp : (∑ i:Axis, ∑ r:Spin, grad i (u r) x * M b i r c) = sig b u c x:= Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl (fun r _=> mul_comm ..)
--    rw [← Finset.sum_mul]; -- adjust nesting
    simp_rw [← Finset.sum_mul]; rw [hp,h.way c x p,zero_mul]
  have hu i r : P j i r a + P i j r a =if j=i∧r=a then 2 else 0:=flashM ..
  simp_rw [he,mul_assoc,← Finset.mul_sum];
  change ∑ i:Axis,∑ r:Spin,grad i (u r) x*P j i r a = _
  rw [show ∑ i:Axis,∑ r:Spin,grad i (u r) x*P j i r a= (∑ i:Axis,∑ r:Spin,grad i (u r) x*P j i r a)+0 from (add_zero _).symm,← z,← Finset.sum_add_distrib]; simp_rw [← Finset.sum_add_distrib,← mul_add,hu,ite_and,mul_ite]
  simp [Finset.sum_ite_irrel,mul_comm]

-- charges. use explicit, easy algebra on coefficient.
def fees (K : Dollars) (u : Rtil) (b : Bool) (a : Spin) (i : Axis) (z : E4) :=
    (1/4:ℂ)*(K i z • u a z + ∑ j:Axis,K j z • spin b u j i a z)
def eyes (K : Dollars) (u : Rtil) (a : Spin) (z:E4) := -(1/4:ℂ)* ∑ j:Axis,K j z • grad j (u a) z
lemma crossing (H : Course K) (d : Law b u U) (p : x∈U) (a) : sumD (fees K u b a) x - eyes K u a x= payP b K a u x := by
  have he i : grad i (fees K u b a i) x = (1/4:ℂ)*(K i x • grad i (u a) x+∑ j:Axis,(grad i (K j) x • spin b u j i a x+K j x • grad i (spin b u j i a) x)) := by
    let v j z:= K j z • spin b u j i a z
    have hd j: ContDiffAt ℝ ∞ (v j) x:= (H.health j).contDiffAt.smul (spin_h b (fun i=>d.health i x p) j i a)
    have hp: ContDiffAt ℝ ∞ (fun z=> ∑ j : Axis,v j z) x:= ContDiffAt.sum (fun j _=> hd j)
    have hv: ContDiffAt ℝ ∞ (fun z=> K i z • u a z) x := (H.health i).contDiffAt.smul (d.health a x p)
    change grad i (fun z=> (1/4:ℂ)*(K i z • u a z+∑ j:Axis,v j z)) x=_
    rw [const_add _ (hv.add hp)]
    have hr : grad i (fun z=>K i z • u a z + ∑ j:Axis,v j z) x= grad i (fun z=> K i z • u a z) x+ grad i (fun z=>∑ j:Axis,v j z) x:= by unfold YM.Maxwell.grad D; rw [fderiv_fun_add (hv.differentiableAt (by simp)) (hp.differentiableAt (by simp))]; rfl
    rw [hr,here_dollar (H.health i).contDiffAt (d.health a x p) i,show grad i (K i) x=0 from by have hm:=H.skew i i x; linarith,zero_smul,zero_add,here_sum (f:=v) (fun j _=> hd j)]
    congr 2; exact Finset.sum_congr rfl fun j _=> here_dollar (H.health j).contDiffAt (spin_h b (fun i=> d.health i x p) j i a) i
  unfold sumD eyes payP; simp_rw [he,← Finset.mul_sum,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f:=fun i j : Axis=>K j x • grad i (spin b u j i a) x)]; simp_rw [← Finset.smul_sum (s:=Finset.univ) (r:=K _ x), dot_sp d p a]
  have hw (i : Axis): K i x • (2 * grad i (u a) x)=2*(K i x • grad i (u a) x) := by simp; ring
  simp_rw [hw, ← Finset.mul_sum]; unfold spin; ring

lemma regF (h : Law b u U) (P : Course K) (p : IsOpen U) (a : Spin) (s : E4) (t : ℝ) (ht : 0<t) (hx : x∈U) :
    sumD (currentZ K (force b u (jewel b s a t))) x= soul t s x • eyes K u a x+∑ i:Axis, grad i (soul t s) x • fees K u b a i x := by
  let B:=jewel b s a t
  let f : FunC:= fun x=> ↑(soul t s x)
  have g z (_ : z∈U): ContDiffAt ℝ ∞ f z := ofRealCLM.contDiff.contDiffAt.comp z (tune ht s).contDiffAt
  have hu i z (_:z∈U) : ContDiffAt ℝ ∞ (B i) z:= gems ht s z
  rw [submitting hx P (fun i j y v=> fresh b (fun a=> h.health a y v) (fun a=> hu a y v) i j) (fun i j=>switch ..)]
  have he j:= force_law b h hu f g a (fun i x _=> jewel_in b s a x t ht i) p hx j
  change ∑ i:Axis,K i x • YM.GaugeFieldConstruction.Flux.div (force b u B) i x=_
  have hp (j : Axis): grad j f x= ((grad j (soul t s) x:ℝ):ℂ):= Photo.blare _ (tune ht s |>.contDiffAt)
  simp_rw [he,hp]; change ∑ j:Axis,K j x • ((1/4:ℂ)*(u a x* ↑(grad j (soul t s) x)- grad j (u a) x * ↑(soul t s x) + ∑ i:Axis,(↑(grad i (soul t s) x) : ℂ)*spin b u j i a x)) = _
  simp_rw [fees, eyes]
  -- rewrite scalar & sum comm
  simp only [real_smul,smul_eq_mul,mul_add,Finset.sum_add_distrib,mul_sub, Finset.sum_sub_distrib,Finset.mul_sum]
  rw [Finset.sum_comm]; simp only [neg_mul,mul_neg,Finset.sum_neg_distrib,mul_left_comm,mul_comm,mul_assoc]; abel


theorem income (hU : IsOpen U) (h : Law b u U) (v : Cost χ) (d : tsupport χ ⊆ U) (p : χ =ᶠ[𝓝 x] fun _=>1) (sk : Course K) (k : Spin) :
    Flux χ (currentZ K (force b u (jewel b x k 0)))=payP b K k u x := by
  refine Eq.trans (rates v x p (fun t=> currentZ K (force b u (jewel b x k t))) (eyes K u k) (fees K u b k) ?_ ?_ (f_circles h v d p sk k) ?_ ?_) (crossing sk h (d (YM.Maxwell.Free.enclosed x p)) k)
  · intro z hz; exact contDiffAt_const.mul (ContDiffAt.sum fun i _=> (sk.health i).contDiffAt.smul (ko (h.health k z (d hz)) i))
  · intro i z hz; exact contDiffAt_const.mul (((sk.health i).contDiffAt.smul (h.health k z (d hz))).add
      (ContDiffAt.sum fun j _=> (sk.health j).contDiffAt.smul (spin_h b (fun i=>h.health i z (d hz)) j i k)))
  · intro t ht a z hz; apply daily sk; intro j; exact fresh b (fun i=> h.health i _ (d hz)) (fun i=> gems ht x z) _ _
  intro t ht z hz; exact regF h sk hU k x t ht (d hz)
end YM.GaugeFieldConstruction.Flux.Tissue

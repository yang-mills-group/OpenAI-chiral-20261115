import YM.SU5.Reconstruction.Trap.Bounded
/-!
# SOT and multiplying
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Multiplier
open Function Set Filter MeasureTheory Spectral Analysis
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {X ι : Type*} [MeasurableSpace X] {H : Hilbert} (P : PVM H X)
local notation "𝔪" x:max => P.diagonal x
variable {P}
namespace Registers
variable {f g : X→ℂ}{U V : H.Op}
lemma comm (h:Registers P f U) {s:Set X} (v:MeasurableSet s): Commute U (P.region s):= by
 obtain ⟨W,h',q⟩:= find P f h.price; rw [h.single h']; exact q v
lemma times (h:Registers P f U) (p:Registers P g V): Registers P (f*g) (U*V):= by
 let y(n):= SimpleFunc.approxOn f h.price.meas Set.univ 0 (mem_univ _) n
 have ht(x:X):Tendsto (fun n=> y n x) atTop (𝓝 (f x)):= SimpleFunc.tendsto_approxOn h.price.meas (s:=univ) _ (by simp)
 obtain ⟨c,v,b⟩:= h.price.bound; obtain ⟨d,k,q⟩:=p.price.bound
 have e(i x):‖y i x‖≤c+c:=(SimpleFunc.norm_approxOn_zero_le _ _ _ _).trans (add_le_add (b x) (b x))
 obtain ⟨A,t⟩:=reader P y f (c+c) (add_nonneg v v) e ht
 have hu: U=A:= h.single (onLimit P _ _ _ f h.price (c+c) (Eventually.of_forall e) ht (fun i=> records P _) t)
 apply onLimit P (fun i=> hit P (y i)*V) atTop (fun i=> ((y i): X→ℂ)*g) _ (h.price.times p.price) ((c+c)*d) (Eventually.of_forall fun i x => (norm_mul ((y i) x) (g x)).trans_le (mul_le_mul (e i x) (q x) (norm_nonneg _) (by positivity))) (fun x=> (ht x).mul tendsto_const_nhds) (fun i=> masks P p (fun {_} => p.comm) (y i)); rw [hu]; intro x; exact t (V x)
lemma jointly (h:Registers P f U)(p:Registers P g V): Commute U V:= (times h p).single (mul_comm g f ▸ times p h)
lemma squareCost (h:Registers P f U) (x:H): ‖U x‖^2=∫ p, ‖f p‖^2∂𝔪 x:= dots_norm P (times h.adjoint h) x
lemma fare (h:Registers P f U) {q:ℝ}(p:0≤q)(b:∀ x,‖f x‖≤ q): ‖U‖≤q:= ContinuousLinearMap.opNorm_le_bound U p (dots_bill P (times h.adjoint h) p b)
lemma takes {x:H} {s:Set X} (hs:MeasurableSet s)(p:Registers P f U):
    (P.diagonal (U x)).real s = ∫ p in s, ‖f p‖^2∂𝔪 x := by
 rw [← restricted P hs x, P.same hs,  show P.region s (U x)= U (P.region s x) from ?_, p.squareCost]; exact DFunLike.congr_fun (p.comm hs).eq.symm x
-- multiplier action dominated theorem. For any v. Allow AE convergence & bound there
lemma tends (l:Filter ι) [l.IsCountablyGenerated](F:ι→X→ℂ)(A:ι→H.Op)(h:Registers P f U)(p:∀ i,Registers P (F i) (A i))(x:H) (q:ℝ)(v:∀ᶠ i in l,∀ᵐ y ∂(P.diagonal x), ‖F i y‖ ≤ q)(s:∀ᵐ y ∂(P.diagonal x),Tendsto (fun i=> F i y) l (𝓝 (f y))) : Tendsto (fun i=> A i x) l (𝓝 (U x)):= by
 obtain ⟨d,b,k⟩:=h.price.bound
 have he : Tendsto (fun i=> ‖A i x-U x‖^2) l (𝓝 0):= by
   have hx:= tendsto_integral_filter_of_dominated_convergence (μ:=𝔪 x) (l:=l) (F:=fun i t=> ‖(F i-f) t‖^2) (f:=fun x=>0) (fun _=> (q+d)^2) (Eventually.of_forall (fun i=> ((measurable_norm.comp ((p i).price.subs h.price).meas).pow_const _).aestronglyMeasurable)) (v.mono (fun i u=> u.mono (fun y uy=> (?_ : ‖‖(F i-f) y‖^2‖ ≤ (q+d)^2)))) (integrable_const _) (s.mono (fun y uy=> by simpa [Pi.sub_apply] using (uy.sub (tendsto_const_nhds (x:=f y))).norm.pow 2))
   · rw [integral_zero] at hx; simp_rw [← squareCost (sub (p _) h) x] at hx; exact hx
   rw [Real.norm_of_nonneg (by positivity)]
   exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le ..).trans (add_le_add uy (k y))) 2
 refine Metric.tendsto_nhds.mpr (fun ε v=>?_); apply (he.eventually (gt_mem_nhds (show (0:ℝ)<ε^2 from by positivity))).mono
 intro i u; rw [dist_eq_norm]; exact (sq_lt_sq₀ (norm_nonneg _) v.le).mp u
end Registers
variable (P)
open scoped Classical in
noncomputable def order (f : X→ℂ) : H.Op := if h:Tag f then (find P f h).choose else 0
lemma order_reads {f:X→ℂ}(h:Tag f) : Registers P f (order P f):= by unfold order; rw [dif_pos h]; exact (find P f h).choose_spec.1
lemma takes_order {f:X→ℂ} {U:H.Op}(p:Registers P f U): U=order P f:= p.single (order_reads _ p.price)
lemma order_tends (l:Filter ι)[l.IsCountablyGenerated] {f:X→ℂ}(g:ι→X→ℂ)(p:Tag f)(v:∀ i, Tag (g i))(t:∀ x,Tendsto (fun i=> g i x) l (𝓝 (f x))) (c:ℝ)(q:∀ᶠ i in l,∀ x,‖g i x‖≤ c)(x:H): Tendsto (fun i=> order P (g i) x) l (𝓝 (order P f x)):= Registers.tends l g _ (order_reads P p) (fun i=> order_reads P (v i)) x c (q.mono fun _ h=> Eventually.of_forall h) (Eventually.of_forall t)
end YM.Multiplier

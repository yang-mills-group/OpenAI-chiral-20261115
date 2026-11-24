import YM.SU5.FiniteGaugeData.Mist.Artery
/-! Sums on all physical axes of Willow -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Mist.Kodiak
open Function Filter Metric Finset Lattice Hills
open scoped Topology BigOperators InnerProductSpace
variable {M:Hilbert}(F:Axis→ Willow M ℝ)(B:List Axis)
def combT (x:E4)(w:List Axis):M.Op := (w.map fun j=>(F j).U (x j)).prod
local notation "F₁" i:max => combT F i
lemma comb_zero : combT F 0 B=1:= by unfold combT; induction B with
 | nil=>rfl
 | cons i v h'=>rw [List.map_cons,List.prod_cons,h']; rw [PiLp.zero_apply,(F i).init,one_mul]
variable (w:∀ i j:Axis,∀ x y:ℝ, Commute ((F i).U x) ((F j).U y))(hx:∀ i v,UniformContinuous fun x:ℝ=>(F i).U x v)
include w
lemma comb_comp (c d:E4): combT F (c+d) B= (F₁ c) B * (F₁ d) B:=by
 unfold combT; induction B with
 | nil=> simp
 | cons i v hh=> simp only [List.map_cons,List.prod_cons, PiLp.add_apply] at hh ⊢; rw [(F i).both,hh]; exact paid ((F i).U (c i)) ((F i).U (d i)) ((F₁ c) v) ((F₁ d) v) (glue i _ v)
where glue i t B: Commute ((F i).U t) ((F₁ c) B):= by induction B with
       | nil=> exact Commute.one_right _
       | cons z b hb=> exact (w i z t (c z)).mul_right hb
      paid(f g h k:M.Op)(p:Commute g h): (f*g)*(h*k)=(f*h)*(g*k):=by rw [mul_assoc,mul_assoc, ←mul_assoc g h, p.eq,mul_assoc]
omit w
lemma comb_price (x:E4)(v:M): ‖combT F x B v‖= ‖v‖ :=by induction B with
 | nil=> rfl
 | cons i s ih=> exact (((F i).keep (x i) ((F₁ x) s v))).trans ih
include hx
lemma comb_strong (v:M): Continuous (fun x=> (combT F x B) v):=by
 induction B with
 | nil=> exact continuous_const
 | cons i s ih=>
    refine mix_move (F i) (hx i) (fun x:E4=>x i) (by fun_prop) (fun x:E4=> (F₁ x) s v) ih -- args
where
 mix_move {M₁:Hilbert}(P: Willow M₁ ℝ)(p:∀ x:M₁.space,UniformContinuous fun t:ℝ=>P.U t x)(f:E4→ℝ)(h:Continuous f)(g:E4→ M₁)(u:Continuous g): Continuous (fun x=>P.U (f x) (g x)):=by
    refine continuous_iff_continuousAt.mpr fun i=> Metric.tendsto_nhds.mpr fun ε e=> ?_
    filter_upwards [Metric.tendsto_nhds.mp (((p (g i)).continuous.comp h).tendsto i) (ε/2) (by positivity),Metric.tendsto_nhds.mp (u.tendsto i) (ε/2) (by positivity)] with x q w
    refine lt_of_le_of_lt (dist_triangle _ (P.U (f x) (g i)) _) ?_; rw [P.keepD]; dsimp only [Function.comp_apply] at q; linarith only [q,w]
omit hx
lemma confluence (x:E4)(A:M.Op)(p:∀ i t, Commute ((F i).U t) A): Commute (combT F x B) A:=by induction B with | nil=> exact Commute.one_left _ | cons i y ih=> exact (p i (x i)).mul_left ih
lemma comb_one (x:ℝ)(a:Axis): combT F (x • basis a) Terrace.scheduleL=(F a).U x:=by fin_cases a <;> simp [combT,Terrace.scheduleL,basis, Willow.init, Ne.symm]
section
variable {L:Side}{a:Axis}{H:Hilbert}(P:Terrace H L a)(z:1<L.val)(p:a∈B)
lemma streamU (s:ℕ)(j:ℤ)(b:Axis)(g:b∈B)(t:b≠ a): mistU P B z (spinT L s j) b g=social (GroupR P B) (P.stepT s b j (fun i=> (t i).elim)):=by rw [show spinT L s j=((ticQ L s j):ℝ) from rfl,unitPaid,ramble_eq _ _ _ t,Driver_eq]
lemma stream_self (x:ℝ):mistU P B z x a p=1:=by
 apply ContinuousLinearMap.ext; intro v; refine congr_fun (vistas z (fun x=> mistU P B z x a p v) (fun _=>v) (unitC P B z p v).continuous continuous_const fun t=> ?_) x; rw [unitPaid,ramble_self,social_id]; rfl
end
end YM.CF.Buffered.Afterglow.Hierarchy.Mist.Kodiak

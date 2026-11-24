import YM.SU5.FiniteGaugeData.LocalLimit.Sequence.Ring
import Mathlib.Analysis.Complex.Basic

/-!
Uniform approximation port for convergence of the clipped receipts.
We ultimately want two sequential limits (iteration and all paths in a
property). Uniform approximation on the whole array, by arrays with the two
limits, is enough: neither space of tests nor duals needs sequential
compactness in its norm.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Sound
open Function Filter Metric Finset TopologicalSpace
open scoped Topology
section metric
variable {X:Type*}[PseudoMetricSpace X][CompleteSpace X]

private lemma converging {A:ℕ→ X} (p:∀ r:ℝ,0<r→∃ (B:ℕ→ X)(b:X), (∀ i:ℕ,dist (A i) (B i) ≤ r) ∧ Tendsto B atTop (𝓝 b)):∃ b:X,Tendsto A atTop (𝓝 b):=by
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.mpr ?_)
  intro r h
  obtain ⟨B,b,v,u⟩:=p (r/4) (by positivity)
  obtain ⟨s,H⟩:= Metric.cauchySeq_iff.mp (Filter.Tendsto.cauchySeq u) (r/4) (by positivity)
  exact ⟨s,fun i a j h=>by linarith [v i,v j,H i a j h,dist_triangle4_right (A i) (A j) (B i) (B j)]⟩

/-- Both limits along chosen i,k. -/
structure Couplet (i k:ℕ→ℕ)(A:ℕ→ℕ→X) (ℓ:ℕ→X)(z:X) (P:(ℕ→ℕ)→Prop):Prop where
  inner (n): Tendsto (fun t=> A n (k t)) atTop (𝓝 (ℓ n))
  periods : Tendsto (ℓ ∘ i) atTop (𝓝 z)
  paths (v:ℕ→ℕ) (h:P v): Tendsto (fun n=> A (i n) (k (v n))) atTop (𝓝 z)
lemma rising_cloud {i k:ℕ→ℕ} {P:(ℕ→ℕ)→ Prop}(A:ℕ→ℕ→X)
    (p:∀ r:ℝ,0<r→∃ (B:ℕ→ℕ→X)(L:ℕ→X)(z:X), (∀ i k, dist (A i k) (B i k) ≤ r) ∧ Couplet i k B L z P):
    ∃ (L:ℕ→X)(z:X), Couplet i k A L z P:=by
  have hi(n):∃ x:X,Tendsto (fun t=>A n (k t)) atTop (𝓝 x):= by apply converging; intro r h; obtain ⟨B,L,z,v,H⟩:= p r h; exact ⟨_,L n, (fun t=>v n (k t)),H.inner n⟩
  choose L hL using hi
  have he {B:ℕ→ℕ→X} {M:ℕ→X}{z:X}{r:ℝ}(v:∀ i k,dist (A i k) (B i k)≤ r)(H:Couplet i k B M z P)(n:ℕ):dist (L n) (M n) ≤ r:= le_of_tendsto ((hL n).dist (H.inner n)) (Eventually.of_forall (fun t=> v n (k t)))
  obtain ⟨x,hx⟩:=converging (A:=L ∘ i) (fun r h=> by obtain ⟨B,M,z,w,f⟩:= p r h; exact ⟨M∘i,z,(fun t=>he w f (i t)),f.periods⟩)
  refine ⟨L,x,⟨hL,hx,fun a h=> Metric.tendsto_nhds.mpr (fun r g=>?_)⟩⟩
  obtain ⟨B,M,z,V,Q⟩:=p (r/4) (by positivity)
  have hz: dist x z ≤ r/4:= le_of_tendsto (hx.dist Q.periods) (Eventually.of_forall fun t=> he V Q (i t))
  filter_upwards [Metric.tendsto_nhds.mp (Q.paths a h) (r/4) (by positivity)] with n t
  linarith [V (i n) (k (a n)),dist_triangle4_right (A (i n) (k (a n))) x (B (i n) (k (a n))) z]
end metric

section pick
variable {Y:Type}[Countable Y][Nonempty Y]
include Y
private lemma countstage : ∃ L:ℕ→Finset Y, (∀ k,(L k).Nonempty) ∧ ∀ y:Y,∀ᶠ k:ℕ in atTop,y ∈ L k := by
  classical
  letI := Encodable.ofCountable Y
  let f(n:ℕ):Y:= (Encodable.decode n).getD (Classical.arbitrary Y)
  have hf (x:Y): f (Encodable.encode x)=x:=by unfold f; simp
  refine ⟨fun n=> (Iic n).image f,fun n=> Finset.Nonempty.image ?_ _,fun y=>?_⟩
  · exact ⟨n,mem_Iic.mpr le_rfl⟩
  filter_upwards [eventually_ge_atTop (Encodable.encode y)] with k h
  exact mem_image.mpr ⟨Encodable.encode y,mem_Iic.mpr h,hf y⟩

/-- Countably many exams, all values live in period-independent compact disks.
Additionally pay arbitrary per-period cutoff gates at *all cone points* of
our returned array (usable for identifications as well as inequalities). We
can do this thanks to the `card` part: a selection of periods/cutoffs so the
cone excludes all cutoffs before the stage's UV-selected point and includes
that point and later ones. The convergence on paths then uses all such UV
indices; not just the value right at the stage index. -/
lemma recites (A:Y→ℕ→ℕ→ℂ) (v:∀ j,∃ D:ℝ, ∀ n k,‖A j n k‖ ≤ D) {cone pay :ℕ→ℕ→Prop}
    (e:∀ n,∀ᶠ k:ℕ in atTop,pay n k)
    (h:∀ n,∀ᶠ k:ℕ in atTop,cone n k)(q:∀ k,∀ᶠ n:ℕ in atTop,¬cone n k):
    ∃ i k:ℕ→ℕ, StrictMono i ∧ StrictMono k ∧
      (∀ a b, cone (i a) (k b)→ pay (i a) (k b)) ∧
      (∀ j,∃ (L:ℕ→ℂ)(z:ℂ),Couplet i k (A j) L z (fun f=> ∀ᶠ n in atTop, cone (i n) (k (f n)))) := by
  let fee(n:ℕ):=(1/2:ℝ)^n
  obtain ⟨U,u,y⟩:=countstage (Y:=Y)
  obtain ⟨i,k,L,H,hi,hk,f⟩:=YM.SU5.FiniteGaugeData.LocalLimit.Rings.two_steps A (fun _ _=>True) (fun n k _=>pay n k) cone U fee
    (fun j=>by
      obtain ⟨r,v⟩:=v j
      exact ⟨closedBall 0 r,isCompact_closedBall ..,fun n k=>mem_closedBall_zero_iff.mpr (v ..)⟩)
    (fun _=> Eventually.of_forall fun _=>trivial) (fun n _ _=> e n) h q
    (fun n=> pow_pos (by norm_num) _) id id strictMono_id strictMono_id
  refine ⟨i,k,hi,hk,?_,fun j=> ⟨L j,H j,⟨f.cut j,f.ir j,?_⟩⟩⟩
  · intro a b c; obtain ⟨j,t⟩:=u a; exact (f.line a b ((f.card a b).mp c) j t).1
  intro x hs
  refine Metric.tendsto_nhds.mpr fun r p=> ?_
  have he:Tendsto fee atTop (𝓝 0):=tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [y j,hs,he.eventually (gt_mem_nhds p)] with n t hn w
  exact (f.line n (x n) ((f.card n (x n)).mp hn) j t).2.trans_lt w
end pick
end YM.CF.Buffered.Afterglow.Sound

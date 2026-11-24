import Mathlib.Analysis.Normed.Group.Tannery
import Zephyr.Chern.Grad
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Topology Silk


/-! limits with a uniform moments envelope -/

variable {I : Type*}

lemma Fast.absolute {f} (hf : Fast f) : Fast fun x => (‖f x‖:ℂ) := by
  simpa only [Fast,Complex.norm_of_nonneg (norm_nonneg _)] using hf -- variant

def uCo (F : Ultrafilter I) (f : I → ℂ) := (F.map f).lim

lemma u_go {F : Ultrafilter I} {f : I → ℂ} (K : ℝ)
    (h : ∀ᶠ i in (F:Filter I), ‖f i‖ ≤ K) :
    Tendsto f F (𝓝 (uCo F f)) := by
  obtain ⟨x,-,e⟩:=(isCompact_closedBall (0:ℂ) K).ultrafilter_le_nhds' (F.map f)
    (show {i:I| f i∈Metric.closedBall 0 K}∈(F:Filter I) by simpa only
      [Metric.mem_closedBall,dist_zero_right] using! h)
  change (F.map f: Filter ℂ) ≤ 𝓝 (uCo F f)
  unfold uCo Ultrafilter.lim
  rwa [lim_eq e]

/-- Pointwise on coefficients, eventual absolute uniform envelope
with summable moments. -/
def Swift (F : Filter I) (f : I → Cover → ℂ) :=
  ∃ b, Fast b ∧ ∀ᶠ i in F, ∀ x, ‖f i x‖ ≤ ‖b x‖

structure Converges (F : Filter I) (f : I → Cover → ℂ) (z : Silk) : Prop where
  swift : Swift F f
  co (x) : Tendsto (fun i => f i x) F (𝓝 (z.co x))

abbrev Arrives (F : Filter I) (f : I → Silk) := Converges F (fun i => (f i).co)
abbrev Moves (F : Filter I) (f : I → Silk) := Swift F (fun i => (f i).co)

variable {L : Ultrafilter I}
lemma Swift.arrive {f} (h : Swift (L:Filter I) f) :
    ∃ y,Converges (L:Filter I) f y := by
  obtain ⟨b,hb,bds⟩:=h
  let y (x : Cover) := uCo L (fun i => f i x)
  have he x : Tendsto (fun i => f i x) L (𝓝 (y x)) := u_go ‖b x‖ (bds.mono fun _ e => e x)
  have ym x : ‖y x‖ ≤ ‖b x‖ := le_of_tendsto (he x).norm (bds.mono fun _ e => e x)
  exact ⟨⟨y, fun k => (hb k).of_nonneg_of_le (fun _=> mul_nonneg (penPos ..).le (norm_nonneg _))
    (fun _=> mul_le_mul_of_nonneg_left (ym _) (penPos ..).le)⟩, ⟨b,hb,bds⟩, he⟩

variable {F : Filter I} {f g : I → Silk} {v w : Silk}

lemma arrives_const (F : Filter I) (v : Silk) : Arrives F (fun _ => v) v where
  swift := ⟨_,v.fast,Eventually.of_forall (fun _ _=>le_rfl)⟩
  co _ := tendsto_const_nhds

lemma Swift.comp {J : Type*} {F' : Filter J} {r : I → Cover → ℂ}
    (h : Swift F r) {n : J → I} (hn : Tendsto n F' F) : Swift F' (fun j => r (n j)) :=
  let ⟨b,hb,p⟩:=h
  ⟨b,hb,hn.eventually p⟩

lemma Arrives.comp {J : Type*} {F' : Filter J} (h : Arrives F f v)
    {n : J → I} (hn : Tendsto n F' F) : Arrives F' (fun j => f (n j)) v where
  swift := h.swift.comp hn
  co x := (h.co x).comp hn

lemma Moves.add (p : Moves F f) (q : Moves F g) :
    Moves F (fun i => f i + g i) := by
  obtain ⟨a,ha,ea⟩:=p
  obtain ⟨b,hb,eb⟩:=q
  refine ⟨_,ha.absolute.add hb.absolute,?_⟩
  filter_upwards [ea,eb] with i pa pb x
  rw [co_add,Pi.add_apply,← Complex.ofReal_add,Complex.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact (norm_add_le ..).trans (add_le_add (pa x) (pb x))

lemma Arrives.add (p : Arrives F f v) (q : Arrives F g w) :
    Arrives F (fun i => f i + g i) (v+w) where
  swift := Moves.add p.swift q.swift
  co x := (p.co x).add (q.co x)

lemma Moves.neg (p : Moves F f) : Moves F (fun i => -f i) := by
  obtain ⟨a,ha,ea⟩:=p
  exact ⟨a,ha,ea.mono fun i hi x => (norm_neg (f i|>.co x)).le.trans (hi x)⟩

lemma Arrives.neg (p : Arrives F f v) :
    Arrives F (fun i => -f i) (-v) where
  swift := Moves.neg p.swift
  co x := (p.co x).neg

lemma Moves.mul (p : Moves F f) (q : Moves F g) :
    Moves F (fun i => f i * g i) := by
  obtain ⟨a,ha,ea⟩:=p
  obtain ⟨b,hb,eb⟩:=q
  refine ⟨_,ha.absolute.pile hb.absolute,?_⟩
  filter_upwards [ea,eb] with i pa pb x
  rw [co_mul,pile]
  simp_rw [←Complex.ofReal_mul,←Complex.ofReal_tsum,Complex.norm_of_nonneg (tsum_nonneg
    (g:=fun y => ‖a y‖*‖b (x-y)‖) (fun _=>by positivity))]
  have hg := ((f i).fast.splitAbs (g i).fast).prod_factor x
  refine (norm_tsum_le_tsum_norm hg).trans (hg.tsum_le_tsum ?_ ?_)
  · exact fun y => (norm_mul_le ..).trans (mul_le_mul (pa y) (pb _) (norm_nonneg _) (norm_nonneg _))
  simpa only [←norm_mul] using! (ha.splitAbs hb).prod_factor x

lemma Arrives.mul (p : Arrives F f v) (q : Arrives F g w) :
    Arrives F (fun i => f i * g i) (v*w) where
  swift := Moves.mul p.swift q.swift
  co x := by
    simp only [co_mul]
    obtain ⟨a,ha,ea⟩:=p.swift
    obtain ⟨b,hb,eb⟩:=q.swift
    apply tendsto_tsum_of_dominated_convergence ((ha.splitAbs hb).prod_factor x)
      (fun y => (p.co y).mul (q.co _))
    filter_upwards [ea,eb] with i pa pb y
    rw [norm_mul,norm_mul]
    exact mul_le_mul (pa _) (pb _) (norm_nonneg _) (norm_nonneg _)

lemma Arrives.D (p : Arrives F f v) (j : Axis) :
    Arrives F (fun i => D j (f i)) (D j v) where
  swift := by
    obtain ⟨a,ha,ea⟩:=p.swift
    refine ⟨_,ha.rune j,?_⟩
    filter_upwards [ea] with i pa x
    rw [co_D,norm_mul,norm_mul]
    exact mul_le_mul_of_nonneg_left (pa _) (norm_nonneg _)
  co x := tendsto_const_nhds.mul (p.co x)

lemma Converges.E {r} (p : Converges F r v) (t : Brill) :
    Tendsto (fun i => vista (r i) t) F (𝓝 (E t v)) := by
  obtain ⟨b,hb,eb⟩:=p.swift
  apply tendsto_tsum_of_dominated_convergence hb.abs
    (fun x => tendsto_const_nhds.mul (p.co x))
  filter_upwards [eb] with i hi x
  rw [norm_mul,badge,one_mul]
  exact hi x

theorem Arrives.E (p : Arrives F f v) (t : Brill) :
    Tendsto (fun i => E t (f i)) F (𝓝 (E t v)) := Converges.E p t

lemma Arrives.sum {κ : Type*} {f : κ → I → Silk} {g : κ → Silk}
    (s : Finset κ) (p : ∀ k, Arrives F (f k) (g k)) :
    Arrives F (fun i => ∑ k∈s,f k i) (∑ k∈s,g k) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact arrives_const ..
  | @insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]; exact (p a).add ih
lemma Arrives.prod {κ : Type*} {f : κ → I → Silk} {g : κ → Silk}
    (s : Finset κ) (p : ∀ k, Arrives F (f k) (g k)) :
    Arrives F (fun i => ∏ k∈s,f k i) (∏ k∈s,g k) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty]; exact arrives_const ..
  | @insert a s ha ih =>
    simp_rw [Finset.prod_insert ha]; exact (p a).mul ih

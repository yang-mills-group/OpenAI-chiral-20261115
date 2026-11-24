import YM.CF.Petal.Poll
import YM.CF.Sample.Mist
import Mathlib.Analysis.Convex.Integral
set_option linter.unusedSectionVars false

/-! Sampling into even sectors with exact locality. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Petal
open scoped BigOperators Topology
open Branch NormedSpace Function Finset MeasureTheory Phase Sample Filter
variable {Y I M D E G : Type*} [DecidableEq Y] [Fintype Y] [DecidableEq I] [MeasurableSpace M] [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [BorelSpace M] [Nonempty M] [NormedCommRing E] [NormOneClass E] [NormedAlgebra ℝ E] [CompleteSpace E] [TopologicalSpace D] [FirstCountableTopology D] [LocallyCompactSpace D]
variable {μ : Measure M} [IsProbabilityMeasure μ]
structure Cabin (μ : Measure M) [IsProbabilityMeasure μ] (L : Lodge Y E D G) where
  seat : D→ Plan Y μ
  unionV : G→(Y→M)→(Y→M)
  board g : MeasurableEmbedding (unionV g)
  plenty g : MeasurePreserving (unionV g) (fares Y μ) (fares Y μ)
  mass g d x : fall (seat (L.pick g d)) (unionV g x)=fall (seat d) x
  ct : Continuous (fun p : D×(Y→M)=> fall (seat p.1) p.2)
  reflL S d : L.zone S d d
variable {L : Lodge Y E D G}
def Crew (y : Cabin μ L) := D × (Y→ M)
-- don't use Crew (top)
abbrev Mood (Y D M : Type*) := D × (Y→M)
def barF (y : Cabin μ L) (d : Mood Y D M) := fall (y.seat d.1) d.2
def booth (y : Cabin μ L) := {v | barF y v≠0}
structure Manifest (y : Cabin μ L) (f : Mood Y D M→E) (w : ℝ) (X Q : Seal Y) : Prop where
  price : 0≤w
  pad : Q⊆X
  avail x (p:x∈booth y) : L.fare (f x)≤ w
  stock x (p:x∈booth y) : f x∈ L.store X
  ct : ContinuousOn f (booth y)
  records d : Bank (y.seat d) Q
  same {x z} : x∈booth y→ z∈booth y→ L.zone X x.1 z.1→ AgreeF Q x.2 z.2→ f x=f z
  weights {d t} : L.zone X d t→∀ i∈Q, (y.seat d).run i=(y.seat t).run i
  attire g (x) (p:x∈ booth y) : L.rule g (f x)=f (L.pick g x.1,y.unionV g x.2)
variable {V : Cabin μ L} {f g : Mood Y D M→E} {w c : ℝ} {X Y' Q R : Seal Y}
namespace Manifest
lemma convexB (K : Bell Y E) : ConvexOn ℝ Set.univ K.fare := by
  refine ⟨convex_univ, fun x _ y _ a b p v h=>?_⟩
  apply (K.plus ..).trans; rw [K.scale,K.scale,Real.norm_of_nonneg p,Real.norm_of_nonneg v]; exact le_rfl
lemma giftT (h : Manifest V f w X Q) : Gift (barF V) f w := by
  have he : IsOpen (booth V) := isOpen_ne_fun V.ct continuous_const
  exact soft (fun _=> sails_nonneg ..) (fun i g=>(L.normF _).trans (h.avail i g)) V.ct (fun x g=> ContinuousWithinAt.continuousAt (h.ct x g) (he.mem_nhds g))
lemma cashG (h : Manifest V f w X Q) (d : D) : Continuous (bet (V.seat d) fun x=>f (d,x)) := h.giftT.weighted.comp (f:=fun x=>(d,x)) (continuous_const.prodMk continuous_id)
def motor (V : Cabin μ L) (f : Mood Y D M→E) (d : D) := ∫ x, bet (V.seat d) (fun x=>f (d,x)) x ∂fares Y μ
lemma flush (h : Manifest V f w X Q) : Token L X (motor V f) w (fun _=>True) := by
  refine ⟨h.price,fun _=> trivial,fun d=>?_,fun g=> ?_,fun d=>?_, ?_, fun g v=>?_⟩
  · apply Convex.integral_mem (μ:=fares Y μ) (s:=(L.store X:Set E)) (f:=bet (V.seat d) (fun x=>f (d,x))) (L.store X).toSubmodule.convex (L.wallL X) _ (net_compact (h.cashG d)); apply Eventually.of_forall; intro x; by_cases g : fall (V.seat d) x=0
    · simp [bet,g]
    exact Subalgebra.smul_mem _ (h.stock (d,x) g) _
  · rename_i x y; exact banks_like (V.seat x) (V.seat y) _ _ (h.records x) (h.records y) (fun z=> prod_congr rfl (fun i k=> congr_fun (h.weights g i k) _)) (fun t v p u q=> h.same (x:=(x,t)) (z:=(y,v)) u q g p) (h.cashG x) (h.cashG y)
  · let P := V.seat d; let F := bet P (fun x=> f (d,x)); let m := fares Y μ
    have hC : Continuous (fall P) := V.ct.comp (f:=fun x=>(d,x)) (continuous_const.prodMk continuous_id)
    have he := (convexB L.toBell).map_integral_le L.sound.continuousOn isClosed_univ (μ:=fares Y μ) (by simp) (f:=F) (net_compact (h.cashG d)) (net_compact (L.sound.comp (h.cashG d)))
    apply he.trans
    have hk x : L.fare (F x) ≤ fall P x * w := by
      unfold F bet; rw [L.scale,Real.norm_of_nonneg (sails_nonneg ..)]; by_cases hv:fall P x=0
      · rw [hv,zero_mul,show sails P univ x=0 from hv,zero_mul]
      exact mul_le_mul_of_nonneg_left (h.avail (d,x) hv) (sails_nonneg ..)
    exact (integral_mono (net_compact (L.sound.comp (h.cashG d))) (net_compact (hC.mul continuous_const)) hk).trans_eq (by simp only [Pi.mul_apply]; rw [integral_mul_const, sails_all,one_mul])
  · exact net_cont _ _ h.giftT.weighted
  let t := V.seat v; let R : E→L[ℝ] E := ⟨(L.rule g).toLinearMap,L.ct g⟩
  unfold motor
  rw [← (V.plenty g).integral_comp (V.board g) (bet (V.seat (L.pick g v)) _)] -- may wrong integral
  -- tune
  change R (∫ x, bet t (fun x=>f (v,x)) x ∂fares Y μ)=_
  rw [←R.integral_comp_comm (net_compact (h.cashG v))]; apply integral_congr_ae; apply Eventually.of_forall; intro x
  simp only [bet, Function.comp_apply, map_smul]; rw [V.mass]; by_cases e:fall t x=0
  · rw [show fall _ x=0 from e]; simp [t,e] -- tune
  exact congrArg (fun z:E=>fall t x • z) (h.attire g (v,x) e)
lemma free : Manifest V (fun _=>1) 1 ∅ ∅ :=
  ⟨zero_le_one,Subset.refl _,fun _ _=>L.single.le,fun x _=>Subalgebra.one_mem _,continuousOn_const,fun d=>fun i h=>by simp at h,fun _ _ _ _=>rfl,fun _ _ e=>by simp at e,fun _ _ _=>map_one _⟩
lemma blend (h : Manifest V f w X Q) (k : Manifest V g c Y' R) : Manifest V (fun x=>f x*g x) (w*c) (X∪Y') (Q∪R) := by
  refine ⟨mul_nonneg h.price k.price,union_subset_union h.pad k.pad,fun x p=>(L.times ..).trans (mul_le_mul (h.avail x p) (k.avail x p) (Bell.starL _) h.price),fun x p=> Subalgebra.mul_mem _ (L.stair subset_union_left (h.stock x p)) (L.stair subset_union_right (k.stock x p)),h.ct.mul k.ct,fun d=>(h.records d).union (k.records d), fun p u v l=> congrArg₂ _ (h.same p u (L.grows subset_union_left v) (l.less subset_union_left)) (k.same p u (L.grows subset_union_right v) (l.less subset_union_right)), fun p i l=>?_,fun g v p=>by rw [map_mul,h.attire g v p,k.attire g v p]⟩
  rcases mem_union.mp l with g|g
  · exact h.weights (L.grows subset_union_left p) i g
  exact k.weights (L.grows subset_union_right p) i g
lemma localise (h : Manifest V f w X Q) (d : D) (x y : Y→M) (g : AgreeF Q x y) (p : fall (V.seat d) x≠0) (e : fall (V.seat d) y≠0) : f (d,x)=f (d,y) := h.same p e (V.reflL X d) g
lemma namepath (h : Manifest V f w X Q) (p : Manifest V g c Y' R) (k : Disjoint X Y') (d:D) : motor V (fun x=> f x*g x) d=motor V f d*motor V g d := independent (V.seat d) (fun x=>g (d,x)) (fun x=>f (d,x)) (h.records d) (p.records d) (h.localise d) (p.localise d) (Disjoint.mono h.pad p.pad k) (h.cashG d) (p.cashG d) ((h.blend p).cashG d)
end Manifest
end YM.CF.Petal

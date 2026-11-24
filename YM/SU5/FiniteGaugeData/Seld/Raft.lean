import YM.SU5.FiniteGaugeData.Seld.Fountain
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)(x y:H)(t:ℝ)(u:ℝ≥0)
local notation "rayA"=> Ioi (0:ℝ)
local notation "R"=> saucer S
open Spectral Boundary Probe
local notation "V"=> S.unit
local notation "U"=> M S
variable (A B: H.Op)(p:E4)(g h: Test4)(c:ℂ)
local notation "W" => Bench S
local notation "□" => W →ₗ[ℂ] W
variable (k:ℝ≥0) (m n:ℕ)
local notation "d"=> OS.Semigroup.duration
local notation "δ"=> d u
local notation "K"=> Cache S
local notation "F"=> parabola S
local notation "P"=> Par S
local notation "εd"=> OS.Semigroup.sideways
-- reversed sign plume.W hol (not bounded or cont to edge** until b**)
local notation "M₀"=> F (m+n)
abbrev backwards (z:ℂ):= inner ℂ x ((P m 2) (A ( (F (m+n) z) (B (F n (2-z) y)))))
abbrev forwards (z:ℂ):= inner ℂ x ((F n (2-z)) (B ( (F (m+n) z) (A (P m 2 y)))))
variable (z:ℂ)(h':z.re > 0 ∧ z.re < 2)
private lemma join_two(h':z.re<2) : 2-z∈inside:=by change 0<(2-z).re; rw [sub_re]; exact sub_pos.mpr h'
lemma rafts (h':z.re>0 ∧ z.re<2) : AnalyticAt ℂ (backwards S x y A B m n) z ∧ AnalyticAt ℂ (forwards S x y A B m n) z:=by
 let f:= (P m 2); let L:=(innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ H.space y)); let b(z:ℂ):= F n (2-z); let ζ(z:ℂ):= F (m+n) z
 have hb:AnalyticAt ℂ b z:= (Bokeh S n _ (join_two z h'.2)).comp (analyticAt_const.sub analyticAt_id); have hc:= Bokeh S (m+n) z (show z∈inside from h'.1)
 change AnalyticAt ℂ (L ∘ fun z=> (f*A*ζ z*B*b z)) z∧AnalyticAt ℂ (L ∘ fun z=> b z* B*ζ z*A*f) z; exact ⟨L.analyticAt _ |>.comp (((analyticAt_const.mul hc).mul analyticAt_const).mul hb), L.analyticAt _ |>.comp ((((hb.mul analyticAt_const).mul hc).mul analyticAt_const).mul analyticAt_const)⟩
-- shifted.B used all axis Eu relative t extension
variable (k0:0<u)(v:u<2)
lemma wplus (v:u<2): OS.Semigroup.duration (2-u) = 2-δ:=by unfold OS.Semigroup.duration; rw [NNReal.coe_sub v.le]; push_cast; rfl
lemma terrace0 (v:u<2) (t:ℝ): (2-(δ+sideways t))=d (2-u)+sideways (-t):=by rw [wplus u v]; unfold sideways; push_cast; ring
include k0 v
lemma rpair(t:ℝ) : backwards S x y A B m n (δ+sideways t)= inner ℂ x ((P m 2*A*P (m+n) u * (S.edge t*B*S.edge (-t))*P n (2-u)) y):=by
 unfold backwards; rw [terrace0 u v, ← FRight S t (m+n) _ (dur.mpr k0), ← FsAct S (-t) n _ (dur.mpr (tsub_pos_of_lt v))]; rfl
lemma vpair(t:ℝ) : forwards S x y A B m n (δ+sideways (-t))= inner ℂ x (((P n (2-u) * (S.edge t*B*S.edge (-t))) *( P (m+n) u * A* P m 2)) y):=by
 unfold forwards; rw [terrace0 u v,neg_neg,← FRight S t n _ (dur.mpr (tsub_pos_of_lt v)), ← FsAct S (-t) (m+n) _ (dur.mpr k0)]; rfl
omit k0 v
-- literal orientation.T. fill teaser
abbrev coreSp (p:E4)(A:H.Op):=optx S A (SEP a p).val
lemma shrike (p0:p a=0): coreSp S p A=optx S A p:=by unfold coreSp; change optx S A (p-p a • basis a)=_; rw [p0,zero_smul,sub_zero]
lemma regain : S.edge (p a) * (coreSp S p A)* S.edge (-(p a))=optx S A p:=by
 rw [← timeslot S (p a),← timeslot S (-(p a)), neg_smul]; change optx S (optx S A (SEP a p).val) (p a • basis a)= _; rw [opt_act, show p a • basis a+(SEP a p).val=p from by change p a • basis a+(p-_)=p; abel]
#print axioms rafts
end YM.CF.Buffered.Afterglow.Hierarchy.Seld

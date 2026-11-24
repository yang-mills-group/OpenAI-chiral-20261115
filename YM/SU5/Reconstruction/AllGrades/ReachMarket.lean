import YM.SU5.Reconstruction.AllGrades.GChess
import YM.SU5.Reconstruction.Quanta.Garret
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
open Reed (Fine think)
open Fock Pastry Tenant
namespace Garret
/-! Chess tables purchased on REAL Warm & root, leaves costs of sharp alone. As in Tower/Distance. -/
local notation "K₀"=>tent Y H
variable (n m:ℕ)
local notation "u₀"=> momentm Y n s
local notation "N"=> (tent Y H).c (momentm Y n s)
lemma choral_hot (q:Ferry Y s n m) (a:Axis)(z:ℤ)(F:Mark ((tent Y H).c (momentm Y n s))) (h:AtSupport true (band ((tent Y H).c (momentm Y n s)) a (Heat.gaugeShift Λ.block z) (reserve Λ l)) F):
 0 ≤ Complex.I * (collector Y H n m q.depth s) (reflMark a (Heat.gaugeShift Λ.block z) F*F):=by
 -- instantiate at table; authorization of collector need not visit unlimited shelf.
 let G:Family (tent Y H):= Pi.single u₀ F
 have he:G u₀=F:= Pi.single_eq_same ..
 have h':=NorthTapes.hot_positive Y H s a z n m q (f:=G) (he.symm ▸ h)
 let v:= boxprice Y H n m q.depth s q.fire q.enters
 unfold hot at h'; rw [dif_pos q.depth] at h'
 change 0 ≤ (collector Y H n m q.depth s) (Complex.I • (reflMark a (Heat.gaugeShift Λ.block z) (G u₀)* G u₀)) at h'
 rwa [he, v.mult] at h'
local notation "C₀" d:max=>Grip Y H s d
-- native lease rates for both. warmth sufficient (UV) controls I. sharpened consumer can use on moving pairs too.
local notation "Φ" i:max k:max F:max=>hot Y H s i k F
lemma hotChess(d:ℕ):∀ᶠ i in atTop,∀ (k:ℕ), Ferry Y s i k→
 ∀ {S T:Finset Cover}{f g:Family (tent Y H)},InTest (tent Y H) true S true f→ InTest (tent Y H) true T true g→ CompactArc S d→ CompactArc T d→∀ a b:ℝ,pay f a→pay g b→ ‖Φ i k (f*g)‖≤ C₀ d*(a*b) := by
 filter_upwards [(momentum Y s).eventually ((c_grows (K₀)).eventually_ge_atTop (widthPair K₀ d+addgap K₀))] with i h k q S T f g a b c t A₁ B t₀ w
 unfold hot; rw [dif_pos q.depth]; exact pair_for_odd (boxprice Y H i k q.depth s q.fire q.enters) (fun j s' F h=>choral_hot Y H s i k q j s' F h) d h (a.support _) (b.support _) (torus_arc S K₀ _ c) (torus_arc T K₀ _ t) A₁ B (t₀ _) (w _)

include V
lemma root_budget_odd (d:ℕ){S T:Finset Cover}{f g:Family (tent Y H)} (p:InTest K true S true f)(t:InTest K true T true g)(a:CompactArc S d)(b:CompactArc T d)(v w:ℝ)(h:pay f v)(z:pay g w):‖E s (f*g)‖≤ C₀ d*(v*w):=by
 let D:=warm_limit Y H V s (aux_test (show InTest _ _ (S∪T) false (f*g) from InTest.mul (p.mono subset_union_left) (t.mono subset_union_right))); let q:= hotChess Y H s d
 apply le_of_tendsto D.periods.norm
 filter_upwards [V.pick.grow_i.tendsto_atTop.eventually q] with i₀ h₀
 apply le_of_tendsto (D.inner _).norm
 exact (V.pick.pass Y H s _).mono fun _ hz=>h₀ _ hz p t a b v w h z

lemma root_budget(b': Bool)(d:ℕ){S T:Finset Cover}{f g:Family (tent Y H)} (p:InTest K true S b' f)(t:InTest K true T b' g)(a:CompactArc S d)(b:CompactArc T d)(v w:ℝ)(h:pay f v)(z:pay g w):‖E s (f*g)‖≤ C₀ d*(v*w):=by
 cases b'
 · exact pair_budget Y H V s d p t a b v w h z
 exact root_budget_odd Y H V s d p t a b v w h z

end Garret
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.root_budget

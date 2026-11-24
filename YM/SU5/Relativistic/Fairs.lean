import YM.SU5.FiniteGaugeData.Tower.Distance
import YM.SU5.Relativistic.FairPair
import YM.SU5.Relativistic.OddLimit
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
local notation "K₀"=>tent Y H
local notation "A"=> Journey.duetCharge Y s
local notation "C₀" d:max=>Grip Y H s d
-- native lease rates for both. warmth sufficient (UV) controls I. sharpened consumer can use on moving pairs too.
local notation "Φ" i:max k:max F:max=>hot Y H s i k F
lemma shot_tandem(d:ℕ):∀ᶠ i in atTop,∀ (k:ℕ), Ferry Y s i k→
 ∀ {S T:Finset Cover}{f g:Family (tent Y H)},InTest (tent Y H) true S true f→ InTest (tent Y H) true T true g→ CompactArc S d→ CompactArc T d→∀ a b:ℝ,pay f a→pay g b→ ‖Φ i k (f*g)‖≤ C₀ d*(a*b) := by
 filter_upwards [(momentum Y s).eventually ((c_grows (K₀)).eventually_ge_atTop (widthPair K₀ d+addgap K₀))] with i h k q S T f g a b c t A₁ B t₀ w
 unfold hot; rw [dif_pos q.depth]; apply CapEight.all_pair (boxprice Y H i k q.depth s q.fire q.enters) d h ?_ (a.support _) (b.support _) (torus_arc S K₀ _ c) (torus_arc T K₀ _ t) A₁ B (t₀ _) (w _)
 intro j z F g
 let N:= momentm Y i s
 let G: Family (tent Y H):= Function.update (0:Family (tent Y H)) N F
 have hp:G N=F:=by simp [G]
 have ht:=gradedLaw Y H s i k (p:=q) j z (F:=G) (hp.symm ▸ g); unfold hot at ht; rw [dif_pos q.depth] at ht
 -- simplify hp coerces
 unfold mirror at ht; change 0 ≤ _ at ht
 -- want fun input
 convert ht using 2; try { simp [G,N] }


include V
lemma shot_pair (d:ℕ){S T:Finset Cover}{f g:Family (tent Y H)} (p:InTest K true S true f)(t:InTest K true T true g)(a:CompactArc S d)(b:CompactArc T d)(v w:ℝ)(h:pay f v)(z:pay g w):‖E s (f*g)‖≤ C₀ d*(v*w):=by
 let D:=warm_limit Y H V s (aux_test ((p.mono (subset_union_left (s₂:=T))).mul (t.mono subset_union_right))); let q:= shot_tandem Y H s d
 apply le_of_tendsto D.periods.norm
 filter_upwards [V.pick.grow_i.tendsto_atTop.eventually q] with i₀ h₀
 apply le_of_tendsto (D.inner _).norm
 exact (V.pick.pass Y H s _).mono fun _ hz=>h₀ _ hz p t a b v w h z
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab

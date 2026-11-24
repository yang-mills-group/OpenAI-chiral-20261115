import YM.SU5.Reconstruction.Sleet.Shawl
/-! Growth in the cone. Push through the wings for Paley. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm.Snowball
open Function Set Filter MeasureTheory Measure Complex Metric YM.Paley
open scoped Topology NNReal ENNReal Real ComplexConjugate
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable (μ : Measure X) [IsFiniteMeasure μ] (H P:X→ℝ)(x:Continuous H)(y:Continuous P)(p:∀ i,0≤ H i)
section size
private lemma poles {d b σ:ℝ}(e:0≤d)(δ:0<b)(p:0<σ) (s:σ<1): ∀ᶠ r:ℝ in atTop, b < r-d ∧ 0 ≤ σ*r ∧ b^2+(σ*r)^2<(r-d)^2:=by
 have h:0<1-σ:=by linarith
 filter_upwards [eventually_gt_atTop ((b+d)/(1-σ))] with r hr
 have hw:0<r:=lt_trans (by positivity) hr
 have hm:b+σ*r<r-d:=by linarith [(div_lt_iff₀ h).mp hr]
 have ht:0<σ*r:=by positivity
 exact ⟨by linarith,ht.le,by nlinarith⟩
end size
private lemma herm (r t:ℝ):metre μ H P r (-t)= conj (metre μ H P r t):=by unfold metre; rw [← integral_conj]; refine integral_congr_ae (ae_of_all _ fun i=>?_); simp only; rw [map_mul,conj_ofReal,← exp_conj]; congr 2; simp
structure Crystalline (μ:Measure X) (H P:X→ℝ) (d b Q C:ℝ) : Prop where
   positive : 0<b
   pad: 0≤d
   weather : ∃ᶠ r:ℝ in atTop, Weatherproof Q (r-d) (metre μ H P r) ∧ InPocket C b (metre μ H P r)
variable {d b Q C:ℝ} (w:Crystalline μ H P d b Q C)
include w
lemma Crystalline.pending: Snoops μ H P:= by
 intro σ ⟨δ,s⟩; refine ⟨max Q C, ((w.weather).and_eventually (poles w.pad w.positive δ s)).mono fun r ⟨⟨f,g⟩,e,v,t⟩=>?_⟩
 exact affords w.positive e v t f g (g.mirror (herm μ H P r)) le_rfl
lemma Crystalline.mirror: Crystalline μ H (-P) d b Q C:= by
 refine ⟨w.positive,w.pad, w.weather.mono fun r ⟨t,e⟩=> ?_⟩
 have he: metre μ H (-P) r = fun x=>metre μ H P r (-x):=funext (reversed μ H P r)
 rw [he]; exact ⟨Weatherproof.back t,e.mirror (herm μ H P r)⟩
include p x y
lemma Crystalline.forces (z:X)(u:z∈ μ.support): |P z| ≤ H z:= by
 apply abs_le.mpr; have ht:= trailblazer μ H P x y p (w.pending μ H P) z u; have hX: -(-P z) ≤ H z:= trailblazer μ H (-P) x y.neg p ((w.mirror μ H P).pending μ H (-P)) z u
 constructor <;> linarith
end YM.ConePrice.Storm.Snowball

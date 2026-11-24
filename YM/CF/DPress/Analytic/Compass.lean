import YM.CF.DPress.Analytic.Stead
import YM.CF.Jet.Sam
/- Disc property stable under $real jet. Only near qualitative re-centered allowances rather than all $sphere continuity.Lempel. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.DPress.Analytic
open Function Set Filter Metric MeasureTheory Complex
open scoped Topology Classical ContDiff InnerProductSpace
variable {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
local notation "J"=> Jet.Allows
variable (p:ℕ)(L:ℝ)(f:ℂ→ V→ℂ)
lemma planeZero {L:ℝ}(p:1<L) : (0:ℂ)∈ank L:=mem_ball_self (by linarith)
lemma planeOne {L:ℝ}(p:1<L) : (1:ℂ)∈ank L:= by simpa only [ank,mem_ball_zero_iff,norm_one]
open Planned.AtomRegular
private abbrev gearbox(c:ℂ):ℂ →L[ℝ] ℂ:= (ContinuousLinearMap.lsmul ℝ ℂ c) -- tune use mul.LC.
lemma gear (c:ℂ): ‖gearbox c‖ ≤ ‖c‖:= ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun i=> norm_mul c i|>.le
abbrev tend (L:ℝ)(f:ℂ→V→ℂ)(p:ℕ):Prop:= ∃ C:ℝ,∀ᶠ x in 𝓝 (0:V),∀ v∈ank L,Jet.Allows p (f v) x C
variable (e:tend L f p)(q:∀ᶠ x in 𝓝 (0:V), DifferentiableOn ℂ (fun z=>f z x) (ank L))(R:ℝ)(t:1<R)(v:R<L)
include t v e q
lemma underClock : ∃ (S:Set V)(C:ℝ), (∀ x∈S, ∀ v∈ank L, ∃ c:ℝ,Jet.Allows p (f v) x c)∧ IsOpen S∧ (0:V)∈S∧ Under ωμ (fun θ z=>gearbox (tor R θ) (f (φ R θ) z)) p S (fun _=> C) :=by
 obtain ⟨C,g⟩:=e; obtain ⟨S,vS,x,y⟩:=_root_.mem_nhds_iff.mp (g.and q); let K:= (R-1)⁻¹*C; let f(x) := f x; have ht(a:ℝ):φ R a∈ank L:= β _ _ v (by linarith) _
 let W(x:ℝ)(y:V):=gearbox (tor R x) (f (φ R x) y); have hp(u:V)(c:u∈S):= fun i:ℝ=>(Jet.Allows.linear (gearbox (tor R i)) ((vS c).1 _ (ht i)) ((gear _).trans (mft R t i))); refine ⟨S,K,fun i t z u=> ⟨C,(vS t).1 z u⟩,x,y, Jet.under x (fun t y q=>(hp _ q t).smooth) (fun i z=>?_) (integrable_const _) (fun x y p=>hp _ p _)⟩; have he : ContinuousOn (fun z=> f z i) (ank L):=(vS z).2.continuousOn; exact ((tor_C R t).mul (continuousOn_univ.mp (he.comp ((φ_C ..).continuousOn) (fun i _=> ht i)))).stronglyMeasurable -- tune
variable (j:ℕ) (h:j≤p)(u: Fin j→ V)
include h
lemma diffD : let A:=fun z=>f z; let a(θ:ℝ):=tor R θ*iteratedFDeriv ℝ j (f (φ R θ)) 0 u; let M:=iteratedFDeriv ℝ j (f 1-f 0) 0 u; Integrable a ωμ ∧ ∫ θ,a θ ∂ωμ=M:=by
 intro A a M; let W(x:ℝ)(y:V):=gearbox (tor R x) (f (φ R x) y); obtain ⟨S,C,hS,g',z,p'⟩:= underClock p L f e q R t v; let Z:= ContinuousMultilinearMap.apply ℝ _ ℂ u; let κ(θ:ℝ):= iteratedFDeriv ℝ j (W θ) 0; have hh: Integrable κ ωμ:= p'.integrate z h
 have he(θ:ℝ) : Z (κ θ)= a θ:=by
    let L':= gearbox (tor R θ); let k:= f (φ R θ); change iteratedFDeriv ℝ j (L' ∘ k) 0 u= _; rw [L'.iteratedFDeriv_comp_left (hS _ z _ (β R L v (by linarith) _)).choose_spec.smooth ?_]; · rfl
    exact_mod_cast h
 refine ⟨funext he ▸ (Z.integrable_comp ‹Integrable _ _›),?_⟩ -- bound cast
 simp_rw [← he]; rw [ContinuousLinearMap.integral_comp_comm Z hh]; let H:= Planned.AtomRegular.average ωμ W; rw [←show iteratedFDeriv ℝ j H 0= ∫ θ,κ θ ∂ωμ from (p'.less h).differentiate g' z]; have hx:H=ᶠ[𝓝 (0:V)] f 1-f 0:=q.mono fun i p=> (Disc.ofDiff p).read R t v; rw [(hx.iteratedFDeriv (𝕜:=ℝ) j).eq_of_nhds]; rfl -- tune
omit t v
lemma diffClock (_g:1<L) : Disc L (fun θ=> iteratedFDeriv ℝ j (f θ) 0 u) (iteratedFDeriv ℝ j (f 1-f 0) 0 u):=⟨ fun R t v=> (diffD p L f e q R t v j h u).1, fun R t v=>(diffD p L f e q R t v j h u).2⟩ -- tune
end YM.CF.DPress.Analytic

import YM.CF.BPress.Mount.Extends
/-! within angular Marks eval. Actor portrait cost without needs on tags, pointwise on all argument species. In N gauge `p` labels must co-transform as in `Extends` stance.` -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Mount
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf Primary
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale Fare Machine Shot Till Store Skye Girt Scree Voice Noon Phase Extensor Stamps Grid Hazel Net -- ambiguity.
variable {s m B N:Side} {D:BandWidth}(X:Bands (More N) D)
variable {T:Sheet.Atlas}{c d L y:ℝ}{a:ℕ}(F: Net (More N) T L y c d a) (A:Tiling (More N)) (i:X.Index)
-- derivatives in actual spine ($prime of v)$ from printed continuous cert. works without proof Born.
lemma primeC_plot (f:ℝ→ Paint s)(h:∀ i, ContDiff ℝ ∞ (fun t=> f t i)): Plot (primeC f):=fun i=> (continuous_apply i).comp (dconC _ h)
variable (p : Micro (More N) × Duo (More N))
abbrev spline := Stamps.brush F p.1 p.2 A X i
lemma rootPrice (t:Site (More N)): ContDiff ℝ ∞ (fun v=> spline X F A i p v t):= (Stamps.paid ..).smooth t -- tune args
lemma plan0: Plot (spline X F A i p):=fun t=> (rootPrice X F A i p t).continuous
lemma plan1: Plot (primeC (spline X F A i p)):= primeC_plot _ (fun i'=>rootPrice ..)
def readingX: Plain N:=portrait _ _ (plan0 X F A i p) (plan1 X F A i p) (Stamps.plant F p.1 p.2 A X i) p.1 ∅
lemma deriv_φ {D E:Type}[MeasurableSpace D][NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] (f:D→ℝ→ E) (p:∀ v, Measurable fun i=> f i v)(v:ℝ)(h:∀ i,DifferentiableAt ℝ (f i) v) : Measurable fun i=> deriv (f i) v:=by
 let k(n:ℕ):= 1/(n+1:ℝ); let Q(n:ℕ)(i:D):=(k n)⁻¹ • (f i (v+k n)- f i v); refine measurable_of_tendsto_metrizable (f:=Q) (fun i=> ((p (v+k i)).sub (p v)).const_smul _) (tendsto_pi_nhds.mpr ?_); intro i; have ht(n:ℕ):0<k n:=by unfold k; positivity
 exact (h i).hasDerivAt.tendsto_slope_zero.comp (show Tendsto k atTop (𝓝[≠] 0) from tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall (fun i=> (ht i).ne')⟩)
lemma reading_m : Measurable (readingX X F A i):=by
 have h(i':Site (More N))(v:ℝ):Measurable (fun p=> spline X F A i p v i'):= (measurable_pi_apply _).comp (Stamps.brush_m F A X i v); exact portrait_meas (plan0 X F A i) (plan1 X F A i) measurable_fst (Stamps.plant_m ..) (S:=fun _=>∅) (a:=fun x=>by simp) h (fun x t => deriv_φ (fun p v=> spline X F A i p v x) (h x) t (fun i'=> (rootPrice X F A i i' x).differentiable (by norm_num) t))
lemma reading_gauge (v:Mach (More N))(h:i∈X.nc): let q:=(Lattice.gauge v p.1, p.2*((X.mark i).framesE v)⁻¹); Along (X.band i) (readingX X F A i q) (τ (readingX X F A i p) v):=by
 intro q; let S:=readingX X F A i p; let W:= spline X F A i p; let K:=spline X F A i q; obtain ⟨e,k⟩:= Stamps.follows F p.1 p.2 A X i v h; refine ⟨fun _ _ _=>rfl,fun i' u=>e u, fun _ _=> rfl,fun j t a=>?_⟩; cases a <;> apply ContinuousMap.ext <;> intro z
 · exact k z.val t
 exact Hazel.Zone.d_swive K W (v j) z.val j (fun i=> k _ t) ((rootPrice X F A i p j).differentiable (by norm_num) _)
lemma reading_local (p' : Micro (More N) × Duo (More N))(h:p'.2=p.2)(u:Agrees (X.band i) p.1 p'.1) : Along (X.band i) (readingX X F A i p) (readingX X F A i p'):=by
 have hx:= Stamps.roots F p.1 p.2 A X i p'.1 u; have he: Plain.X (readingX X F A i p)=Plain.X (readingX X F A i p'):=by change Stamps.plant F p.1 p.2 A X i = Stamps.plant F p'.1 p'.2 A X i; rw [h]; exact hx.1
 have hp: spline X F A i p=spline X F A i p':=by unfold spline; rw [h]; exact hx.2
 refine ⟨u,fun i t=>congrFun he i,fun _ _=>rfl,fun j b v=>?_⟩; cases v <;> apply ContinuousMap.ext <;> intro a
 · exact congrFun (congrFun hp a.val) j
 exact congrArg (fun H:ℝ→ Paint (More N)=> primeC H a.val j) hp -- tune
end YM.CF.BPress.Mount

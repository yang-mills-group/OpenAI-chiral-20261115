import YM.CF.BPress.Primary.Maize
/-! independent copies of local terms (analysis of invariant Mark). `Workers` generic averaging; measure on all sites of the SAME micro lattice. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Primary
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale
variable {s N:Side}{U:Driver N}{A B C:Pledge}
abbrev machines (s:Side):Measure (Mach s):= Law.chain group.probHaar _
variable {D:Type*}[MeasurableSpace D]
structure Worker (M:Mach s→D→D):Prop where
 seq :∀ p g x,M p (M g x)=M (p*g) x
 meas: Measurable (fun p:D × Mach s=>M p.2 p.1)
abbrev average (M:Mach s→D→D)(f:D→ℂ)(x:D):=∫ p,f (M p x)∂machines s
namespace Worker
variable {M:Mach s→ D→D}(S:Worker M)(f:D→ℂ) {c:ℝ}(p:Measurable f)(t:∀ x,‖f x‖≤c)
include S t p
lemma integ (x:D): Integrable (fun i=>f (M i x)) (machines s):= Integrable.of_bound (((f: D→ℂ) |> (fun _=>p)).comp (S.meas.comp (measurable_const.prodMk (measurable_id' (α:=Mach s)))) |>.aestronglyMeasurable) c (Eventually.of_forall fun x=>t _) -- tune
lemma meas_A : Measurable (average M f):=(Law.marginalP (f:=fun x:D × Mach s=>f (M x.2 x.1)) ⟨p.comp S.meas,c,fun x=>t _⟩ (machines s)).meas
lemma price_A (x:D):‖average M f x‖≤c:=(norm_integral_le_of_norm_le_const (μ:=machines s) (ae_of_all _ fun p=>t (M p x))).trans_eq (by simp)
lemma move_avg (g:Mach s)(x:D): average M f (M g x)=average M f x:=by
 unfold average; simp_rw [S.seq]; exact (Law.restore (machines s) (machines s) (fun p=>p*g) (measurePreserving_pi _ _ (f:=fun i (p:E)=>p*g i) (fun i=>measurePreserving_mul_right _ _)) _ (S.integ f p t x)).symm -- tune
lemma priceΔ (x y:D)(h:ℝ)(v:∀ u, ‖f (M u x)-f (M u y)‖ ≤ h): ‖average M f x - average M f y‖ ≤ h:=by unfold average; rw [←integral_sub (S.integ f p t x) (S.integ f p t y)]; exact (norm_integral_le_of_norm_le_const (μ:=machines s) (ae_of_all _ v)).trans_eq (by simp)
omit t p
lemma align (x y:D)(v:∀ g,f (M g x)=f (M g y)): average M f x=average M f y:=by unfold average; simp_rw [v]
variable {I:Type*}(V:I→D→ℂ){C:I→ℝ}(v:∀ i,Measurable (V i))(g:∀ i x,‖V i x‖≤ C i)
include v g
lemma total_avg (t:Finset I)(x:D): ∑ i∈t,average M (V i) x=∫ p:Mach s,∑ i∈t,V i (M p x)∂machines s:=(integral_finsetSum _ (fun i _=> S.integ (V i) (v i) (g i) x)).symm -- parentheses ∑ scope?
lemma subtotal_r (t:Finset I)(x:D): ∑ i∈ t,(average M (V i) x).re=∫ p:Mach s,(∑ i∈t,(V i (M p x)).re)∂machines s:=by
 rw [←Complex.re_sum,total_avg S V v g]; simp_rw [←Complex.re_sum]; exact Eq.symm (integral_re (show Integrable (fun p=> ∑ i∈t,V i (M p x)) (machines s) from integrable_finsetSum _ (fun i _=> S.integ (V i) (v i) (g i) x))) -- tune name
 -- tune
end Worker
namespace Machine
variable (W:Wish U A B C)
def spinM (g: Mach (More N))(x:U.Pose) := moveW x W g
private lemma meas_mov {D:Type}[TopologicalSpace D][MeasurableSpace D][BorelSpace D] (f : Mach (More N) × D → D)(p:Continuous f): Measurable fun x:D× Mach (More N)=> f x.swap:=by haveI:SecondCountableTopologyEither (Mach (More N)) D := ⟨Or.inl inferInstance⟩; exact p.measurable.comp measurable_swap
lemma μ_worker : Worker (Machine.spinM W):=by
 refine ⟨fun p g x=> pose_seq x W g p,?_⟩; let f(x:Mach (More N) × U.Pose) := Machine.spinM W x.1 x.2; haveI : BorelSpace U.Pose:=by letI : BorelSpace (Plain N):=bore_p; infer_instance
 exact meas_mov f (Driver.feeling W)
end Machine
end YM.CF.BPress.Primary

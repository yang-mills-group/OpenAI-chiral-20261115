import YM.CF.Slate.Bulb
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Slate
open Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=> SU.group
variable {K:Teller SU.group}{U:Config SU.group f}{V:Config SU.group c}
section symbols
variable(T:Tube G S)(R:ℕ)(k:S.Choices)
lemma dc_k (p:PathData SU.group)(u:Clip) (R d:ℕ)(i:Twin f)(t:ℝ)(W:Config SU.group f): taken ∅ p u R d t W i=plotted p u R d W i:=by unfold taken; split; simp [pers]; simp
lemma manta (p:PathData SU.group)(u:Clip)(V:Config SU.group f)(t:ℝ)(i:Cell f)(d R:ℕ): king ∅ p u R d t V i = u.direct*sore SU.group (faceValue V i)+(∑ j:Bool, ‖plotted p u R d V (i,j)‖^2/2):=by
 unfold king; rw [dc_k,Fintype.sum_bool]; unfold hallP sore plotted shoot; simp only [notMem_empty,↓reduceIte,Bool.false_eq_true, norm_smul, Real.norm_eq_abs, mul_pow,sq_abs,Real.sq_sqrt u.quadratic_pos.le]; ring -- tune
lemma hiatus(x:ℝ)(i:Cell f) : kF T R (fiery G x S.patch.L) (temp x) ∅ ∅ V U i= KissP U T i+ ∑ j:Bool,‖RiftF R U V T (i,j)‖^2/2:=by
 have he:wV T R (temp x) ∅ V=T.Xn R V:=funext fun i=>dc_k ..; unfold kF zF KissP; rw [he,manta]; change _*(sore ..)+(∑ j:Bool,‖T.Xf R U (i,j)‖^2/2)+_= _; rw [add_assoc, ← sum_add_distrib]; congr 1; refine sum_congr rfl fun j _=>?_ ; unfold RiftF; rw [norm_sub_sq_real, real_inner_comm]; ring -- tune
lemma iham(i:Bond c)(u:ℝ) : kI T R u ∅ V (wit V (S.prediction U k)) i= KissI U V k i+‖RiftI R U V T k i‖^2/2:=by
 let Z := S.prediction U k; have he:wV T R u ∅ V=T.Xn R V:=funext fun i=>dc_k ..; unfold kI KissI zI RiftI sore; rw [he,norm_sub_sq_real,real_inner_comm _,show kZ (S:=S) (wit V Z) i=Tube.Z S Z V i from rfl,show fareG G (wit V Z i)= SU.group.price (tideX S k V U i) from fare_h ..] -- tune
 rw [Tube.Z,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,Real.sq_sqrt S.kernel.penalty_pos.le]; unfold tideX; ring
lemma inka(i:Cell c)(t:ℝ): kC T R t ∅ V i= -KissQ V T i:=by
 have he:wV T R t ∅ V=T.Xn R V:=funext fun i=>dc_k ..; unfold kC KissQ; rw [he,manta]; simp_rw [real_inner_self_eq_norm_sq]; rw [sum_sub_distrib]; unfold Tube.Xn; rw [← sum_div]; ring
lemma zpia(i:Cell c)(t:ℝ) : kL T R t ∅ V U (wit V (S.prediction U k)) i+kD T R t ∅ V i= ∑ j:Bool,(inner ℝ (RiftL R U V T k (i,j)) (T.Xn R V (i,j))+ inner ℝ (RiftD R V T (i,j)) (T.Xn R V (i,j))/2):=by
 have he:wV T R t ∅ V=T.Xn R V:=funext fun i=>dc_k ..; unfold kL kD zI zF; simp only [he,RiftL,RiftD, lGap,dGap]; rw [← sum_add_distrib]; apply sum_congr rfl; intro j _; rw [real_inner_comm (T.Xn R V (i,j)),real_inner_comm (T.Xn R V (i,j))]; rfl
lemma nk(i:Co c Gain)(x:ℝ): kN T R x ∅ V i= ‖RiftN R V T i‖^2/2:=by have he:wV T R x ∅ V=T.Xn R V:=funext fun i=>dc_k ..; unfold kN; rw [he]; rfl
end symbols
end YM.CF.Slate

import YM.CF.Appel.Font
import YM.CF.Appel.Cube
set_option autoImplicit false
noncomputable section
namespace YM.CF.Appel
open Char Summit Neige
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal NNReal
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c} {K v d s t:ℝ} {n:ℕ}
open Gaussian ProbabilityTheory AnalyticBridge.Annulus1AD
open Oriented Rows SectorNext.Remainder.Affine SectorNext.Remainder.Scales
variable(T:Tube G S) (A O:Stores S)(F:Forest S.ratio)(V:Config G c)(k:S.Choices)(q:Chi)(β d x:ℝ)(Y: LinkArray G (Frozen A x F))(l:ℕ)(z:LogArray G (Active A x F))
def pushP := credW T A F k q d x Y l V *ᵥ tape.symm z
-- partial additive gauges
variable (M: Signed→ Window S)
def embH:=emission T V x A k F q d Y M β (liftN T x V k A F q d Y l) (pushP T A F V k q d x Y l z)
def duty:= -(coupling β)⁻¹ * (Dira T A F k q d x Y l V ⬝ᵥ tape.symm z)
def phere := -(tape.symm z ⬝ᵥ (fullV T A F k q d x Y l V *ᵥ tape.symm z))/2
def leaseP(F:Config G f→E)(U:Config G f):= Real.exp (-β*Rows.fee T x V k A U) • F U
lemma lease_env [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]{U:Config G f→E} (h:Envelope U) (P:Teller G)(hp:P.Funds S T): Envelope (leaseP T A V k β x U):= Env.scale (((Envelope.const _).mul (Rows.fee_envelope _ _ _ _ _ hp)).exp) h
lemma seriesG {U:Config G f→E}{p:Allocation G S x C}(hp:0<β)(h:MossX n l x A F T V k K d t q)(J:ChartRatio G){K':ℝ}(ht:T.up.Bounds T.high s v K'): -- undecl
 let a:= putU β T F A V k x l q d Y z
 let u:= fieldU β T F A V k x l q d Y z;
 reelX β p q J x d T A F V k l (leaseP T A V k β x U) Y z = (capsule x A F q d J Finset.univ a * p.bill A k u V * S.likelihood u k * Real.exp (Real.log |(credW T A F k q d x Y l V).det| + embH T A F V k q β d x Y l z (fun _=>globe S)+duty T A F V k q β d x Y l z+ phere T A F V k q d x Y l z)) • U u:=by
 intro a u; obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩:=h.jumps Y; let g:= coupling β; let B:= embH T A F V k q β d x Y l z (fun _=>globe S); let e:= B+duty T A F V k q β d x Y l z+ phere T A F V k q d x Y l z
 have hv := chalk q Y hp ht (tape.symm z) h1.1 l
 have hp': Real.exp e= Real.exp (costU z /2) * Real.exp (-β*Rows.fee T x V k A u):=by
    unfold e duty phere; rw [neg_div,neg_mul, ← sub_eq_add_neg, ← sub_eq_add_neg,←Real.exp_add,add_comm]; exact congr_arg _ hv.symm -- tune
 let t:=|(credW T A F k q d x Y l V).det|
 change t • (Real.exp (costU z/2) • ((Next.SectorChange.reserve q J d a *doors q d a) • ((p.bill A k u V*S.likelihood u k) • (Real.exp (-β*Rows.fee ..) • U u))))= _
 have hh: 0<t:=abs_pos.mpr h7.ne_zero
 simp only [smul_smul]; congr 1
 rw [show Real.log _+_+_+_=Real.log t+ e from by unfold e B; abel, Real.exp_add,Real.exp_log hh,hp',show capsule x A F q d J Finset.univ a=Next.SectorChange.reserve q J d a*doors q d a from rfl]; ring
end YM.CF.Appel

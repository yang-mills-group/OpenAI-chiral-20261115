import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
variable (P:Spine)
abbrev readingSq (s:ℕ)(x:P.Test)(a:P.Spectrum0 3):ℝ:= (P.singleState 3 s a (P.reflectTest 3 x*x)).re
lemma as_paid {f:P.Test}{s:ℕ}(p:P.birthF 3 s f)(a:P.Spectrum0 3) : readingSq P s f a = ‖P.viewF 3 a s p‖^2:=by
 unfold readingSq; rw [← P.released_gram _ _ _ p p,inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal]; change (((‖P.viewF 3 a s p‖:ℝ):ℂ)^2).re=_; rw [←Complex.ofReal_pow,Complex.ofReal_re]
lemma paid_cont(s:ℕ)(f:P.Test):Continuous (readingSq P s f):= Complex.continuous_re.comp (P.chi_joint 3 _)
lemma paid_mean (s:ℕ)(f:P.Test): (∫ x,readingSq P s f x ∂ P.pillars 3)=(P.E s (P.reflectTest 3 f*f).val).re:=by
 let B:= P.reflectTest 3 f * f; let W:=P.reading 3 s B
 have e:= P.recovery 3 W; change (∫ x,P.chi 3 x W ∂P.pillars 3)=inner ℂ (P.groundZero 3) ((P.compressed 3 s B) (P.groundZero 3)) at e
 rw [P.occupied] at e
 rw [←e]; exact @integral_re _ _ _ ℂ _ _ ((P.chi_joint 3 W).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
#check P.positiveVox
#check art
#check marked
#check enclave_spec
#check integral_re
#check conj_trivial
#print axioms paid_mean
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

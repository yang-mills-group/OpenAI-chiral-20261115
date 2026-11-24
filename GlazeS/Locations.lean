import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
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
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
variable (P:Spine)
local notation "Λ₁"=>P.par
local notation "T"=>timeMesh P.par
abbrev optic (P:Spine)(s:ℕ)(o:Cover): Vantage:= fun i=> Tapestry.markZ P.par s (nodeC o i)/2
abbrev intrinsic (P:Spine)(s:ℕ):ℝ:= (22+P.calibration.ℓ:ℝ)/(2*precisionAt P.par s)
lemma countMoney : Tendsto (intrinsic P) atTop (𝓝 0):=by
 have h:1 < (P.par.R.L.val:ℝ):=by exact_mod_cast (lt_of_lt_of_le (by norm_num) P.par.R.coarse:1<P.par.R.L.val)
 exact tendsto_const_nhds.div_atTop ( (tendsto_pow_atTop_atTop_of_one_lt h).const_mul_atTop (by norm_num:0<(2:ℝ)))
lemma measureCatch(s:ℕ)(x:ℤ): measured P s x = Tapestry.markZ P.par s x/2:=by
 unfold measured markZ mill precisionAt; change ((x:ℝ)/((ruler P.par.block:ℤ):ℝ))*((( (T).base / ((T).L:ℝ≥0)^s:ℝ≥0):ℝ))=_; rw [NNReal.coe_div,NNReal.coe_pow,NNReal.coe_natCast]
 unfold ruler timeMesh; push_cast
 field_simp [(by exact_mod_cast P.par.block.property.ne': ((P.par.block.val:ℕ):ℝ) ≠ 0)]; ring
/- real footprint, including orientation history buffer -/
lemma expense(o:Cover)(s:ℕ){x:Vantage}(p:x ∈ P.pinFoot s (Calico.bands o 22))(i:Axis):|(optic P s o) i-x i|≤ intrinsic P s:=by
 obtain ⟨q,w,h⟩:=p
 have u:=h i; change |(precisionAt P.par s)*(2*x i)-(q i:ℝ)|≤_ at u
 have hx:= Calico.bands_spec o w i; have he:|((q i:ℤ):ℝ)-(nodeC o i:ℝ)| ≤22:=abs_le.mpr (by exact_mod_cast hx)
 have ht:0<(precisionAt P.par s):= Tapestry.positiveScale ..
 unfold optic markZ intrinsic; obtain ⟨h1,h2⟩:= abs_le.mp he; obtain ⟨h3,h4⟩:=abs_le.mp u; rw [abs_le]; change _≤_∧ _≤ _
 constructor <;> field_simp <;> change _≤_ <;> have v:P.calibration.ℓ=reserve P.par P.width:=rfl <;> rw [v] <;> linarith
-- center for representative at height s. translated cost at each resolution. x3=tidal & transverse fixed
abbrev central (P:Spine)(F s:ℕ):Vantage:= optic P s (cellar P F s)
lemma center3 (F s:ℕ): central P F s 3= tidal P F s := (measureCatch P _ _).symm
lemma centerSpace (F s:ℕ)(t:F ≤ s){i:Axis}(v:i≠3): central P F s i= measured P F 1:=by
 change markZ _ _ _/2=_; rw [←measureCatch,cellar,bellV,if_neg v,add_zero,subject,dutyT _ _ P.par.R.odd_side]
 simp only [Pi.smul_apply,nsmul_eq_mul,Nat.cast_pow]; exact marks_rec P _ s F t
#print axioms expense
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

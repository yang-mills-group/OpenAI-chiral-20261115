import Bay.D.Frond
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Resonance Brecht Circuit

variable {I J:Type*}[Fintype I][Fintype J]
abbrev Muff (I:Type*) :=Icey I
def dip (A:Icey I)(U:Muff I) := ∑i,∑j,A i j*U i j

lemma dip_bind (A:Icey I) (x:I→ℝ) :
 splash A x=dip A (fun i j=> Complex.ofReal (x i*x j)):=by
 simp [splash,swirl, Complex.real_smul,dip,mul_comm]

lemma dip_sub (A:Icey I)(U V:Muff I):dip A (U-V)=dip A U-dip A V:=by
 simp only [dip,Pi.sub_apply,mul_sub,sum_sub_distrib]
lemma dip_out(c:ℂ)(A:Icey I)(U:Muff I): dip A (c • U)=c*dip A U:=by
 simp only [dip,mul_sum,Pi.smul_apply,smul_eq_mul,mul_left_comm _ c]
lemma dip_in(c:ℂ)(A:Icey I)(U:Muff I): dip A (fun i j=>U i j*c)=dip A U*c:=by
 simp only[dip,sum_mul, mul_assoc]
def creamM (A:Icey I): Icey I:=fun i j=> star (A i j)
lemma cream_dip (A U:Icey I): dip (creamM A) (creamM U)=star (dip A U):=by
 simp [dip,creamM]
variable {A:Icey I}{s:Finset I}{f:ℝ}
lemma cream_fee(v:Rake s f A):Rake s f (creamM A):=by
 refine ⟨fun i j=>congrArg _ (v.sym i j), fun i j h=>?_,?_⟩
 · apply v.fits
   contrapose! h
   simp [creamM,h]
 simpa [swill,creamM] using v.fee

lemma dip_fee(v:Rake s f A) (U:Muff I){b:ℝ}(t:0≤b)(h:∀i∈s,∀j∈s,‖U i j‖≤b): ‖dip A U‖≤ f*b:=by
 refine le_trans ?_ (mul_le_mul_of_nonneg_right v.fee t)
 unfold swill; simp_rw [sum_mul]
 refine (norm_sum_le ..).trans (sum_le_sum fun i _=> (norm_sum_le ..).trans (sum_le_sum fun j _=>?_))
 rw[norm_mul]
 by_cases e:A i j=0
 · simp [e]
 have m:=v.fits _ _ e
 gcongr; exact h i m.1 j m.2
lemma dip_le (v:Rake s f A){U V:Muff I}{b:ℝ}(t:0≤b)(h:∀i∈s,∀j∈s,‖U i j-V i j‖≤b):
  ‖dip A U-dip A V‖≤f*b:=(dip_sub A U V) ▸ dip_fee v (U-V) t h

def dips (A:Icey I)(B:Icey J)(F:I→I→Muff J):=dip A (fun i j=>dip B (F i j))
variable {B:Icey J}{r:Finset J}{g:ℝ}
lemma dips_le (v:Rake s f A)(u:Rake r g B){U V:I→I→Muff J}{b:ℝ}(t:0≤b)
    (h:∀i∈s,∀j∈s,∀k∈r,∀l∈r,‖U i j k l-V i j k l‖≤b):
    ‖dips A B U-dips A B V‖≤f*(g*b):=
 dip_le v (mul_nonneg u.nonneg t) fun i hi j hj=>dip_le u t (h i hi j hj)

lemma dips_prod(A:Icey I)(B:Icey J)(U:Muff I)(V:Muff J):
 dips A B (fun i j k l=> U i j*V k l) = dip A U*dip B V:=by
 unfold dips
 rw[←dip_in]
 apply congr_arg
 exact funext fun i=>funext fun j=>dip_out (U i j) _ _
lemma dips_plus(A:Icey I)(B:Icey J)(U V:I→I→Muff J):
  dips A B (fun i j k l=>U i j k l+V i j k l)=dips A B U+dips A B V:=by
 simp [dips,dip,mul_add,sum_add_distrib]
lemma dips_times(A:Icey I)(B:Icey J)(c:ℂ)(U:I→I→Muff J):
 dips A B (fun i j k l=>c*U i j k l)=c*dips A B U:=by
 simp [dips,dip,mul_sum,mul_left_comm _ c]

variable {E:Type*}[MeasurableSpace E]{μ:Measure E} (A:Icey I)
lemma dip_int₀ (U:I→I→E→ℂ)(h:∀i j,Integrable (U i j) μ):
    Integrable (fun x=>dip A (fun i j=>U i j x)) μ:=
 integrable_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>(h i j).const_mul _))
lemma dip_int(U:I→I→E→ℂ) (h:∀i j,Integrable (U i j) μ):
 (∫x,dip A (fun i j=>U i j x)∂μ)=dip A (fun i j=>∫x,U i j x∂μ):=by
 simp_rw[dip]
 rw[integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=> (h i j).const_mul _))]

 refine sum_congr rfl fun i _=>?_
 rw[integral_finsetSum _ (fun j _=>(h i j).const_mul _)]
 simp_rw[integral_const_mul]
lemma dips_int(U:I→I→J→J→E→ℂ) (h:∀i j k l,Integrable (U i j k l) μ):
 (∫x,dips A B (fun i j k l=>U i j k l x)∂μ)
  =dips A B (fun i j k l=>∫x,U i j k l x∂μ):=by
 unfold dips
 rw[dip_int _ _ (fun i j=>dip_int₀ B _ (h i j))]
 exact congr_arg _ (funext fun i=>funext fun j=>dip_int B _ (h i j))

end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.dips_int

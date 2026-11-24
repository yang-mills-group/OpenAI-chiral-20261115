import YM.CF.BProof.Mote.Snow
import YM.CF.BProof.Law.Product
-- basic weighted operator transforms (no normalized state). step probabilities & mask errors
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory Cube SU Fock Lat Spire Scroll Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 26000
open Skye Law
namespace Wager
variable {X Y I E D: Type}[Fintype I][DecidableEq I][MeasurableSpace X][MeasurableSpace Y]
variable {μ:Measure X}[IsFiniteMeasure μ]{r:X→ℝ}
local instance measureVal (I : Type) [Fintype I] [DecidableEq I] : MeasurableSpace (Op I) := borel _
local instance billVal (I : Type) [Fintype I] [DecidableEq I] : BorelSpace (Op I) := ⟨rfl⟩
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
-- don't include measurable structs on avg
abbrev avg (μ:Measure X)(r:X→ℝ)(F:X→E):=∫ x,r x • F x∂μ
variable [NormedAddCommGroup D][NormedSpace ℝ D][MeasurableSpace D][BorelSpace D][FiniteDimensional ℝ D]
lemma fee {F:X→E} (p:Envelope F)(g:Envelope r):Envelope (fun x=> r x • F x):= Girt.kitE r F (· • ·) (continuous_fst.smul continuous_snd) g p -- FinDim proper
lemma take (μ:Measure X)[IsFiniteMeasure μ](L:E→L[ℝ]D){F:X→ E}(p:Envelope F)(h:Envelope r):avg μ r (fun x=> L (F x))=L (avg μ r F):=by
 unfold avg; have hx : Integrable (fun x=> r x • F x) μ:= Law.pay (fee p h); simp_rw [← map_smul]; exact L.integral_comp_comm hx -- tune direction
variable {φ:X→ E}
lemma one (μ:Measure X): avg μ 1 φ=∫ x,φ x∂μ:=by simp only [avg,Pi.one_apply,one_smul]
theorem abr (μ:Measure X) [IsFiniteMeasure μ] (U:Submodule ℝ E)(p:Envelope φ)(k:Envelope r)(h:∀ x, φ x ∈ U): avg μ r φ∈ U:=by
 let Z(x):U:=⟨φ x,h x⟩; have hx: Envelope Z:= ⟨p.meas.subtype_mk,p.cost⟩; change avg μ r (fun x=> U.subtypeL (Z x))∈U; rw [take μ U.subtypeL hx k]; exact Subtype.prop _ -- tune instances
end
abbrev penny(i j:I): Op I→L[ℝ]ℂ where
 toFun A := A i j
 map_add' _ _ := rfl
 map_smul' _ _:=rfl
 cont:= (continuous_apply j).comp (continuous_apply i)
variable {F G:X→ Op I}
lemma pane {F:X→ Op I}(p:Envelope F)(i j:I):Envelope (fun x=> F x i j):= Girt.pole_w F _ (penny i j).continuous p
lemma fund (μ:Measure X)[IsFiniteMeasure μ](p:Envelope F)(h:Envelope r)(i j:I): (avg μ r F) i j= avg μ r (fun x=>F x i j):=(take μ (penny i j) p h).symm
lemma engine (p:Envelope F)(h:Envelope G): Envelope (fun x=>F x * G x):= Girt.kitE F G (·*·) (continuous_fst.mul continuous_snd) p h
lemma company {f g:X→ℂ}(p:Envelope f)(h:Envelope g): Envelope (fun x=>f x * g x):= Girt.kitE f g (·*·) (continuous_fst.mul continuous_snd) p h
lemma factor (p:Envelope F)(h:Envelope G)(k:Envelope r)(e:∀ i j q:I, avg μ r (fun x=> F x i q * G x q j)=avg μ r (fun x=>F x i q)* avg μ r (fun x=> G x q j)): avg μ r (fun x=> F x*G x)= avg μ r F * avg μ r G:=by
 ext i j; rw [fund μ (engine p h) k i j]; simp_rw [Matrix.mul_apply,fund μ p k,fund μ h k,←e]; unfold avg; simp_rw [smul_sum]; exact integral_finsetSum _ fun j _=> Law.pay (fee (company (pane p _ _) (pane h _ _)) k)
-- usual symmetric Kontin.S.Sign average for tags and θ
variable {J:Type}[LinearOrder J][Fintype J]
def thetaCL (U:UNI J): FC J →L[ℝ] FC J where
 toFun:= Fock.theta U
 map_add':= theta_add U
 map_smul' z v:=theta_rsmul U v z
 cont:=theta_cont _
end Wager
end YM.CF.BProof.Bide

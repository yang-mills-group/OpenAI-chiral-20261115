import YM.CF.Continuum.Tether
import YM.CF.Continuum.CoolSieve
import YM.CF.Continuum.ReflectTest
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Window
open Function Filter NormedSpace Lattice Wilson Lat SU Fock Phase Mir Cube Mir.Trip RP Reflect Finset Spire Brace Spark Scroll Tulip Dial Scree Skye MeasureTheory RG
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I]
section limits
variable (K:ℕ→Matrix I I ℂ)(A:Matrix I I ℂ)
lemma proveLimit (e:∀ᶠ i in atTop,(K i).PosSemidef)(ht:∀ a b,Tendsto (fun i=> K i a b) atTop (𝓝 (A a b))) : A.PosSemidef:=by
 classical
 apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr; refine ⟨?_,fun x=>?_⟩
 · ext i j; exact tendsto_nhds_unique_of_eventuallyEq ((ht j i).star) (ht i j) (e.mono fun u v=>v.1.apply i j)
 let f(z:Matrix I I ℂ):=∑ i,star (x i)* ∑ j,z i j*x j
 apply ge_of_tendsto (x:=atTop) (f:=fun j=>f (K j)) (a:=f A); swap; · exact e.mono fun i v=>(Matrix.posSemidef_iff_dotProduct_mulVec.mp v).2 x
 exact tendsto_finsetSum _ fun i _=>tendsto_const_nhds.mul (tendsto_finsetSum _ fun j _=>(ht i j).mul_const _)
end limits
section compare
variable {m B:Side}{s:Axis}{P:Patch}
local notation "VZ"=> CSide m B
open Evenly
lemma psdTape (U: Orbit VZ→Phys VZ)(q:Integrable U (city VZ)) (H:TestOK m B s (moment U)) (T:I→Pane VZ→ℂ)(p:∀ i,ξTape s P VZ (T i)) : (reflectionForm s (moment U) (fun i=>bosonic VZ (T i))).PosSemidef:=by
 classical
 choose c F hc ht hV using fun i=>supportApprox _ (p i)
 let W(i:ℕ):= reflectionForm s (moment U) (fun j=>bosonic VZ (F j i)); apply proveLimit W _ (Eventually.of_forall fun i=>?_)
 swap; · exact H.ref_matrix s (fun j=> let z:= ht j i; ξ_obs P s _ z.2.1 z.1.localSites z.1.gauge)
 intro i j; let C:=max (c i) (c j); unfold W reflectionForm crossForm; simp only [Matrix.of_apply,boseP,θ_bosonic]
 exact chipPass U q (F i) (F j) _ _ C ((hc i).trans_le (le_max_left ..)) (fun k=>Envelope.compactC (ht i k).2.1) (fun k=>Envelope.compactC (ht j k).2.1) (fun n k=>((ht i n).2.2 _).trans (le_max_left ..)) (fun n k=>((ht j n).2.2 _).trans (le_max_right ..)) (hV i) (hV j) s
end compare
end YM.CF.Window
#print axioms YM.CF.Window.psdTape

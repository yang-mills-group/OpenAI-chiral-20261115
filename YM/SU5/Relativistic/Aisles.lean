import YM.SU5.Relativistic.Wade
import YM.SU5.Relativistic.FermiStep

/-! # lifting variable odd tests. -/
set_option autoImplicit false
set_option synthInstance.maxSize 25000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin

section books
variable {N:Side}{S:Support (More N)}{P:ℕ→ Mark N}{F:Mark N}{b:Bool}{C:ℝ}
lemma firmS (h:∀ i, AtSupport b S (P i))(t:∀ᶠ n in atTop, ∀ x, ‖P n x‖ ≤ C) (p:∀ x,Tendsto (fun i=>P i x) atTop (𝓝 (F x))) : AtSupport b S F:=by
 let Q:Submodule ℂ (FC (Single N)):= { carrier:={A| Reed.Fine (Tset N) (modesIn N S) b A}, zero_mem':= Reed.Fine.empty _, add_mem':= fun x y=>Reed.Fine.add x y, smul_mem':= fun i a x=>Reed.Fine.scale x _ }
 refine ⟨⟨measurable_of_tendsto_metrizable (fun i=> (h i).env.meas) (tendsto_pi_nhds.mpr p),C,fun x=>le_of_tendsto (p x).norm (t.mono fun i h=>h x)⟩,fun x y e k=>tendsto_nhds_unique_of_eventuallyEq (p x) (p y) (Eventually.of_forall fun i=>(h i).dep x y e k),fun x=>?_⟩
 exact Q.closed_of_finiteDimensional.mem_of_tendsto (p x) (Eventually.of_forall fun i=>show P i x∈Q from (h i).allV x)

variable (A: Finset Cover)
def coverCharge (v:Bool):ℝ:= if v=true then (Fintype.card (Singles A):ℝ) else Fintype.card (Evens A)
lemma cover_pays {b:Bool}{K:Calibration} {m:Side} {F:Family K} (p:InTest K true A b F)(q:Hosp A (K.c m))(h:∀ x,‖F m x‖ ≤ C) : pay F (coverCharge A b*C):= by cases b; exact concern _ _ p q C h; exact levy A _ p C q h
lemma inNeg {K:Calibration}{b:Bool}{S: Finset Cover}{F: Family K}(p:InTest K true S b F):InTest K true S b (-F):=by rw [←neg_one_smul ℂ]; apply InTest.smul _ p
lemma inLess {K:Calibration}{b:Bool}{S: Finset Cover}{F G: Family K}(p:InTest K true S b F)(q:InTest K true S b G):InTest K true S b (F-G):=by rw [sub_eq_add_neg]; exact p.add (inNeg q)
end books

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)
variable (s:ℕ){b:Bool}(i' k':ℕ)(p:legalAt Y s i' k') {S:Finset Cover}{F G:Family (tent Y H)}
local notation "W"=> wingspan Λ l S
local notation "M"=>moveUp Y H s i' k' S b
variable (u:Tivoli (wingspan Λ l S) ((tent Y H).c (momentm Y i' (s+1))))(h:InTest (tent Y H) true S b F)
include u p h
lemma addMove (v:InTest K true S b G): M (F+G)=M F+M G:= by
 apply charge_ext Y H _ i' _ u (stay ..) ((stay Y H ..).add (stay Y H ..)); rw [(distribute_arith Y H _ _ _ _ 1).1, rebased Y H s i' k' S p (h.add v) u, rebased Y H s i' k' S p h u,rebased Y H s i' k' S p v u,(distribute_arith Y H s i' F G 1).1]; exact Tapestry.ascendPlus _ _ _ _ p _ _ (parked Y H s i' S h).env (parked Y H s i' S v).env

 
lemma scaleMove (c:ℂ): M (c • F)=c • M F:=by
 apply charge_ext Y H _ i' _ u (stay ..) (InTest.smul _ (stay ..)); rw [(distribute_arith Y H _ _ (M F) (M F) c).2.2.1,rebased Y H s i' k' S p h u,rebased Y H s i' k' S p (InTest.smul c h) u,(distribute_arith Y H _ _ F F c).2.2.1]; exact Tapestry.ascendScale _ _ _ _ p _ (parked Y H s i' S h).env _
lemma glued {T: Finset Cover}(e:S⊆T)(v:Tivoli (wingspan Λ l T) ((tent Y H).c (momentm Y i' (s+1)))): moveUp Y H s i' k' T b F=M F:= charge_ext Y H _ i' _ v (stay ..) ((stay Y H ..).mono (wingspan_mono e)) ((rebased Y H s i' k' _ p (h.mono e) v).trans (rebased Y H s i' k' S p h u).symm)
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab

import Compass.Sloop
import Mathlib.GroupTheory.OrderOfElement
import Compass.Energy
import Compass.Schools
import YM.CF.Pec.Sorrel
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 25000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Compass
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Pastry Salt Hive Vow Skye Scion Levier Spire Scree Stilo
open Classical Finset
attribute [local instance] propDecidable
variable {G E P:Type*}[Group G][Fintype G][DecidableEq P][AddCommGroup E][Module ℝ E]
variable (ξ:G→ P→P) (M:G→ E→ₗ[ℝ] E)(C:G→ℝ)
-- pullM t(s)=M(t*s) indeed. orbit action flips.
variable (i j:P)
def frames {G P:Type*}[Group G][Fintype G][DecidableEq P](ξ:G→P→P)(i j:P):Finset G:= univ.filter fun t=> ξ t j=i
noncomputable def meanX {G E P:Type*}[Group G][Fintype G][DecidableEq P][AddCommGroup E][Module ℝ E](ξ:G→ P→P)(M:G→ E→ₗ[ℝ] E)(C:G→ℝ) (i:P)(x:E)(j:P):=let v:=frames ξ i j; ((v.card:ℝ)⁻¹) • ∑ t∈v,(C t) • M t x
variable (hq:∀ a b:G,∀ x:P,ξ b (ξ a x)=ξ (a*b) x)(hm:∀ s t:G,∀ x:E,M s (M t x)= M (s*t) x)(hc:∀ s t:G,C (s*t)=C s*C t)(hq0:∀ s:G,C s*C s=1)(x:E)
include hq
lemma f_frame (s:G): frames ξ i j=(frames ξ i (ξ s j)).map (Equiv.mulLeft s).toEmbedding:=by ext t; simp only [frames,mem_filter,mem_univ,true_and,Finset.mem_map]; exact ⟨fun h=>⟨s⁻¹*t, by rw [hq,mul_inv_cancel_left]; exact h, mul_inv_cancel_left ..⟩,fun ⟨a,v,p⟩=>by rw [←p]; rwa [hq] at v⟩
include hm hc hq0
lemma reyn (s:G): M s (meanX ξ M C i x (ξ s j))=C s • meanX ξ M C i x j:=by
 unfold meanX; let g:=(Equiv.mulLeft s); rw [f_frame ξ i j hq s]; simp only [Finset.sum_map,card_map,map_smul,map_sum]; rw [smul_comm (C s) ((_ :ℝ)⁻¹)]; apply congrArg (fun p:E=> (_:ℝ) • p); rw [Finset.smul_sum]; refine sum_congr rfl fun t _=>?_; change C t • M s (M t x)=C s • C (s*t) • M (s*t) x; rw [hm,hc,smul_smul,←mul_assoc,hq0,one_mul]
end YM.CF.Compass

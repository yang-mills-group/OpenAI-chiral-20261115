import YM.SU5.Selected.Cor.RideMark
import YM.SU5.FiniteGaugeData.Tower.RoomShape
import YM.SU5.Selected.Lantern.Scatter
import YM.SU5.Selected.Lantern.Pops
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
namespace Mezz
open Mint Numeric Afterglow
open Stencil (pace pval pulseNode heatize)
open Caste Payroll Tender
set_option synthInstance.maxSize 24000
attribute [local instance] opCStarAlgebra
variable {N:Side} (A:Mezz)
local notation "R" => Tender.widthK A.G A.D A.q.val
local notation "S" => park N A.Broad
local notation "B" => A.beams
local notation "T" => A.Broad
local notation "P" => park N
local notation "W₀"=> A.W
-- witness placement ∀ enough. positivity for any Hall seat3.
lemma horizonL (K:Calibration) (p:addgap K ≤ A.ℓ.val)(h:A.Legate): addgap K≤ A.W:=by have ht:= h.turn; have he:= A.geo_d; omega
lemma broad_test {x:Cover} (p:x∈ A.Broad)(j:Axis): -(↑(A.beams):ℤ)≤ x j-A.pal j∧ x j - A.pal j ≤ ↑(A.beams):=by obtain ⟨t,v⟩:=box_test.mp (plant_test.mp p); exact ⟨t j,v j⟩
lemma broad_time {x:Cover}(p:x∈ A.Broad): (400:ℤ)*A.W ≤ x 3 ∧ x 3 ≤ (1200:ℤ)* A.W:=by have h:= broad_test A p 3; rw [pal_z] at h; unfold beams at h; omega
lemma broad_hour (K:Calibration) (t:addgap K ≤ A.W): Tower.region 3 0 K.ℓ T:= by intro x v; have h:= (broad_time A v).1; unfold addgap stepgap at t; omega
lemma broad_date (K: Calibration) (u:addgap K ≤ A.W)(t:10*A.beams < N.val): park N T⊆ band N 3 0 K.ℓ:=
 Tower.SlabMark.enters_arc K 3 (x:=0) (fun x h=> by obtain ⟨a,b⟩:= broad_time A h; unfold addgap stepgap at u; unfold beams at t; constructor <;> omega) rfl
lemma precise_width : R=10000*W₀:=by unfold widthK W; ring
lemma broad_explicit {x:Cover} (h:x∈ A.Broad)(j:Axis): -(1200:ℤ)*A.W ≤ x j∧ x j ≤ (1200:ℤ)* A.W:=by
 have h':= broad_test A h j; by_cases t:j=3; · subst j; obtain ⟨a,b⟩:= broad_time A h; omega
 rw [pal_tr A t] at h'; unfold beams at h'; omega
lemma broad_cow (j:Axis): cows j (hyphen 3 0 S ∪ S) (R):=by
 refine ⟨(-1200:ℤ)*W₀,fun x k=>?_⟩
 rw [A.precise_width]; rcases mem_union.mp k with m|m
 · obtain ⟨t,e,rfl⟩:= mem_image.mp m; obtain ⟨w,kx,rfl⟩:= mem_image.mp e; rw [Shape.anno]; refine ⟨(plane 3 0).motion w j,?_,?_,rfl⟩ -- width
   all_goals rw [fling_move]; have hp:= A.broad_explicit kx j; split_ifs <;> omega
 obtain ⟨w,kx,rfl⟩:= mem_image.mp m; refine ⟨w j,?_,?_,rfl⟩ <;> have hp:= broad_explicit A kx j <;> omega
variable {M:Tulip.Male}{C ε:ℝ}{w:ℕ}{X Z: Coast→Wq A.marks}(c:Caste (N:=N) A M C (tightH A.D (billR C)) w X Z) -- may billR ambiguous
variable {d:Type}[Fintype d][DecidableEq d] (U:Society d)(K:Calibration)
local notation "T₀"=> triumph A U X Z C c
local notation "M₁"=>Station
local notation "Λ" => billR C
local notation "η"=> levyH A.D Λ
local notation "θ"=> Station.tollK (dueW Λ)
local notation "Act" => Service
lemma bargain {u t:ℕ} {δ ψ:ℝ} (p:addgap K≤A.W) (v:safeReflect M 4 δ N)
      (h:Lounge M 4 u t ψ η η θ Λ δ (A.Tack U) A.vowP (T₀)) : Act M 4 u t ψ η η θ Λ δ (A.Tack U) A.vowP [(T₀).shadow 3 0,T₀] ∧ ∀ i:Axis,cows i (Resort [(T₀).shadow 3 0,T₀]) R:=by
 let L:= triumph A U X Z C c; have ht:=Service.alone (h.shadow 3 0 v); constructor
 · apply ht.append (Service.alone h); change Disjoint (hyphen 3 0 S∪∅) (S∪∅); rw [union_empty,union_empty]; exact west K 3 0 _ (broad_date A K p c.enoughN)
 intro i; change cows i ((hyphen 3 0 S)∪ (S∪ ∅)) _; rw [union_empty]; exact broad_cow A i
lemma offer (j:Axis)(s:ℤ) (F:Cab N): guest [F.shadow j s,F]=reflMark j s F.frame * F.frame:=by change _*(_*1)=_; rw [mul_one]; rfl
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz
#print axioms bargain

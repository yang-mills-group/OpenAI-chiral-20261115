import Gingham.Ruff.Bouquet
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Buffered Afterglow Satin Tapestry
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
attribute [local instance] opCStarAlgebra
open Pastry


variable {K:Calibration}{S:Finset Cover}{U:Set PairsC}{C D:ℝ}{H:Bool}
variable {z:Option ℕ → Swatch S}
lemma swelling
   (h:∀i,z i∈Rose S K U C D H)
   (v:Tendsto (z ∘ some) atTop (𝓝 (z none))):
   Bouquet S C H (fun i=>render S K (z i)):=by
 refine ⟨fun i=>texture S K _,fun i=>(h i).2,?_⟩
 intro e q
 have d:(0:ℝ)<Tapestry.spread S + 1:=by unfold Tapestry.spread;positivity
 filter_upwards [(Metric.tendsto_nhds.mp v) (e/(Tapestry.spread S+1)) (by positivity)]
    with i b
 rw [←map_sub]
 intro m x
 refine (appearLe S K m (z (some i)-z none) x).trans ?_
 rw [←dist_eq_norm,mul_comm]
 exact ((mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one)
      dist_nonneg).trans ((le_div_iff₀ d).mp b.le))
variable {I:Type}[Countable I]


/-- Simultaneous subsequence extraction including infinitely many sizes. -/
theorem gardens {S:I→Finset Cover}{U:I→Set PairsC}
   {C D:I→ℝ}{H:I→Bool}(c:∀i,0≤C i)(d:∀i,0≤D i)
   (z:ℕ→(i:I)→Swatch (S i))
   (h:∀n i, z n i∈Rose (S i) K (U i) (C i) (D i) (H i)):
   ∃ (ν:ℕ→ℕ) (x:(i:I)→Option ℕ→Swatch (S i)), StrictMono ν∧
   (∀i m, x i m∈ Rose (S i) K (U i) (C i) (D i) (H i))∧
   (∀n i, x i (some n)=z (ν n) i)∧
   (∀i, Tendsto (x i ∘ some) atTop (𝓝 (x i none))) ∧
   ∀i,Bouquet (S i) (C i) (H i) (fun j=>render (S i) K (x i j)):=by
   obtain ⟨a,t,ν,V,W⟩:= (isCompact_pi_infinite (fun i=>
      fenced (S i) K (U i) _ _ (H i) (c i) (d i))).tendsto_subseq (x:=z) h
   let x(i:I)(m:Option ℕ):Swatch (S i):=
      m.elim (a i) (fun n=> z (ν n) i)
   have v(i:I): Tendsto (x i ∘ some) atTop (𝓝 (x i none)):=tendsto_pi_nhds.mp W i
   have y(i:I)(m): x i m ∈ Rose (S i) K (U i) (C i) (D i) (H i):=by
     cases m
     · exact t i
     exact h _ i
   exact ⟨ν,x,V,y,fun _ _=>rfl,v,fun i=>swelling (y i) (v i)⟩
#print axioms gardens

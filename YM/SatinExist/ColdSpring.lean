import YM.SatinExist.OneCup
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
namespace OneCup
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower
variable (K:Calibration)
private lemma cored (S:Finset Cover)(i:Evens S): InTest K true S false (Sound.sing K (tagWord S i.val)):= by simpa only [i.property] using sung K _ (Satin.brand S i.val)
def toastPoint (S:Finset Cover)(i:Evens S): Dome K:= ⟨Sound.sing K (tagWord S i.val), broadCompile K S (cored ..)⟩
private def silkBit (S:Finset Cover)(u:Pigment S): Dome K:= ⟨scalar K (daub S u),broadCompile K S (.seed (authentic ..))⟩
variable {K}
lemma toastAt (S:Finset Cover)(i:Evens S): toastPoint K S i∈ bay K S true:= (locates ..).2 (cored K S i)
lemma cutsUp (E:Dome K→ₗ[ℂ]ℂ)(S:Finset Cover)(u:Swatch S): slice K E (badge K S u) = ∑ i:Evens S, E (toastPoint K S i) • silkBit K S (u i):=by
 have hz: badge K S u=∑ i:Evens S, silkBit K S (u i)*toastPoint K S i:=by
   apply Subtype.ext; change render S K u=(screenHall K).val _
   rw [render_eq,map_sum]; apply sum_congr rfl; intro i _; rfl
 rw [hz,map_sum]; apply sum_congr rfl; intro i _; exact slicer K E _ _ ⟨S,_, authentic S (u i),rfl⟩ (wordIndependent K (tagWord S i.val))
lemma cuts_local (E:Dome K→ₗ[ℂ]ℂ)(S:Finset Cover)(a:Dome K)(p:a∈bay K S true): slice K E a∈bay K S true:=by
 obtain ⟨x,rfl⟩:= accolade K S a p
 rw [cutsUp]; exact Submodule.sum_mem (bay K S true).toSubmodule fun i _=> Submodule.smul_mem _ _ ((locates K S true (f:=silkBit K S (x i))).mpr (by exact InTest.seed (authentic ..)))
lemma toast_limit (E:Dome K→ₗ[ℂ]ℂ)(S:Finset Cover)(m:Side)(r:Hosp S (K.c m))(a:Dome K)(p:a∈bay K S true)(B:ℝ)(L:Evens S→ℝ)
    (b:∀ v, ‖a.val m v‖ ≤ B)(l:∀ i, ‖E (toastPoint K S i)‖ ≤ L i)(n:Side)(V:Fields (K.c n)): ‖(slice K E a).val n V‖ ≤ (∑ i, L i)*B:=by
 let x:= trophy K a p; have ht: a=badge K S x:= (trophy_at ..).symm; rw [ht,cutsUp]
 have hz:‖x‖≤ B:= trophy_bounds K a p r b
 change ‖((screenHall K).val _) n V‖≤ _
 rw [map_sum]; simp_rw [map_smul,Finset.sum_apply,Pi.smul_apply]; rw [sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum (fun i _=>?_)); rw [norm_smul]
 refine mul_le_mul (l i) ?_ (norm_nonneg _) ((norm_nonneg _).trans (l i)); change ‖(daub S (x i) _) • (1:FC _)‖ ≤ B; rw [norm_smul,norm_one,mul_one]; exact (daubLe ..).trans ((norm_le_pi_norm ..).trans hz)
#print axioms toast_limit
end OneCup
end YM.CF.Buffered.Afterglow.Six

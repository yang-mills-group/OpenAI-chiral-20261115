import YM.SU5.FiniteGaugeData.Tapestry.PalmCourt
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude Heat Pastry
open PiTensorProduct (tprod)

/-!
# Fixed volume all level UV estimates

Local assessed price (unlike `Pavilion` geometric prices) depends on native torus,
NO claim holds as period increases. Dual norm passage across all UV rows applies
even when the cover support & frame bills aren't tested (e.g. when the one fixed
test box too large for a particular row qualification). Use just for the separate
cutoff limit first.
-/
set_option quotPrecheck false
section
variable (Z:ℕ→ Side)
local notation "U" i:max => Ward (Z i)
abbrev Ballet := ∀ i:ℕ,Ward (Z i)→L[ℂ]Ward (Z (i+1))
def awardStart (n: Side): Ward n →L[ℂ] Ward n:= ContinuousLinearMap.id ℂ _
def blossom (z:Side): Ward z →L[ℂ] (Ward z →L[ℂ] Ward z):= ContinuousLinearMap.mul ℂ (Ward z)
noncomputable def accolading (p:Ballet Z) (n:ℕ) (x:∀ i:ℕ,Ward (Z i)) : Ward (Z n):=
  Altitude.herring (X:=fun i=> U i) (Y:=fun i=> U i) (awardStart (Z 0)) (fun i=> blossom (Z (i+1))) p n x
variable (p:ℕ→ Ballet Z)(a:Ballet Z)(n:ℕ)(q:∀ i,Tendsto (fun k=>p k i) atTop (𝓝 (a i)))
lemma awards_init (x): accolading Z a 0 x=x 0:=rfl
lemma awards_succ (x): accolading Z a (n+1) x= a n (accolading Z a n x)*x (n+1):=rfl
include q
lemma summery (F:ℕ→Ward (Z n)→L[ℂ]ℂ)(s: Ward (Z n)→L[ℂ]ℂ)(t:Tendsto F atTop (𝓝 s)): ∀ ε:ℝ,0<ε→∀ᶠ k in atTop,∀ x: (∀ i:ℕ,Ward (Z i)),
 ‖F k (accolading Z (p k) n x)- s (accolading Z a n x)‖ ≤ ε*nectar n x:= upstream (X:=fun i=> U i) (Y:=fun i=> U i) (awardStart (Z 0)) (fun i=> blossom (Z (i+1))) a n p q s F t
-- apply herring size. constant selected row
lemma ballroom : ∃ D:ℝ,0 ≤ D∧ ∀ᶠ k in atTop, ∀ x:(∀ i:ℕ,Ward (Z i)), ‖accolading Z (p k) n x‖≤ D * nectar n x:=by
  let M(i:ℕ):=‖a i‖+1; let X:= awardStart (Z 0); let V(i:ℕ):= blossom (Z (i+1)); let g :∀ i,0≤ M i:=fun i=>add_nonneg (norm_nonneg (a i)) zero_le_one; refine ⟨_,positiveQ (X:=fun i=>U i) (Y:=fun i=>U i) X V _ g n,?_⟩
  have he(i:ℕ): ∀ᶠ k in atTop, ‖p k i‖ ≤ M i:= (Altitude.glimpse (Y:=fun i=>U i) a p q i 1 zero_lt_one).mono fun k h => by unfold M; rw [add_comm ‖a i‖]; exact Altitude.opPriceBelow (V:=Ward (Z i)) (W:=Ward (Z (i+1))) h le_rfl -- _:=V notation conflict?
  exact ((eventually_all_finset (Iic n)).mpr fun i _=>he i).mono fun k h x=> herringSize (X:=fun i=>U i) (Y:=fun i=>U i) X V (p k) M n (fun i k=> h i (mem_Iic.mpr k.le)) x
end
end YM.CF.Buffered.Afterglow.Tapestry

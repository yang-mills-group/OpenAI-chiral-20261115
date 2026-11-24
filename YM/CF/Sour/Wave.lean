import YM.CF.Sour.Maize
import YM.CF.Sour.Seal
import YM.CF.Exa.Water
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
variable {κ:Type}[TopologicalSpace κ][Nonempty κ]
variable {ι:Type*} {m:ℕ} {δ b a:ℝ}
open Sault
lemma mood (T S:WG ι)(p:Lively T)(t:Lively S)(q:∀ i N,S i N 1=0)(m:ℕ)(ε:ℝ)(v:0<ε) : ∃ (a b c d:ℝ),0<a∧0<b∧0 ≤ c∧((a/(m+1:ℝ))⁻¹)^m*c≤ ε∧0<d∧a≤1∧∃ n:ℕ,∀ (M:Side),n ≤ M.val→∀ i z e,0<e→e≤ d→0≤z→∀ (κ:Type)[TopologicalSpace κ][Nonempty κ](Z:κ→ Op SU.Slot),Continuous Z→(∀ i,Mind (Z i))→(∀ i,‖Z i‖≤z)→ Piety M (T i M) (S i M) Z a z (b*z) (c*z) e:=by
 obtain ⟨B,c,e₀,hB,hc,he,c',A,C⟩:= p.link t; let M':= Tap.wingRent Fir.Aop B; let Q':=Tap.wingRent (Fir.Aop-(1/2:ℂ) • 1) B; let Y:=max c (max M' Q'); have hY:0<Y:=hc.trans_le (le_max_left ..)
 let W:=sprigK Y; have hW:0<W:=by unfold W sprigK; positivity
 obtain ⟨a,e,v',ha,hs,hV,hD,he',hr,H',L,G⟩:= estate_m m C hB he hc (min (ε/W) Y) (lt_min (by positivity) hY) (fun i N _=> q ..)
 have hk:v'≤Y:=by
    apply (le_mul_of_one_le_left hr _).trans (H'.trans (min_le_right ..)); apply one_le_pow₀; rw [one_le_inv₀ (by positivity)]; exact (div_le_self ha.le (by simp)).trans he'
 have hu:a≤ B:=hD.trans (half_le_self hB.le); let C0:=χr Y; have hU:0<C0:=by unfold C0 χr loan_L spiritK sprigK qy_K; unfold spiritK sprigK; positivity
 refine ⟨a,C0,W*v',e,ha,hU,mul_nonneg hW.le hr,by rw [mul_left_comm]; exact (mul_comm ..).le.trans ((le_div_iff₀ hW).mp (H'.trans (min_le_left ..))),hs,he',max c' L,fun M z i b d g h b' κ _ _ Z h' y v =>?_⟩
 let Q(t:κ):= -(plankP M (Z t))
 have h₁:Solo a v' (S i M) d:=axis_down a v' (G i M ((le_max_right ..).trans z)) _ g h
 have h₂:Solo a Y (T i M) d:=((axis_down B _ (A i M ((le_max_left ..).trans z)) _ g (h.trans hV)).drop hu).books (le_max_left ..)
 have h₃:Solo a Y (fun _=> tickA M) d:= ((soil_tick B d).drop hu).books ((le_max_left ..).trans (le_max_right ..)) -- check soil args implicit
 have h₄: Milli d M (fun i _=>Q i) (Y*b) a:= (((barK (a:=B) d M Z b (Fir.Aop-(1/2:ℂ) • 1) b' h' v (fun i g=>(y i).firm g)).neg_m.dusk hu).tall (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_max_right ..)) b'))
 exact ours M _ _ Z h₄ h₂ h₁ h₃ hY.le hr hk b' ha.le he'
end YM.CF.Sour

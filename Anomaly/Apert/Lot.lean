import Anomaly.Apert.Employee
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
variable {n : Side}


namespace LocalLimit
namespace Preparation
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell QuadClock Ione.Clock Moto Neon Taxi Lor
open Oise Pitching Focus
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) (k0:ℕ)(Γ:ℝ)

local notation "p0"=> Y.meter.a 0

lemma calendar_Long {H U:ℝ→ℝ}(t:Quench P.R H)(p:Quench P.R U):
    ∀ᶠ s:ℕ in atTop, let X:=hat P.R.L P.x s; let x:=hat P.R.L P.x (s+1)
                         let y:= colorsPhi P.R.L Γ X; let z:= stageΛ Y Γ H x; let v:= chargeC Y Γ k0 H U x
                         let w:=wakeK k0 U x
                         0≤ y∧ v ≤ y ∧ w ≤ y ∧ z ≤ y ∧ Real.exp 1*z ≤ y ∧ Real.exp 1 *((2*Moto.peka_H (p0).power)*z) ≤ y∧ 0≤z :=by -- 0≤wakeK if U not positive! require BScale.hold or modify. passCotton needs v or maybe g: μ≤d from y.Nonneg rather than v and no w≥0
  let T:=hat P.R.L P.x; let K:=P.R.L
  have hB:∀ᶠ s:ℕ in atTop,0 ≤ colorsPhi P.R.L Γ (T s):=by
    filter_upwards [(turnover P).eventually (colors_more P.R Γ 0)] with i p
    simpa only [zero_mul] using p
  obtain ⟨V,C,Z,D,Hs⟩:=quenchingStage Y Γ k0 H t U p
  have hx(Q:ℝ→ℝ)(u:Quench P.R Q):∀ᶠ s:ℕ in atTop,Q (T (s+1))≤ colorsPhi P.R.L Γ (T s):=by
    let G:= allotΨ K
    have hH:∀ᶠ s:ℕ in atTop,G (T (s+1))≤ G (T s):=by
       filter_upwards [(turnover P).eventually (pal_U K (billX K) (pitch _))] with i p; unfold T; rw [hat_succ]; exact p.2.1 -- tune opts
    have hu:Tendsto (fun s:ℕ => T (s+1)) atTop atTop:= (turnover P).comp (tendsto_add_atTop_nat 1) -- tune
    filter_upwards [hH,(turnover P).eventually (colors_more P.R Γ 1),hu.eventually (draft_π P.R.L),hu.eventually (u.spine_a.eventually (ge_mem_nhds zero_lt_one))] with i e v h w -- u.spine_a notation via cast
    let x:=T (i+1); have hp:0<G x:=pow_pos h.2.1 _; rw [one_mul] at v; refine le_trans (?_: Q x≤G x) (e.trans v); exact (by simpa only [one_mul] using (div_le_iff₀ hp).mp w)
  filter_upwards [hB,hx _ D,hx _ Hs,hx _ Z,hx (fun i=>Real.exp 1*stageΛ Y Γ H i) (Z.manyF _), hx _ ((Z.manyF (2*Moto.peka_H (p0).power)).manyF (Real.exp 1))] with s p v w z q y
  exact ⟨p,v,w,z,q,y,mul_nonneg costPos (mul_nonneg (by unfold Δv; positivity) (by unfold fees putTip reserveT coin_n stilK BScale.runway; positivity))⟩

variable (flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)
include flag
lemma frameCredit :∀ᶠ s:ℕ in atTop, let x:=hat P.R.L P.x s; let μ:=3*dleaf P.R.L x
                                  μ≤ 1 ∧ ∀ᶠ i in atTop,∀ k:ℕ,s<Y.uv k→Arc_r (RootBook Y i k (s+1)) P.h μ μ μ∧ (RootBook Y i k (s+1)).slip=0 := by
  let X:=hat P.R.L P.x; have hP:= ((npl_chill (dirP P.R.L)).cheap 3).spine_a.eventually (ge_mem_nhds zero_lt_one); filter_upwards [(turnover P).eventually hP] with s p
  intro x μ; refine ⟨p,?_⟩; filter_upwards with i k u
  let N:=Y.uv k; let Z:=(Y.voyage i).X N; let X₀:=Z.pull
  obtain ⟨Xc,Kx,Hr,Jx⟩:= flag i N
  let Yb:=Xc.clocks s; have hc:=Yb.leaf_mono (X (s+1)) (hat_mono (by omega)); have hB:=Yb.leaf
  let E₁:=Z.pull.note (s+1) u
  have hv:0≤dleaf P.R.L x:=by linarith only [hB]
  exact ⟨E₁.vest μ μ μ (by unfold μ; linarith only [hc,hB]) (by unfold μ; linarith only [hc,hB]) (by unfold μ; positivity), E₁.tone⟩ -- tune parameters For Force

end Preparation
end LocalLimit
end YM.CF.Py.Rate

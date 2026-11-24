import Anomaly.Rack.Ink
import YM.SU5.Exchange.Force.Band
/-!
Aperture preparation. State stand-alone electricity so can consume it on
later post-Orientation pin data as well. Does NOT consume motion rights.
-/
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
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell QuadClock Lor
variable {P:Preparation} {F:(n:Side)→ Scree.Loom n→Prop}(Y:Course P F)
local notation "α" i:max s:max => P.Ctor (Y.ir i) s

lemma p_meters (i k s:ℕ)(hk:s<Y.uv k) : -- tune
 let p:=(RootBook Y i k s).p; let X:= hat P.R.L P.x s
 p.B=radiusB X ∧ p.threshold=temp X ∧ p.order=6∧ p.power=2∧p.supportExponent=1:=by
  intro p X; have he:p=Y.meter.a s:= (((Y.voyage i).X (Y.uv k)).pull.owns s hk.le).width.symm
  rw [he]; obtain ⟨t,hx,b,q,v⟩:= Y.meter.boot s; exact ⟨hx,t,v,q,b⟩

-- costs in downstream Shelf formulas and Quench. 0<t threshold.
abbrev wakeE (h:ℝ→ℝ) (x:ℝ):= reserveT 2 6 (radiusB x) (BScale.runway x)* dollarT (radiusB x) (BScale.runway x) (h x) -- in Facade maybe not imported, use formula
abbrev wakeK (k:ℕ)(h:ℝ→ℝ)(x:ℝ):= Real.exp (3*(k:ℝ))*(reserveT 2 6 (radiusB x) (BScale.runway x)*(h x*200))
abbrev putTip (n:ℕ)(d:ℝ→ℝ)(x:ℝ):= reserveT n 6 (radiusB x) (BScale.runway x)* |d x|
abbrev wakeL (p:ℝ→ℝ)(x:ℝ):= Vow.TreasuryFog.sigma (BScale.runway x + BScale.runway x) (radiusB x) * wakeE p x

lemma wakePrice(k:ℕ)(U:ℝ→ℝ)(L:Patch)(t:Quench L U): Quench L (wakeE U)∧ Quench L (wakeK k U) ∧Quench L (putTip 2 U)∧ Quench L (putTip 3 U)∧ Quench L (wakeL U):=by
  have H:Quench L (wakeK k U) := by
    let p(x):=U x*200; have he:Quench L p:=by unfold p; simp_rw [mul_comm _ (200:ℝ)]; exact t.manyF _
    exact (he.bondF (reserve_bond 2 6)).manyF _
  have p:Quench L (wakeE U):=(dollar_Q _ _ t).bondF (reserve_bond 2 6)
  refine ⟨p,H,(t.normF).bondF (reserve_bond 2 6),(t.normF).bondF (reserve_bond 3 6),?_⟩
  apply p.bondF
  apply (BoreP.still 1).tune
  filter_upwards with x; change |Real.exp _| ≤ _; rw [abs_one,abs_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]; unfold BScale.runway; -- tune positivity
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _)) (by positivity)

structure ReadyBench (Y:Course P F)(x G d Z K:ℝ) (A:GramM n) (u:ℕ):Prop where
  heads:A.p.B=radiusB x ∧ A.p.threshold=temp x ∧ A.p.order=6 ∧ A.p.power=2 ∧ A.p.supportExponent=1 ∧ 3 ≤ A.p.B
  fence: ThresholdPool A.p.B (A.p.B:ℝ)⁻¹ (inkScatter u A.p.B |G|) (chi_f 6*K) (inkScatter u A.p.B |d|) Z
  data: FlagWidth A.p A.K (cipherK P.J.n)∧SanB A.K (giftK A.p (A.p.supportExponent+(1:ℝ)/2)) A.p P.h (fun _=> K)
  debt: (9:ℝ)*3*(u:ℝ) ≤ (A.p.B:ℝ)⁻¹ * (A.p.B:ℝ)^2

-- readiness purchased with OrbitJet:
variable {Pay kc G_:ℝ} {Tξ:Hove.Grant P.K.j 2} {w j:ℕ}
    (W:Sweepcraft Y Tξ Pay kc G_ w j)(k0:ℕ) (G D:ℝ→ℝ) (hf:Chill_v G)(hD:Quench P.R D)
include W hf hD

theorem benchEarn :∃ X U:ℝ→ℝ, Quench P.R U ∧∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s<Y.uv k →
   let x:=hat P.R.L P.x s; ReadyBench Y x (G x) (D x) (U x) (X x) (RootBook Y i k s) k0:=by
  obtain ⟨Z,W',V1,K,t,u⟩:=W.scene
  obtain ⟨U',v,g⟩:= spanning P.R (billScatter k0 G hf) ((show Quench P.R K from t.mint).manyF (chi_f 6)) (billScatter2 k0 _ hD)
  refine ⟨K,U',v,?_⟩; filter_upwards [u,(turnover P).eventually g, (Work.E01.radiusB_tendsto.comp (turnover P)).eventually_ge_atTop (3+9*3*k0)] with s t q w; filter_upwards [t] with i t k h _
  let A:= RootBook Y i k s; obtain ⟨hx,hy,hk,p',u⟩:= p_meters Y i k s h; have he:3+9*3*k0 ≤ A.p.B:= hx.symm ▸ w
  refine ⟨⟨hx,hy,hk,p',u,show 3≤ A.p.B by omega⟩,by unfold BScale.runway at q; simpa only [hx] using q,?_ ,?_⟩
  · exact AstroFunding.radius _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (t k h) -- tune underscores
  change (9:ℝ)*3* _≤ (A.p.B:ℝ)⁻¹*_ ; have hz: (A.p.B:ℝ)≠0:=by exact_mod_cast A.p.B_pos.ne'
  rw [pow_two,←mul_assoc,inv_mul_cancel₀ hz,one_mul]
  have hg:(9:ℕ)*3*k0 ≤ A.p.B:=by omega
  exact_mod_cast hg

end Preparation
end LocalLimit
end YM.CF.Py.Rate

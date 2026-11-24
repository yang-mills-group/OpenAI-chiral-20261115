import YM.CF.Vp929.Loan.Nuptial
import YM.CF.Vp929.Stage.Banker
import Thin.Pave
import YM.CF.Vp929.Kinematic.Cellar
import YM.CF.Vp929.Kinematic.Vapor
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
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
namespace Pitching
local notation "G5"=> SU.group
local notation "S'"=> w.step V
local notation "y"=> Scales.y SU.group R.L x
local notation "ι" => Scree.mid m B
local notation "η" => Scree.mid n B
local notation "z'" => (coming D.Z 105 5*radiusB x)
variable {o : Pitching w D x}
local notation "Bs" v:max F:max => base (q:=q) (J:=J) (w:=w) p' v F
local notation "Ys" β:max F:max=> Pitching.input (V:=V) (w:=w) p' β F
local notation "Xs" β:max => Pitching.start (V:=V) (w:=w) p β
local notation "A'"=> o.muster
local notation "P'"=> D.pilot
local notation "Up" v:max=> (tint_z o.muster v)
local notation "Jq"=> (w.Φ (V:=V))
namespace Cellar
variable {N0:ℕ} (Z:Cellar N0 o p p' c f ag Cg)
open Lilt Lid Plume.Rate
variable {X:Pilot}{F:Corr (Scree.mid n B)}
variable (t:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V)))(P0:Ride (w.step V))
local notation "ρ₁"=> D.pilot.hat R x
local notation "ιw"=> ρ₁/2
local notation "M'"=> Stilo.bay P0
local notation "FV"=> (cook S' t.toLeft).flags
local notation "Φ₀"=> Rue.litres p.threshold (Stilo.bay P0) (cook S' t.toLeft).flags
local notation "Ω"=> Cord S'
local notation "Λ"=> (quanta (x:=x))
local notation "H"=> Z.toLid
local notation "χ"=> shotM o.muster.vita
local notation "Υ" X:max v:max=> (χ (Pilot.hat X R x) v:ℂ)
local notation "μ"=> Cipher ι
variable (hF:Location.gross p' D f F)
/- extended unintegrated formula under the real pole change: keep all other factors frozen in kinematics; `tokenFuel` independent of inputs, Gauge and Y-coordinates -/

open Appel
private theorem tableAC (G:Gauge){I:Type}[Fintype I]{a b:ℝ}(hp:0<a)(e:a≤b): tableG G I a ≪ tableG G I b:=by
  have h:=meal G hp (α:=I)
  have h':=meal G (hp.trans_le e) (α:=I)
  have hx : surface G I a⊆ surface G I b:= fun _ i j t=> (Metric.closedBall_subset_closedBall e) (i j t)
  intro u hu
  have he : ((grainS G a)^Fintype.card I • tableG G I a) u = 0:= by
    apply le_antisymm _ bot_le
    rw [h]; refine le_trans (Measure.restrict_mono_set _ hx u) ?_
    rw [←h',Measure.smul_apply, smul_eq_mul,hu,mul_zero]
    exact le_refl 0
  rw [Measure.smul_apply,smul_eq_mul] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (grain_pos _ hp).ne')

private theorem plumAC {a b:ℝ}{w:Location (R:=R) B m n}(p:0<a)(e:a ≤ b) :
    plummy (w.step V) a ≪ plummy (w.step V) b:=by
  letI := how (α:=Bond (Domain n B)) SU.group (p.trans_le e)
  letI := lum_p (w.step V) (p.trans_le e)
  unfold plummy springT
  exact Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl
    ((Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl (tableAC _ p e)).prod
      Measure.AbsolutelyContinuous.rfl)

variable (hb:β∈Year R x)

local notation "Jo"=> Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))
-- tokenFuel factors through a totally finite space, even at fixed large volume.
private lemma count_rails(t:Jo): ∃ f:Arena.Tab S'→ℕ,∀ q:Cord S',tokenFuel t q=f q.1:=
 ⟨fun v=>∑ j∈ liftK S' t.toLeft, Fintype.card (Frozen j.val x v.1),fun _=>rfl⟩

private lemma finite_amount {I:Type}[Finite I](w:I→ℝ):∃ A>0,∀ i:I,w i≤ A:=by
 classical
 letI:= Fintype.ofFinite I
 refine ⟨1+∑ i:I, |w i|, add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg fun i _=>abs_nonneg _),fun i=>?_⟩
 exact (le_abs_self _).trans ((single_le_sum (fun i _=> abs_nonneg (w i)) (mem_univ i)).trans (le_add_of_nonneg_left (by norm_num)))

local notation "u₁"=> D.pilot.hat R x
local notation "P₂"=> Z.toLid.ZoomB hb
local notation "b₂"=> (P₂).hat R x
local notation "F₀"=> (Z.toLid.crew β hb).1
local notation "F₂"=> Z.toLid.fend hb (Z.toLid.scaler hb)
local notation "Loc"=> Palot.leaf (Site (Domain m B))

open Oise
include Z hb
/-- LookZ transfer by ratio and magnification. `Y` on credits uses base offset;
independence of offsets will be applied separately. -/
theorem lookThin (J_:ℕ) (cQ vL:ℝ) {v₁ bL σ κq Bv:ℝ}{nₐ:ℕ}
    (M : Climate D.pilot R c x v₁ bL σ κq ag Cg Bv nₐ)
    (hv:(β:ℂ)∈ Ledge nₐ v₁ (Scales.y SU.group R.L x)) :
    ∃ z:ℝ,∀ F:Corr (Scree.mid n B), ∀ he:Location.gross p' D f F,
      LookZ V (Xm:=Xs β) (Xu:=Ys β F) o.SheepR F₀ (Z.toLid.choice hb he) o.bags o.vista J_ cQ vL →
      ∀ θ:base (w:=w) (J:=J) (q:=q) p' β F,
      LookZ V (Xm:=Xs β) (Xu:=Ys β F) o.SheepR F₂ θ o.bags o.vista J_ z vL := by
 let eP:ℂ:= ↑(χ u₁ β) / (↑(χ b₂ β):ℂ)
 choose lens hl using fun t:Jo=> count_rails t
 obtain ⟨Ar,cA,lA⟩:= finite_amount (fun v:Jo × Arena.Tab S'=> ‖eP ^ lens v.1 v.2‖)
 have ha (i:Jo)(t:Cord S') : ‖eP^tokenFuel i t‖ ≤ Ar:= by rw [hl]; exact lA (i,t.1)
 let c₁:=((Up β).loft+(Up β).post+200)*radiusB x
 let c₂:=coming D.Z 105 5*radiusB x
 obtain ⟨Bc,bB,qB⟩:= finite_amount (fun i:Loc=> Jade.pave_ c₁ c₂ u₁ cQ vL (luceL R J_ x) S' p i (radiusB x))
 let ta:= Z.toLid.scaler hb
 have hy:0 < b₂ := mul_pos (P₂).high (Scales.pos ..)
 have hx: b₂ ≤ u₁:= Pilot.hat_zoom ..
 obtain ⟨c₃,pv⟩:= Jade.paveThin S' p b₂ hy c₁ c₂ (luceL R J_ x) vL (Ar*Bc) (radiusB x)
 refine ⟨c₃,fun F e h θ i C Av u hA=>?_⟩
 dsimp only
 let T':= Z.toLid.choice hb e
 let g':= Z.grand i (Stilo.beamH C.val) e hb Av
 have eq₁(a:Cord S'): region (X:=P₂) i (Stilo.beamH C.val) f F₂ θ Av a=eP^tokenFuel i a • g' a:=
    Z.ratio_master i (Stilo.beamH C.val) e a Av hb θ F₂ rfl rfl
 have eq₂: region i (Stilo.beamH C.val) f F₂ θ Av= Z.tiny i (Stilo.beamH C.val) e hb Av:=
    funext fun a=> (eq₁ a).trans (Z.ratio_master i (Stilo.beamH C.val) e a Av hb T' F₂ rfl rfl).symm
 constructor
 · have he':∀ᵐ z∂plummy S' u₁,‖g' z‖≤ Bc:= (h i C Av u hA).1.mono fun z v=> v.trans (qB C)
   have ht:= (plumAC (w:=w) (V:=V) hy hx).ae_le
   refine (he'.filter_mono ht).mono fun a v=>?_ -- ae binder in target
   change ‖region _ (Stilo.beamH C.val) f F₂ θ Av a‖≤_
   rw [eq₁,norm_smul]
   exact (mul_le_mul (ha _ a) v (norm_nonneg _) cA.le).trans (pv C)
 change Integrable (region _ _ f F₂ θ Av) (plummy S' b₂)
 rw [eq₂]
 exact Engine.Basin.keep_live C i Z e M hv _ (by rw [Palot.bay_beam]; exact hA)
end Cellar
end Pitching
end YM.CF.Py.Rate

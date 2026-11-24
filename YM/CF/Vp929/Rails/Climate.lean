import YM.CF.Vp929.Rails.Lure
import YM.CF.Vp929.Rails.Headroom
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
local notation "F₁"=> Folk S' z' (Words S')
local notation "V_"=> Troupe S' z' (Words S')
local notation "Xo" => Hos S' z'
local notation "Θ"=> vast (k:=D.Z.N1*radiusB x) o.muster
open Lich Iva
variable {F:Corr (Scree.mid n B)}
variable {Pν: ↥(Sil (w.step V) (coming D.Z 105 5*radiusB x))}{N0:ℕ}
local notation "Δ"=> (o.muster.post+90)*radiusB x
local notation "Ξ"=> (o.muster.loft+o.muster.post+200)*radiusB x
local notation "D'"=> Dwell ι
local notation "Xp"=> (stake (n:=LeanV (Tulip.Single (Scree.mid m B))) h)
local notation "FX"=> F₁→Raid (Dwell (Scree.mid m B))
-- numeric ledger. λ spacing & Knot closeness. tail normalized difference gain σ.
open Appel.Rate Plume.Rate Lid Dialect
local notation "Pμ" i => VolumeRate.panel i
structure Framing (n:ℕ)(C:ℝ) : Prop where
 big : 2^(6+2)*2 ≤ n
 positive : 1≤ C
 stipend : Appears n C
-- everything depending on a patch, regulator threshold independent of a geometry.
abbrev desire (R:Patch)(P:Pilot)(ag Cg x:ℝ): ℝ:= Real.exp (-ag*(P.hat R x /4)^2)*Cg
structure Climate (P:Pilot)(R:Patch)(c:Estimate)(x t b σ κ ag Cg Bv:ℝ)(n:ℕ): Prop where
 weather : Framing n Bv
 patron : Patron ag Cg
 purse : 0<κ
 margin : 4≤ P.hat R x
 lane : 0<t
 payment : Footprint.payment 1 (6*(radiusB x+1)) 0 (1/4) 1 (Bv*((VolumeRate.panel n).card*c.Pc x)) ((23/4)+1) 0 ≤ κ
 step : degreePrice (radiusB x) κ 1 ≤ 1/2
 speed : 5*radiusB (x+billX R.L) +4≤10*radiusB x
 rho : 0≤b∧ b≤1/2
 -- sufficient if |z-β| ≤ (widthS n+3)*t. express inequalities centers per Y.
 warm : (((widthS n+3):ℝ)*t/Scales.y SU.group R.L x) ≤ ag/2
 dew : (((widthS n+3):ℝ)*t/Scales.y SU.group R.L x)*(2/ag)*Cg ≤ b
 mist : desire R P ag Cg x ≤ b
 vigor : ((wasteful R (radiusB x)):ℝ)*(4*b) ≤ 1/8
 pulse : 0<σ
 unit : σ≤1
 snow : (1+(wasteful R (radiusB x)):ℝ)*desire R P ag Cg x ≤ σ^2/1024
variable {nₐ:ℕ} (H:Lid o p p' f) {t b σ κ Bv:ℝ}
local notation "Rstar"=> wasteful R (radiusB x)
variable (M: Climate D.pilot R c x t b σ κ ag Cg Bv nₐ)
include H M
local notation "℘"=> D.pilot.hat R x
lemma farW (hv:β∈Year R x): ℘/4≤ (H.ZoomB hv).hat R x:= by
 rw [H.hat']; have ht:℘/2>0:= H.park; have hx:1/2≤ Cay.rune β y:= by nlinarith [(H.rune_enroll hv).1,H.scaling_p hv]
 linarith only [mul_le_mul_of_nonneg_right hx ht.le]
lemma coast (hv:β∈Year R x): 1≤(H.ZoomB hv).hat R x:= (le_trans (by linarith only [M.margin] : (1:ℝ) ≤ ℘/4) (farW H M hv))
local notation "Jr" z:max=> jug SU.group (℘/2) z
local notation "Sp" z:max=> (shotM o.muster.vita ℘ z:ℂ)
local notation "θ"=> Cay.rune β y
variable {z:ℂ}
lemma ripe_p (hv:β∈Year R x)(h:‖z-β‖ ≤ ((widthS nₐ+3):ℝ)*t):
  Jr (z/y)≠0 ∧ ‖Jr (z/y)‖/‖Jr ((β:ℂ)/y)‖ ≤ Real.exp b ∧ ‖Jr ((β:ℂ)/y)‖/‖Jr (z/y)‖≤ Real.exp (2*b):= by
 rw [←Complex.ofReal_div,← rune_s (H.pos hv) H.night]; apply M.patron.tilt M.rho.1 M.rho.2 (H.rune_enroll hv).1 (H.scaling_p hv) H.park (by rw [← H.hat']; exact coast H M hv)
 all_goals rw [rune_s (H.pos hv) H.night,Complex.ofReal_div,←sub_div,norm_div, Complex.norm_real, Real.norm_of_nonneg H.night.le]; have hh:= div_le_div_of_nonneg_right h H.night.le
 · exact hh.trans M.warm
 · have ht:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (div_nonneg (by norm_num : (0:ℝ) ≤ 2) M.patron.pos.le)) (zero_le_one.trans M.patron.earns); exact ht.trans M.dew
lemma tailG (hv:β∈Year R x): Real.exp (-ag*((H.ZoomB hv).hat R x)^2)*Cg≤ desire R P' ag Cg x:= by
 refine mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonpos_left (pow_le_pow_left₀ (by linarith only [M.margin]) (farW H M hv) _) (neg_nonpos.mpr M.patron.pos.le))) (zero_le_one.trans M.patron.earns)
lemma frosted (hv:β∈Year R x): Appel.point SU.group ℘/ Appel.point SU.group ((H.ZoomB hv).hat R x) ≤ Real.exp (2*desire R P' ag Cg x):=
 M.patron.toll (zero_lt_one.trans_le (coast H M hv)) (by linarith only [M.margin]) (Pilot.hat_zoom ..) (tailG H M hv) (M.mist.trans M.rho.2)
lemma shot_orientation (hv:β∈Year R x) : shotM o.muster.vita ℘ β/ H.intensity hv= Appel.point G5 ℘ / Appel.point G5 ((H.ZoomB hv).hat R x):= by
 have hp := H.intensity_pos hv; apply mul_div_mul_left; apply left_ne_zero_of_mul; exact hp.ne'
lemma rip (hv:β∈Year R x)(h:‖z-β‖ ≤ ((widthS nₐ+3):ℝ)*t) : latticeFieldEstimatesB o z≠0 ∧ ‖Sp β‖/‖latticeFieldEstimatesB o z‖ ≤ Real.exp (4*b):= by
 obtain ⟨Y,U,P⟩:=ripe_p H M hv h
 let T:= latticeFieldEstimatesB o z; let u0:ℂ:=shotM o.muster.vita (℘/2) y
 have he: u0 ≠0:= by intro h; apply (Complex.ofReal_ne_zero.mpr (H.intensity_pos hv).ne'); rw [←H.latticeFieldEstimates_real]; change u0 * _=0; rw [h,zero_mul]
 have ht:T≠0:=mul_ne_zero he Y
 refine ⟨ht,?_⟩; calc
   _ = (‖Sp β‖/ ‖latticeFieldEstimatesB o (β:ℂ)‖)*(‖latticeFieldEstimatesB o (β:ℂ)‖/‖T‖) := by have hp:latticeFieldEstimatesB o (β:ℂ)≠0:= H.latticeFieldEstimates_real hv ▸ Complex.ofReal_ne_zero.mpr (H.intensity_pos hv).ne'; unfold T; field_simp [(norm_pos_iff.mpr hp).ne',show ‖latticeFieldEstimatesB o z‖≠0 from (norm_pos_iff.mpr ht).ne']
   _ ≤ Real.exp (2*b)*Real.exp (2*b) := by
      apply mul_le_mul _ _ (div_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.exp_pos _).le
      · rw [Complex.norm_real, Real.norm_of_nonneg (H.shot_p hv _ (H.crew β hv).1).le, H.latticeFieldEstimates_real hv,Complex.norm_real, Real.norm_of_nonneg (H.intensity_pos hv).le, shot_orientation H M hv]; exact (frosted H M hv).trans (Real.exp_monotone (by linarith only [M.mist]))
      calc
       _= ‖Jr ((β:ℂ)/y)‖/‖Jr (z/y)‖ := by
        change ‖u0*_‖/‖u0*_‖=_; simp only [norm_mul]; rw [mul_div_mul_left _ _ (norm_pos_iff.mpr he).ne']
       _≤_ := P
   _=_:= by rw [←Real.exp_add]; ring_nf
lemma ink_m (Aq:Dialect o p' f F Pν) (i:F₁)(S:Cord S')(hv:β∈Year R x)(h:‖z-β‖ ≤ ((widthS nₐ+3):ℝ)*t): ‖(latticeFieldEstimatesB o z)⁻¹^born (x:=x) S i‖* ‖(Sp β)^born (x:=x) S i‖ ≤ Aq.extra (1/8) i:= by
 have u:= rip H M hv h; let K':= born (x:=x) S i; let Dcut:= coverNumber (radiusB x) (Aq.req i).val
 rw [norm_pow,norm_pow,←mul_pow,norm_inv,mul_comm ‖latticeFieldEstimatesB o z‖⁻¹,←div_eq_mul_inv]; apply le_trans (pow_le_pow_left₀ (by positivity) u.2 _); rw [←Real.exp_nat_mul]; apply Real.exp_monotone; have he:=Aq.clearance (H.crew β hv).1 S i; have hp:=M.rho; have ht:= mul_le_mul_of_nonneg_left M.vigor (show (0:ℝ)≤ Dcut from Nat.cast_nonneg _); have hq:= Nat.cast_le (α:=ℝ).mpr he; rw [Nat.cast_mul] at hq; apply le_trans (mul_le_mul_of_nonneg_right hq (by linarith [M.rho.1])); unfold Dcut at ht; nlinarith only [ht]
end Pitching
end YM.CF.Py.Rate

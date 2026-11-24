import YM.CF.Vp929.Rails.Climate
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
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
open Appel.Rate Plume.Rate Cellar Lid Lilt
local notation "WQ"=> F₁
local notation "μ"=> coverNumber (radiusB x)
local notation "W'"=> wasteful R (radiusB x)
local notation "℘"=> D.pilot.hat R x
local notation "bκ"=> (Wray.boT R 5 105 c.blips (ag/32) Cg x)
variable (Z: Cellar N0 o p p' c f ag Cg) (Q:β∈ Year R x)
variable {t b σ κ Bv:ℝ}{nₐ:ℕ}
variable (Lx:Support (Domain m B))(M:Climate D.pilot R c x t b σ κ ag Cg Bv nₐ)
include M
local notation "Trop"=> desire R P' ag Cg x
lemma cashL : (wasteful R (radiusB x):ℝ)*desire R P' ag Cg x ≤ σ^2/1024 := by refine le_trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (show 0≤Trop from mul_nonneg (Real.exp_pos _).le (zero_le_one.trans M.patron.earns))) M.snow
include Z Q
local notation "θ"=> Cay.rune β y
local notation "Ustar"=> (Z.toLid.ZoomB Q).hat R x
local notation "Γ"=> (booths Lx S')
local notation "pinv"=> (Appel.point SU.group ℘ / Appel.point SU.group Ustar)
lemma peg_cost : pinv ≤ Real.exp (2*Trop) ∧ 1≤pinv:= by
 have ht:=zero_lt_one.trans_le (coast Z.toLid M Q); exact ⟨frosted Z.toLid M Q,(one_le_div (point_p ht)).2 (point_mono (Pilot.hat_zoom ..))⟩
variable (K0:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V)))
local notation "L'"=> K0.toRight.toRight.toLeft
local notation "S₀"=> Cord S'
local notation "B₀"=> Trees.currency (radiusB x) (1/2) Lx
local notation "yp"=> ((booths Lx S').card*(Real.exp (-ag*(Ustar)^2)*Cg))
lemma avoidance : (booths Lx S').card*(Real.exp (-ag*(Ustar)^2)*Cg) ≤ (σ*B₀)^2:=by
 have hh := headroom_b Lx (Z.toLid.crew _ Q).1; have ht:=Nat.cast_le (α:=ℝ).mpr hh; rw [Nat.cast_mul] at ht; have hs:=zero_le_one.trans M.patron.earns; calc
   _ ≤ ((wasteful R (radiusB x):ℝ)*μ Lx)* Trop := mul_le_mul ht (tailG Z.toLid M Q) (mul_nonneg (Real.exp_pos _).le hs) (by positivity)
   _ ≤ _ := by
     have h:= mul_le_mul_of_nonneg_right (cashL M) (show (0:ℝ)≤ μ Lx from Nat.cast_nonneg _); have hu:1≤ Real.exp (1/2*μ Lx):=Real.one_le_exp (by positivity); have he:=Real.add_one_le_exp ((1/2:ℝ)* μ Lx); have hx : ((μ Lx:ℝ)/1024)≤(Real.exp ((1/2:ℝ)* μ Lx))^2:=by nlinarith [Nat.cast_nonneg (α:=ℝ) (μ Lx)]
     unfold Trees.currency; rw [mul_pow]; nlinarith only [mul_le_mul_of_nonneg_left hx (pow_two_nonneg σ),h]
omit M
abbrev pivotV (S:S₀):ℝ:= pinv^((Γ).card + tokenFuel K0 S)
include M
variable (Aq:Dialect o p' f F Pν) (T':Plume.Cord (w.step V))
lemma rock_v : 0≤ pivotV Z Q Lx K0 T' - 1:= sub_nonneg.mpr (one_le_pow₀ (peg_cost Z Q M).2)
lemma drift_v : pivotV Z Q Lx K0 T'-1 ≤ σ* B₀* Aq.prize K0 (1/8):=by
 have ht:=peg_cost Z Q M; let d:=μ Lx; let v:ℕ:= ∑ i∈K0,μ (Aq.req i).val; let y':= ((booths Lx S').card + tokenFuel K0 T'); let R0:= Trees.currency (radiusB x) (1/2) Lx; have e:y' ≤ wasteful R (radiusB x)*(d+v):=by rw [mul_add]; exact Nat.add_le_add (headroom_b Lx (Z.toLid.crew _ Q).1) (Aq.headroom (Z.toLid.crew _ Q).1 _ _)
 let U':= (1:ℝ)/2*d+1/8*v
 have we : (y':ℝ)*(2*Trop) ≤ σ*U':= by
   have hx:= mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr e) (show 0 ≤2*Trop from by have he:= M.patron.earns; unfold desire; positivity); apply le_trans hx; rw [Nat.cast_mul,Nat.cast_add]; have hu:=mul_le_mul_of_nonneg_right (cashL M) (show 0 ≤ (((d+v):ℕ):ℝ) by positivity); rw [Nat.cast_add] at hu; have hr: σ^2≤σ:= by nlinarith [M.pulse,M.unit]
   unfold U'; nlinarith only [hu,mul_le_mul_of_nonneg_right hr (show 0≤(d:ℝ)+(v:ℝ) by positivity),mul_nonneg M.pulse.le (Nat.cast_nonneg (α:=ℝ) d),mul_nonneg M.pulse.le (Nat.cast_nonneg (α:=ℝ) v)]
 have θs:pivotV Z Q Lx K0 T' ≤ Real.exp (σ*U'):=le_trans (show pinv^y'≤Real.exp (2*Trop)^y' from pow_le_pow_left₀ (zero_le_one.trans ht.2) ht.1 _) ((Real.exp_nat_mul ..).ge.trans (Real.exp_monotone we))
 have hx:=convexOn_exp.2 (Set.mem_univ U') (Set.mem_univ 0) M.pulse.le (sub_nonneg.mpr M.unit) (show σ + (1-σ)=1 from by ring); simp only [smul_eq_mul,mul_zero,add_zero, Real.exp_zero,mul_one] at hx; have P:Real.exp U' = B₀*Aq.prize K0 (1/8):=by unfold U'; rw [Aq.prize_formula,Real.exp_add]; unfold v; push_cast; rfl
 rw [mul_assoc,←P]; linarith only [hx,θs,M.pulse]
lemma poor (t:Sil (w.step V) (coming D.Z 105 5*radiusB x)): (plummy S' ℘).real ((worldL o t ∩ earnS o c K0) ∩ {x|¬textP Lx x Ustar}) ≤ (depot η).real (fairTags t) * (bκ^(L').card * (σ*B₀)):= by
 have h:= coast Z.toLid M Q; exact cut_r (u:=Ustar) K0 M.patron (Z.toLid.crew _ Q).1 Lx (by linarith [M.margin]) (by linarith) (mul_nonneg M.pulse.le (Real.exp_pos _).le) (avoidance Z Q Lx M) _
end Pitching
end YM.CF.Py.Rate

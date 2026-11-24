import GaugeFieldConstruction.Flurry
import GaugeFieldConstruction.Regulator
import SatinThinPlaza

/-! # Step contexts stay on that funded prediction, even when changing authorized Bet input -/
set_option autoImplicit false
set_option autoImplicit false
set_option quotPrecheck false
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
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

namespace Preparation
open FullBill Window Marks
open Pitching Focus QuadClock
variable {P:Preparation}{F:(s:Side)→Scree.Loom s→Prop}(Y:Course P F)
local notation "tape" i:max=> (Y.voyage i)
local notation "Coord" i:max k:max=> (tape i).X (Y.uv k)
variable {Pay ξC Γϕ:ℝ}{n u:ℕ}{Tξ:Hove.Grant P.K.j 2}

abbrev SupplyTrust (i k:ℕ):= Actual Y.meter (Y.voyage i).funds (Y.voyage i).CapeT (gaugeFreq P (Y.tile*P.M)) (Y.uv k)
abbrev PlaceOf (i k s:ℕ):= (SupplyTrust Y i k).toSpine.address s
lemma flag_fine {A C' ρ:ℝ}{D:Treaty P.J Chi.canonical A C' Pay P.h ρ}{Nheat:ℕ}{fog:ℝ→ℝ}(H:Halen D Nheat fog P.N0 ξC Γϕ Tξ n P.P)
 (flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay):
  ∃ (c:Estimate)(pW:WindV P.K.j 2)(g₁ g₀:ℝ→ℝ)(ag Cg Bv hℓ:ℝ)(Dα:ℝ→ℝ)(n₁:ℕ),
  OutlookC D c g₁ g₀ pW ag Cg Bv n₁ ξC hℓ Dα HI Nheat fog ∧
   ∃ (a b1 b2 Wk:ℝ)(Z W V1 Kp γx:ℝ→ℝ), BladeQ P.R Z W V1 Kp ∧ Chill_v γx ∧ ∃ kP:Pinewood P.R,
  -- No height/cutoff filters inside this quantifier. Dockets are inherited at **all later heights**
    ∀ᶠ s in atTop,∀ i k:ℕ,s< Y.uv k→
    let v:=Y.meter.a s; let v':=Y.meter.a (s+1); let w:= PlaceOf Y i k s; let x:= YM.CF.Vale.hat P.R.L P.x s
    w.Request P.V P.U P.W P.J Chi.canonical P.N0 x v v' ∧
    ∃ (β:ℝ)(F:Corr (P.Ctor (Y.ir i) (s+1)))(u:ℂ), enters (x+Vale.billX P.R.L) (β:ℂ) ∧
    Charged v' w.input P.K.j P.R.L.val P.h (3*dleaf P.R.L x) F ∧
     let O:= P.P _ _ w x v v';
     located D c ag Cg Bv (g₁ x) (g₀ x) Nheat (fog x) ξC hℓ (Dα x) P.N0 n₁ (wrc P.R Wk Pay pW.C P.h x) (V1 x) (Kp x) (Z x) (W x) (γx x) Γϕ n Tξ pW a b1 b2 kP w x v v' O ∧
          (RootBook Y i k s)=O.output P.V w v β F u ∧
          (RootBook Y i k (s+1))=w.buildIn P.V v' β F u ∧
          (Coord i k).wave s = O.wave β F:=by
 obtain ⟨c,pW,X,F,ag,Cg,Bv,hℓ,Dα,n₁,h,a,b1,b2,Wk,Z,W,V1,Kp,γx,e,hx,kP,w⟩:=H.coverage
 refine ⟨c,pW,X,F,ag,Cg,Bv,hℓ,Dα,n₁,h,a,b1,b2,Wk,Z,W,V1,Kp,γx,e,hx,kP,?_⟩
 filter_upwards [(turnover P).eventually w] with s u i k hi p p' K x
 let ρ:= SupplyTrust Y i k
 obtain ⟨pA,b,hb,g⟩:= flag i (Y.uv k)
 have hk:=hb.toRealQ; let Zq:= ρ; have hh:ρ.active P.P b s=ρ.gram P.P b s:= pA.success P.H hk s hi (pA.paysStep P.H hb s hi)
 have hv:= pA.request s hi
 refine ⟨hv,(b.read (s+1)).re,(ρ.chargeLevel P.P b (s+1)),ρ.offset P.P b (s+1),hat_step s ▸ (pA.beta_ok P.H hk _ hi).2, pA.flow (pA.charged P.H hk _ hi),u _ _ _ _ _ hv,?_⟩
 unfold RootBook; rw [g.gramZ,g.waveZ,← hh,ρ.gram_fine P.P b s hi]; exact ⟨rfl,rfl,rfl⟩

-- Certify Haven at every one such height by ratio leverage (including top used in X3). In following version any polynomial in b.
lemma pane_fills (Q l m:ℕ): ∀ᶠ s in atTop,∀ i,
 Q*(radiusB (hat P.R.L P.x s))^l+m < (More (P.Ctor (Y.ir i) s)).val:=by
 let a:ℝ:=P.R.L.val
 let x:=P.x
 let Z:=hat P.R.L P.x
 have hp:a>1:=by unfold a; exact_mod_cast (show 1<P.R.L.val by have ht:=P.R.coarse; omega)
 have hk:Tendsto (fun i:ℕ=> Z i / a^i) atTop (𝓝 0):=by
    have h₀:Tendsto (fun n:ℕ=> P.x/a^n) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hp)
    have h₁:Tendsto (fun n:ℕ=> (n:ℝ)/a^n) atTop (𝓝 0):=by
       have v:=tendsto_pow_const_mul_const_pow_of_lt_one 1 (inv_nonneg.mpr (zero_lt_one.trans hp).le) ((inv_lt_one₀ (zero_lt_one.trans hp)).2 hp)
       simpa [inv_pow,div_eq_mul_inv] using v
    simpa [Z,hat,div_eq_mul_inv,add_mul,mul_right_comm _ (Vale.billX P.R.L)] using (h₀.add (h₁.mul_const (Vale.billX P.R.L)))
 let u:= YM.Work.E09.radiusB_small 1 one_pos l
 have hF:Tendsto (fun i:ℕ=> (Q:ℝ)*(Z i /a^i)+(m:ℝ)/a^i) atTop (𝓝 0):=by
   have hx:Tendsto (fun i:ℕ=>(m:ℝ)/a^i) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hp)
   simpa only [mul_zero, add_zero] using (hk.const_mul (Q:ℝ)).add hx
 filter_upwards [hF.eventually (gt_mem_nhds zero_lt_one),(turnover P).eventually (u.bound zero_lt_one),(turnover P).eventually_gt_atTop 0] with s t v ht i
 let X:= radiusB (Z s); have hq:(X:ℝ)^l ≤ Z s:=by
   change ‖(X:ℝ)^l‖≤1*‖Z s^(1:ℝ)‖ at v; simpa [Real.norm_of_nonneg (show 0≤(X:ℝ)^l by positivity), Real.norm_of_nonneg (show 0≤ Z s from ht.le)] using v
 have ha:0<a:=zero_lt_one.trans hp
 rw [← mul_div_assoc,← add_div,div_lt_one (pow_pos ha s)] at t
 have hP: Q*X^l+m < P.R.L.val ^ s:=by
   have hh:(Q:ℝ)*(X:ℝ)^l + m < (P.R.L.val:ℝ)^s:=lt_of_le_of_lt (add_le_add (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)) le_rfl) t
   exact_mod_cast hh
 let N:=Vale.mesh (Y.ir i) P.R.L s
 have hh:N.val ≤ (More (cell (Y.ir i) P.block P.R.L s)).val:= (Nat.le_mul_of_pos_right (N.val) Nat.zero_lt_two|>.trans (Nat.le_mul_of_pos_right _ P.block.property))|>.trans (Nat.le_mul_of_pos_right _ Nat.zero_lt_two)
 exact hP.trans_le ((Nat.le_mul_of_pos_left (P.R.L.val^s) (Y.ir i).property).trans hh)

lemma step_houses : ∀ᶠ s in atTop,∀ i,
 HavenL (P.Ctor (Y.ir i) s) (Y.meter.a s) P.R.L.val:=by
 let Z:= P.R.L.val
 filter_upwards [pane_fills Y (40*Z+20) 1 (4+20*Z), (turnover P).eventually (Work.E01.radiusB_tendsto.eventually_ge_atTop 10)] with s w q i
 have hp: (Y.meter.a s).B= radiusB (hat P.R.L P.x s):=(Y.meter.boot _).2.1 -- fix
 apply regularRooms
 · have h:=w i; omega
 · exact lt_of_lt_of_le (by decide : 1<3) P.R.coarse
 · rw [hp]; exact q
 let d:= radiusB (hat P.R.L P.x s)
 have h: (40*Z+20)*d + (4 + 20*Z) < (More (P.Ctor (Y.ir i) s)).val:=by simpa only [pow_one] using w i
 rw [hp]; change 10*(Z*(4*d+2)+2*d) < _; ring_nf at h ⊢; omega
end Preparation
end LocalLimit
end YM.CF.Py.Rate
end

import Anomaly.Separate.Pumps
import Anomaly.Basis.Helion
import Anomaly.Ward.Block
/-! Critique for housing at 130. Accept sold Spinner ANY.
 -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
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
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell Porticus QuadClock Ione.Clock Moto Neon Taxi Lor
open Oise Buffered
variable {a b c v d s f x y w h:ℝ}{k r:ℕ}{P':BudgetPoint}
open Pitching Focus
namespace LocalLimit
namespace Preparation
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) (Γ:ℝ) (Γ0:Taxi.DayT 6 Γ) (g0:0≤Γ)
-- check binder names
variable {ζ κ c' φ a' M F:ℝ}
variable {i m j:ℕ}
local notation "W"=> RootBook Y i k m
local notation "TΘ"=> (W).p
local notation "C_"=> P.Ctor (Y.ir i) m
local notation "U"=> (Y.voyage i).CapeT m
local notation "Ω"=> hat P.R.L P.x m
local notation "Q_"=> pinpr P.R.L Ω
local notation "o★"=> (0:Site C_)
open Sonar Next.Rank.Spindle
variable (u:m<Y.uv k) {J T : Axis→ SOp (P.Ctor (Y.ir i) m)} {A Z: SOp (P.Ctor (Y.ir i) m)} (Kz: CartPins Y i k m j a b x y J T A Z)
local notation "ψΛ"=> (((W).p).B/10)
variable (h0:0< a) (θ:Rules SU.group) {QV:tableQ SU.group (More (P.Ctor (Y.ir i) m)) ℂ}
   (L: mintQ κ c P.d (RootBook Y i k m).p.order) (L':Knit A (node (0:Site (P.Ctor (Y.ir i) m))) ((RootBook Y i k m).p.B/10) P.d κ b c w (RootBook Y i k m).p.order QV)(Γp:FlowPrice ζ φ (RootBook Y i k m).p.order)
   (hs: Real.exp (-a*(↑(((RootBook Y i k m).p.B/10):ℕ):ℝ)) ≤ (RootBook Y i k m).p.threshold^2)
   (e:2*(((RootBook Y i k m).p.B/10)+1)<(More (P.Ctor (Y.ir i) m)).val)(Qt:4*(↑(((RootBook Y i k m).p.B/10):ℕ):ℝ)*(RootBook Y i k m).p.threshold ≤ θ.c) (b':0<b)
local notation "Y★"=> ((8* (↑ψΛ:ℝ)+1)*(W).p.threshold)
local notation "D" x:max=> Pressure.radiusB x /10
local notation "Mφ"=> gaugeMark (W).p U o★ A
local notation "zν"=> Q_ / (temp Ω)^2
local notation "Λσ"=> stockRate TΘ
abbrev stale_A (b f c:ℝ) (x:ℝ):ℝ:= (7:ℝ)*(Jet.composeCost 6 (2*(2*c*b)*(f*(8*(↑(D x):ℝ)+1))^2) 1+b)
-- size on window by maskScale (not charged). For Poncho
abbrev stale_t (b c:ℝ)(x:ℝ):ℝ:= b+ (8*c*b)*(8* (↑(D x):ℝ))^2
lemma bound_t (b f c:ℝ): BoreP (stale_t b c) ∧ BoreP (stale_A b f c):=by
 unfold stale_t stale_A Jet.composeCost; refine ⟨(BoreP.still _).join ((BoreP.still _).grip (((BoreP.still _).grip rookK).self _)),?_⟩
 exact (BoreP.still _).grip ((( (BoreP.still _).grip ((BoreP.still _).grip (((BoreP.still _).grip (((BoreP.still _).grip rookK).join (BoreP.still _))).self _))).grip (BoreP.still _)).join (BoreP.still _)) -- parentheses!
include u h0 L L' Γp hs e Qt θ Kz b'
lemma fromGauge (z:0≤pinpr P.R.L Ω)(p0:Y★≤ ζ)(p1: φ* Y★<κ)(hq:Y★<κ):∃ X: Bag C_, Hold P.U W U P.J.n 24 (node o★) P.h Λσ ((↑(zν):ℂ) • tracePhys U TΘ o★ A) X (Q_*cashPoncho (stale_A b φ c Ω) 32 24) (Q_*cashPoncho (stale_A b φ c Ω) 32 24) ∧ WindowTag ((↑(zν):ℂ) • Mφ) o★ ((TΘ).B+12) (Q_*stale_t b c Ω) ∧ Contact U (offsetMask ((TΘ).B+12) o★) ((↑(zν):ℂ) • Mφ) ((↑(zν):ℂ) • tracePhys U TΘ o★ A):=by
 let X:= W; let B:=X.p; let C:=C_; let τ:=B.threshold; have ht:0<τ:=B.threshold_pos
 obtain ⟨u1,u2,u3,u4,u5⟩:=p_meters Y i k m u
 let F:=Kz.ropes.tubes.capX; let E:=Kz.pulse
 have hw:B.threshold=temp Ω:=u2; have hv:0 ≤ zν:=div_nonneg z (sq_nonneg _)
 have hh:‖rawQ A 1‖≤τ^2*b:=(show _ from identityPrice Kz h0.le).trans (mul_le_mul_of_nonneg_right hs b'.le)
 have hc:=L.2.2.1
 let D':ℝ:= traceB_cost X.p φ (2*c*b) ψΛ ‖rawQ A 1‖
 have hvD: 0≤D':=by unfold D' traceB_cost Jet.composeCost; dsimp only; positivity
 have ht0:ψΛ= Pressure.radiusB Ω/10:=congrArg (fun x:ℕ=>x/10) u1
 have hb:B.threshold=(W).p.threshold:=rfl -- tune notation
 have hv0:D'≤ τ^2*stale_A b φ c Ω:=by
    let F(q:ℝ):= traceB_cost X.p φ (2*c*b) ψΛ q
    refine le_trans (b:=F (τ^2*b)) ?_ ?_; · unfold D' F traceB_cost; dsimp only; exact mul_le_mul_of_nonneg_left (add_le_add_right hh _) (by positivity)
    unfold F traceB_cost Jet.composeCost; dsimp only; unfold stale_A Jet.composeCost; rw [← ht0]; -- rearrange
    rw [show X.p.order=6 from u3]; change (↑(6:ℕ)+1)* (_*(2*(2*c*b)*(φ*((8*(↑ψΛ:ℝ)+1)*τ))^2)*_+ _) ≤ _ -- typo replace
    apply Eq.le; ring -- tune
 have hs:0≤ Λσ:=by unfold stockRate; positivity
 have hd : Λσ≤32:=by
    have he:1≤(B.B:ℝ):=Nat.one_le_cast.mpr B.B_pos; have hp:=inv_le_one_of_one_le₀ he; unfold stockRate; rw [show (W).p.supportExponent=1 from u5,div_eq_mul_inv]; change (1:ℝ)+8*(B.B:ℝ)⁻¹+(B.B:ℝ)⁻¹+(B.B:ℝ)⁻¹≤_; linarith only [hp]
 have hg: ‖(↑(zν):ℂ)‖= Q_/τ^2:=by rw [Complex.norm_real,Real.norm_of_nonneg hv]; unfold τ; rw [hw]
 have hy: ‖(↑(zν):ℂ)‖* cashPoncho D' Λσ 24 ≤ Q_*cashPoncho (stale_A b φ c Ω) 32 24:=by
    rw [hg]; unfold cashPoncho; refine le_trans (mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _))) hvD) (mul_le_mul_of_nonneg_right hv0 (Real.exp_pos _).le)) (div_nonneg z (sq_nonneg _))) (le_of_eq (by field_simp)) -- tune needs ring
 let hO:= scalarHold (m:=P.h) P.U W U Kz.pulse.roof F L' L Γp θ e Qt P.dpos Kz.capR E.reach p0 p1 hs h0.le
 have h0': Hold P.U W U P.J.n 24 (node o★) P.h Λσ _ _ _ _:= scale_hold P.U W U (m:=P.h) hO (↑(zν):ℂ)
 let G:= gaugeWindow o★ E.roof P.dpos F E.reach Kz.capR h0.le
 have hq: WindowTag Mφ o★ ((W).p.B+12) (τ^2*stale_t b c Ω):=by
    refine {G with price:=?_}
    intro x; unfold gaugeMark; rw [norm_smul,norm_one,mul_one]; have hz:=Sonar.maskScale L' L E.roof Kz.capR E.reach x.1 θ ((by decide: 3≤6)|>.trans ((W).p.order_ge)) Qt e ?_
    · refine hz.trans ((add_le_add_left hh _).trans_eq ?_); unfold maskBudget stale_t; rw [←ht0]; unfold τ; dsimp only [B,X]; ring
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith) ht.le) hq
 have hT: Contact U (offsetMask ((W).p.B+12) o★) Mφ (tracePhys U (W).p o★ A):=⟨G.ticket,fun _=> Fock.Sector.one.scale _,fun _=>rfl⟩
 refine ⟨_,rise_hold _ _ _ h0' hy hy,?_,hT.scale _⟩
 let v':=hq.scale (↑(zν):ℂ); rw [hg] at v'; rw [show Q_/τ^2 * (τ^2*stale_t b c Ω)=Q_*stale_t b c Ω from by field_simp] at v' -- tune
 exact v'
end Preparation
end LocalLimit
end YM.CF.Py.Rate

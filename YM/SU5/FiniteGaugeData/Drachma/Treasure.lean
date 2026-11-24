import YM.SU5.FiniteGaugeData.Drachma.Compound
import YM.SU5.FiniteGaugeData.Steam.Kettle
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
namespace Pitching.Focus
open Haro
abbrev ChamberOilΨ (J:Robes N V W)(h:ℝ) (N₀:ℕ) (q: Chi): Prop:= ∀ k:ℝ, 0 < k → ∀ᶠ x in atTop,∀ (m n:Side)(Y:Location (R:=R) B m n)(p p':BudgetPoint), Location.Request V U W J q Y N₀ x p p' → ∃ δ C r:ℝ, ∃ t:Nonempty (Haro.ΘS r), letI:=t; ∃ S:Shop Y J p p' q h x r, Shop.Ready δ C S ∧ Capsule R x ∧ ScandereΨ k S.operate x h Y J p'

open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt Vow Ione Beau
open Test TestW QuiltB
variable {pW:WindV K.j 2}{b0 b1 b2 b3 Aχ Γχ Wk:ℝ}{n₀:ℕ}(s:Major V Wk b0 b1 b2 b3 Aχ Γχ n₀)
variable (l:lobe (2*catap Wk) h (γ₀ HI b0 (Tenant.quota^2*b1) (Tenant.quota^2*b2) 0 h) HI)(hO:J.roomX ≤ b3)(px:FitB R.L.val K s.k Aχ Γχ Pay pW.C Wk)
include D s l hO px
open Sour
lemma chamber_supplyΨ : ∃ N0, ChamberOilΨ J h N0 q:=by
 obtain ⟨a,b,n,x,g,v⟩:= Frame_exists
 obtain ⟨c,p,χπ,u,_⟩:= Weather.focus_exists (D:=D) v g pW 0
 let N0:= D.size+200+(n₀+1)+Test.perimeter R.L.val
 let δ(i:ℝ):= |χPost K R Pay pW.C Wk Aχ Γχ i|; have hP:Chill_v δ:=χ_tame s.k s
 refine ⟨N0,?_⟩; intro k h1; have ht:=globalSteamΨ s u l hO px k h1
 filter_upwards [ht,prolong (V:=V) hP (Eventually.of_forall fun _=> abs_nonneg _)] with j u v; intro m n Y p p' e; obtain ⟨d,c,hV,T⟩:= u N0 le_rfl; letI:=hV; obtain ⟨S,z,o⟩:=T m n Y p p' e
 exact ⟨d,c,wrc R Wk Pay pW.C h j,hV,S,z,v,o⟩
omit D s l hO px
/-- Any operator with the needed enrollment hops receives this better price, not just receipt-paying from this Chamber! -/
def KettleΨ (J:Robes N V W)(P:Prescription R B)(N0:ℕ)(h:ℝ)(q:Chi):Prop:= ∀ k:ℝ, 0<k→ ∀ᶠ x in atTop,∀ (m n:Side)(Y:Location (R:=R) B m n)(p p':BudgetPoint), Location.Request V U W J q Y N0 x p p' → ∀ (β:ℝ)(G:Corr (mid n B))(v:ℂ), enters (x+billX R.L) β → Charged p' Y.input K.j R.L.val h (3*dleaf R.L x) G → rentD V Y k β ≤ ((P m n Y x p p').offset β G v).re-v.re
private lemma room_drop {k j:ℕ} (pA:k≤ j)(u:Location.Request V U W J q w j x p p'):Location.Request V U W J q w k x p p' := { u with size := (Nat.mul_le_mul_right (radiusB x) pA).trans u.size }
lemma keepsΨ {aH:ℝ}{P: Prescription R B}{k j:ℕ}{X Y C:ℝ→ℝ}{y:ℝ} (p₁: ChamberOilΨ J aH k q)(pA:k≤ j)(ha: 0≤ aH)(hv:aH≤h)(H:CutFrom X Y C J q h P j y): KettleΨ J P j h q:=by
 have hL:Tendsto (dleaf R.L) atTop (𝓝 0):= ((dev_R R).1.low (k:=1) (by norm_num)).spine
 intro z pz; let w:=z/2; have hw:0<w:=half_pos pz
 filter_upwards [eventually_ge_atTop y,p₁ w hw,hL.eventually (ge_mem_nhds hw)] with x y' b u
 intro m n Y p p' ℓ β F v e f
 let c:= room_drop pA ℓ; obtain ⟨δ,C₁,r₁,R₃,A⟩:= b m n Y p p' c; obtain ⟨vRh,r,hR,W,R₂,S⟩:=H.ships m n Y x p p' y' ℓ; letI:=R₃; letI:=R₂; obtain ⟨A,A',vx,XQ⟩:= A; obtain ⟨S,s,hP⟩:= S; rw [hP]; let G:= heater ha hv f
 let P1:= submits (F:=(F,0)) vx e ⟨G,Charged.zero.mono (mul_nonneg (by norm_num) vx.high.le)⟩; let P2:= submits (F:=(F,0)) vRh e ⟨f,Charged.zero.mono (mul_nonneg (by norm_num) vRh.high.le)⟩
 have hV:= XQ P1 v
 -- low reference solve. wave equality / launch density
 let hpR:=(S.prosper (u:=v) (v:=v) A P2 P1 (Filter.EventuallyEq.rfl) ℓ c).2.2
 let U₁:= ((A.worn (s:=vx) A').cost (β:ℂ) (F,0) e ⟨G,Charged.zero.mono (mul_nonneg (by norm_num) vx.high.le)⟩).1.1
 let U₂:= ((S.worn (s:=vRh) s).cost (β:ℂ) (F,0) e ⟨f, Charged.zero.mono (mul_nonneg (by norm_num) vRh.high.le)⟩).1.1
 have he:= abs_le.mp (compare_real U _ _ (J.gran.trans ℓ.rocket.size) (fun x=> (ℓ.rocket.paid.paid x).shrink J.hr.le) (ha.trans hv) ha U₂.toCost U₁.toCost hpR); have hh:= he.1
 let W:= Y.step V; have h': Earn.roomSite (Domain m B)=sites (mid m B):=by unfold Earn.roomSite sites; rw [site_card,Nat.cast_pow]
 have hD:sites (mid m B)≤Earn.roomSite (Domain n B):=h'.symm.le.trans (Earn.builtLe W)
 have hi: (0:ℝ)≤ sites (mid m B):=zero_le_one.trans (sites_pos _)
 have hl:(sites (mid n B))=Earn.roomSite (Domain n B):=(ser_pocket _).symm; have hm:z=w+w:=(add_halves _).symm; rw [hm]; unfold rentD at hV ⊢; nlinarith only [mul_le_mul_of_nonneg_right u hi,hV,mul_le_mul_of_nonneg_left (hD.trans_eq hl.symm) hw.le,hh,mul_nonneg hw.le hi]

end Pitching.Focus
end YM.CF.Py.Rate

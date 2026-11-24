import YM.CF.BProof.Grain.Pole
import YM.CF.BProof.Epoch.Grow
import YM.CF.Reed.Trio
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open YM.CF.Floral Ione Haro Beau Oise Larch Lilt Vow
open scoped YM.CF.Mew
namespace Grain
open Bake Cupboard Cupboard.BasisSt Sour Tap Glyph Digit BondL Axial
open scoped YM.CF.Sour.Axial
variable {R:Patch} (P_:BudgetPoint){x:ℝ}(F G D H:ℝ→ℝ)(h A a b c d:ℝ)
local notation "Pz"=>hall_P P_ -- .B vs .radius
local notation "cnt" => cQ
-- feepad arithmetic rank2 & 1.Note variant takes |
local notation "gL"=> Scales.g SU.group R.L
local notation "zP"=> rainX R 1
local notation "zD"=> rainX R 2
open SupportP
open Taxi Beau AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Geo AnalyticBridge.VerifiedReset.Collection UVNext.PricedKernels Work.F03 WilsonStartup Vow
open Taxi.Denn PushA
variable (Aχ Γχ:ℝ)(S: RG.Stage) (k:ℕ)
-- `P_* only` in declaration. η = Burn/h.Tune. ordering okay.
abbrev fair (P:BudgetPoint)(δ:ℕ)(Γ:ℝ):=1+Taxi.Denn.CH P δ Γ*‖Complex.reCLM‖
local notation "σΦ"=> S.width
local notation "qP"=> S.clip
local notation "CF"=> S.paths
abbrev ηp (P:BudgetPoint)(k:ℕ)(S:RG.Stage)(A Γ C d:ℝ):ℝ:=(regC P S.clip S.width S.paths A Γ +1)*fair P k Γ*C*d -- `C=lance` `d=Amconst`
lemma fair_p (h:0≤Γχ):1 ≤ fair P_ k Γχ:=le_add_of_nonneg_right (mul_nonneg (priceCH P_ k Γχ h).le (norm_nonneg _))
private lemma cash_p (p:0≤ Aχ): 0< regC P_ qP σΦ CF Aχ Γχ:=lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left (money_K _ _ P_ S p)) -- signature
lemma ηp_pos (p:0<A)(h:0<d)(hp:0≤ Aχ)(v:0≤Γχ) : 0<ηp P_ k S Aχ Γχ A d:=by
 have he:0< fair P_ k Γχ:=zero_lt_one.trans_le (fair_p P_ Γχ k v); have ht:= cash_p P_ Aχ Γχ S hp; unfold ηp; positivity
private lemma cash_f(x:ℝ): regC (Pz x) qP σΦ CF Aχ Γχ= regC P_ qP σΦ CF Aχ Γχ:=by obtain ⟨p,h,t⟩:=let_X P_ x; unfold regC; rw [spend_T P_ _ _ _ _ _ _ p h t]
private lemma fair_f(x:ℝ) : fair (Pz x) k Γχ= fair P_ k Γχ:=by obtain ⟨p,h,t⟩:=let_X P_ x; unfold fair Taxi.Denn.CH TC Compass.compassCost faceCost; rw [p,h,t]
local notation "vm"=>d/(R.L.val:ℝ)
local notation "ηq"=> ηp P_ k S Aχ Γχ A d/(R.L.val:ℝ)
abbrev ψf(P:BudgetPoint)(C d:ℝ)(R:Patch)(x:ℝ):= phase_v (hall_P P x) (C*(d/(R.L.val:ℝ)*dleaf R.L x))
local notation "Φ0" => fair P_ k Γχ
local notation "Ψα" x:max => (A*(vm*(x)))
local notation "ΨY" x:max => (Ψα (F (x))) -- use α separate
local notation "Ψv" x:max => (Ψα (dleaf R.L (x)))
local notation "Ψu" x:max => (Φ0 * ΨY (x))
local notation "Ψζ"=> ψf P_ A d R
local notation "KΦ"=> (‖Complex.reCLM‖*A*vm)
lemma soft (p:0<A)(t:0<d)(hp:0≤ Aχ)(hu:0≤Γχ)(hh:1≤h)(q:S.clip.direct≤1)
    (m:(x:ℝ)→Digit.Cash (hall_P P_ x))(g:sizeK R.L 1 (fun x=>(m x).Γr))(y:∀ x,(m x).κ=zD x)(hf:sizeK R.L 2 F)(hs:Chill_v H)(hc:∀ᶠ x in atTop,0<(m x).Γr∧ dleaf R.L x≤ F x)
    (pw:ηp P_ k S Aχ Γχ A d/(R.L.val:ℝ)≤1/4) :
    Chill_v (Ψζ) ∧ sizeK R.L 0 (Ψζ) ∧ ∃ (Hs X:ℝ→ℝ),∀ᶠ x in atTop, let P:=Pz x; let C:=(m x); let U:= Ψu x; Airport P qP σΦ CF Γχ Aχ k R.L.val C h (ΨY x) (Hs x) U (H x) (X x) ∧ ∀ B:ℝ, Charity (CutQ P qP σΦ CF Γχ Aχ U) (Cog_P P (X x) C.κ) (regC P qP σΦ CF Aχ Γχ * Ψv x) KΦ (ΨY x) (Ψv x) (F x) (dleaf R.L x) (ηq) B ((Ψζ) x) (phase_v P (Ψv x)) h:=by
 let Ue(x):= Ψu x; have hU:sizeK R.L 2 Ue:=((hf.scale _).scale _).scale _; let Kf(x):=|glow_W (Pz x) qP σΦ CF Γχ (Ue x) R.L.val|
 have hw: Chill_v Kf := (crop_F _ Γχ _ _ _ R.L.val S q hU).trend (Eventually.of_forall fun x=> (abs_abs (glow_W (Pz x) qP σΦ CF Γχ (Ue x) R.L.val)).le)
 let H0(x):= H x+Kf x+Ue x; have hb:Chill_v H0:=(hs.noteR hw).noteR (Chill_v.coin (hU.low (by omega)))
 let G(x:ℝ):=8*(m x).Γr; let P':=fun x:ℝ=>8*((rainX R 2 x)⁻¹*(m x).Γr); have hg:sizeK R.L 1 G:= g.scale _; obtain ⟨X,-,vZ,iP,Q⟩:=crown_T P_ R G P' (fun x=>4*H0 x) hg (hc.mono fun x p=>mul_pos (by norm_num) p.1) (((rain_l R 2).tint g).scale 8) P_.order P_.power (hb.cheap _)
 refine ⟨?_, qluv _ S q (((dev_R R).1.scale _).scale _),H0,X,?_⟩ -- HsV bogus
 · apply ((dev_R R).2.cheap KΦ).trend; filter_upwards [purse_K P_ S q] with x p; unfold ψf phase_v; rw [p.1]; exact Eq.le (congrArg _ (by ring)) -- .1 orient?
 let C':=Φ0; let E:=A; let D:= (R.L.val:ℝ); have hd:0<D:=by unfold D; positivity
 let θ:= ηq; have he:0< θ:=div_pos (ηp_pos P_ A d Aχ Γχ S k p t hp hu) hd
 filter_upwards [Q,hc,vZ,(fee_Q P_ G hg).spine.eventually (Iio_mem_nhds zero_lt_one), tenor_Q (θ/4) _ iP (by positivity), spice_R (R:=R),hall_l P_,eventually_gt_atTop (0:ℝ)] with x hc hv v ht hY hS hl hp'
 intro T M U; obtain ⟨v,w⟩:=v
 have hx:Cog_P T (X x) M.κ≤ θ/4*dleaf R.L x:=by
    unfold T M Cog_P; rw [y,hl,(let_X P_ x).1,(let_X P_ x).2.1]; exact hY
 have hk:=cash_p P_ Aχ Γχ S hp; let Z:= regC P_ qP σΦ CF Aχ Γχ; have hl': regC T qP σΦ CF Aχ Γχ=Z:= cash_f P_ Aχ Γχ S x; have hu':1 ≤ C':= fair_p P_ Γχ k hu; let B:=dleaf R.L x; have hpos:0<B:=mul_pos hS.2.2 (Work.E09.temp_pos hp')
 let Y:= Ψv x; have hj:0≤Y:=by unfold Y; exact mul_nonneg p.le (mul_nonneg (div_nonneg t.le hd.le) hpos.le)
 have h1(x): (Z+1)*(C'* (A*(d/D*x)))=θ*x:=by unfold Z C' θ ηp D; ring
 have hmode: θ/4*B≤B:=by have ht:=mul_le_mul_of_nonneg_right pw hpos.le; change θ*B ≤ _ at ht; linarith
 refine ⟨⟨⟨?_,hh,mul_pos (by norm_num) hv.1,ht,v,?_,hc.1,?_⟩,?_,le_rfl⟩,fun a' =>⟨?_,?_,?_,hx.trans hmode,?_,le_rfl⟩⟩
 · unfold M; rw [y]; exact hS.2.1
 · unfold T; rw [hl]; exact w.trans_lt (by norm_num)
 · unfold M; rw [y]; exact hc.2
 · change fair (Pz x) _ _ * _ ≤ Φ0* _; rw [fair_f]
 · exact Eq.le (by ring)
 · unfold CutQ; rw [hl']; exact Eq.le (h1 _)
 · have ht:= mul_le_mul_of_nonneg_left hv.2 he.le; change θ* B ≤ _ at ht; change _ ≤ θ*_; change _ ≤ θ/4*B at hx; linarith only [hx,ht]
 rw [hl']; calc
   _ ≤ (Z+1)* (C'* Y) := mul_le_mul (le_add_of_nonneg_right zero_le_one) (le_mul_of_one_le_left hj hu') hj (add_nonneg hk.le zero_le_one)
   _ = θ* B:= h1 _
   _ ≤ _:=by change _ ≤ B; have h1:=mul_le_mul_of_nonneg_right pw hpos.le; change θ*B ≤ _ at h1; linarith
end Grain
end YM.CF.Py

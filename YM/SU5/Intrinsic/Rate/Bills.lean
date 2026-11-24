import YM.SU5.Intrinsic.Rate.Shop
import YM.SU5.Intrinsic.Rate.Height
import SatinThinApt

/-! # XXI cost. Joint high-cover bill for one Location. -/
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

namespace Focus
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt Vow Ione Beau
open Sour Stockpile Test TestW QuiltB Lor Lilt Rill Haro
variable {Wk b0 b1 b2 b3 Aχ Γχ Bv r:ℝ}{n₀ n₁:ℕ} (s: Major V Wk b0 b1 b2 b3 Aχ Γχ n₀) {pW:WindV K.j 2}{X F:ℝ→ℝ}
local notation "κB"=> budS R Wk Pay pW.C
local notation "κS"=> wrc R Wk Pay pW.C h
local notation "Qβ"=> χPost K R Pay pW.C Wk Aχ Γχ
local notation "Qφ"=> χPrice K R Pay pW.C Wk Aχ Γχ
local notation "Qs" x:max => couponY K R s.k Aχ Γχ (Qφ x) x
variable (u:Outlook D c X F pW ag Cg Bv n₁)
variable (l:lobe (2*catap Wk) h (γ₀ HI b0 (Tenant.quota^2*b1) (Tenant.quota^2*b2) 0 h) HI)(hO:J.roomX ≤ b3)
variable (fx:FitB R.L.val K s.k Aχ Γχ Pay pW.C Wk)
local notation "κg"=> sprayM D.pilot R ag

variable {ψ₁ ψ₂ θ₁ θ₂ ξ ξ' Λr g₁ g₀ μp:ℝ} {N0:ℕ}{cs:stationary D c x ag Cg g₁ Bv n₁}{o:Pitching w D x}(Z0:Cellar N0 o p p' c (allF R.L x) ag Cg)(T:Weather cs Z0 pW g₀)
local notation "ε"=> (dleaf R.L x/1000)
local notation "εs"=> (εp R Pay pW.C x)
local notation "km"=> 2*((ηA R c x g₁ (κg x) h Pay g₀ (epoch x) K Γχ (κB x))+(Qs x))
local notation "κτ"=> SelfCert (epoch x) b0 b1 b2 (κS x) 0 Wk g₁ g₀ (κg x) pW D x c
local notation "EqΥ"=> (BudgetPoint.mass)
local notation "Ux"=> (κS x)
local notation "ξx"=> rainX R 2 x
variable {nα:ℕ}{Tξ:Hove.Grant K.j 2} {lφ μℓ ξC Vμ Kμ Wγ Xμ:ℝ}
open Neon

abbrev ΔHigh (R:Patch) (p:BudgetPoint) (x g:ℝ): Prop := ∀ n : Side, p.B=radiusB x →
    ∀ F F' : RegBudget n, ∀ h:ℝ, 0≤h→ IncX Utrue F p h (dleaf R.L x) → IncX Utrue F' (plusOneRate p) h g →
    (∀ i : Scree.Hub n, p.B < coverNumber p.B i.val.2 → F i=F' i) →
    SupportRate (detectorBudget p) F h (peripheryCost R.L x)

include u
lemma table_cap (hU:sizeK R.L 2 (wrc R Wk Pay pW.C h)) (b0 b1 b2:ℝ): sizeK R.L 0 (fun x=> Shop.tableCost R (epoch x) (κS x) h b0 b1 b2 (X x) (F x) x) := by
 -- φcape etc: epoch just affects a few weights which are identical to HI for all x.
 let f(x:ℝ):=φcape (plusOneRate (epoch x)) b0 (Tenant.quota^2*b1*κS x) (Tenant.quota^2*b2*κS x) h
 let g(x:ℝ):=Sour.Glyph.cap1 (plusOneRate (epoch x)) (BondL.øK (κS x)) h
 let a:=φcape (plusOneRate HI) b0 (Tenant.quota^2*b1) (Tenant.quota^2*b2) h; let b:=Sour.Glyph.cap1 (plusOneRate HI) (BondL.øK 1) h
 have hf:f=(fun x=> a*κS x):= by
   funext x; obtain ⟨ho,hp,he⟩ := let_X HI x
   unfold f a φcape Sour.Glyph.cap2 κY tollL0 numV
   dsimp only [plusOneRate,surchargeRate,epoch]; rw [he,ho,hp]; ring
 have hk:g=(fun x=> b*κS x):=by
   funext x; obtain ⟨ho,hp,he⟩ := let_X HI x
   unfold g b Sour.Glyph.cap1 κY tollL0 numV BondL.øK
   dsimp only [plusOneRate,surchargeRate,epoch]; rw [he,ho,hp]; ring
 let V:= scheduled_port u.bookK u.warmK u.chart u.warmG
 refine (((V.accrue ((?hf : sizeK R.L 2 f).low (by omega))).accrue (((sizeK.main R.L).square 2).low (by omega))).accrue ((?hg:sizeK R.L 2 g).low (by omega))).low (by omega)
 · rw [hf]; exact hU.scale _
 · rw [hk]; exact hU.scale _

lemma rates_high (hU:sizeK R.L 2 (wrc R Wk Pay pW.C h))(b0 b1 b2:ℝ)(hb:0<b0) :
     ∀ᶠ x in atTop, ΔHigh R (epoch x) x (Shop.tableCost R (epoch x) (κS x) h b0 b1 b2 (X x) (F x) x) ∧ 2*((epoch x).supportExponent+1)*Fief.tileN 1 ≤ b0/2*(epoch x).B ∧ mstar R.L.val+1+lunarExtent ≤ (epoch x).B:=by
 have he:=buy_B HI (2*(HI.supportExponent+1)*Fief.tileN 1) (show 0<b0/2 by linarith)
 filter_upwards [at_high_covers R _ (table_cap u hU b0 b1 b2),he,hall_l HI, Work.E07.radiusB_eventually (mstar R.L.val+1+lunarExtent)] with x p h e v
 refine ⟨fun n h F F' => p _ _ h Utrue Utrue F F',?_,?_⟩
 · change _ * ((hall_P HI x).supportExponent+1)*_ ≤ _
   rw [(let_X HI x).2.2]; exact h
 change _ ≤ (hall_P HI x).B; rwa [e]

omit u
def WithRate124 (J:Robes N V W)(q:Chi)(h:ℝ): StepReceipt R B:= fun _ _ w x p p' P=>
 ∀ (b:ℝ) G, enters (x+billX R.L) (b:ℂ) → Charged p' w.input K.j R.L.val h (3*dleaf R.L x) G →
    SupportRate (detectorBudget p) (head_L (P.realArr b G).1) h (peripheryCost R.L x)

include T
lemma wants {δ C r:ℝ} [Nonempty (Haro.ΘS r)] (S:Shop w J p p' q h x r) (q0:Shop.Ready δ C S) (η:Capsule R x)
 (u:∃ (Vq:Rill.Arch w.G d) (Ty:Ids (Scree.mid m B)), Vq.val=1 ∧ S.Lp=articles (Z0:=Z0) Ty Vq)
 (hq: ΔHigh R p x (Shop.tableCost R p r h S.b0 S.b1 S.b2 g₁ g₀ x))
 (hb : 2*(p.supportExponent+1)*Fief.tileN 1 ≤ S.b0/2*p.B)
 (hk:mstar R.L.val+1+lunarExtent ≤ p.B): WithRate124 J q h m n w x p p' S.operate:=by
 intro b G ht t
 let f:= (S.operate.realArr b G).1; let v:=submits η ht (show Both (Charged p' w.input K.j R.L.val h (3*dleaf R.L x)) (G,0) from ⟨t,Charged.zero.mono (mul_nonneg (by norm_num) η.high.le)⟩)
 let pX:= ((S.taxed v q0.more q0.last).1.mono (show dleaf R.L x/1000 ≤ dleaf R.L x by linarith [η.high])).inc
 obtain ⟨Vq,Ty,Y,Xρ⟩:=u; obtain ⟨Z,tF,w⟩:= S.literal_boost T Vq Y Ty v Xρ hb
 refine hq _ Z0.request.boot.B _ Z _ (zero_le_one.trans D.high) (Beau.price_Q p f pX|>.1) tF (fun i u=> w i ?_ ?_) <;> omega
end Focus
end Pitching
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.Pitching.Focus.rates_high
#print axioms YM.CF.Py.Rate.Pitching.Focus.wants

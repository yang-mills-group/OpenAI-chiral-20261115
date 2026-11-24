import YM.SU5.SatinWard.Resolution.Aspen
import YM.SU5.SatinWard.Resolution.Mimic
import YM.SU5.SatinWard.Resolution.Aroma
import YM.SU5.SatinWard.Resolution.HeatFinance
import Anomaly.Compass.Tension
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 70000
noncomputable section
set_option linter.unusedSectionVars false
set_option quotPrecheck false
namespace YM.CF.Py.Rate.LocalLimit.Preparation
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
open Pitching Focus QuadClock.ShapeLab
open Oise Buffered
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) (Γ:ℝ)(Pay kc:ℝ)(Tξ:Hove.Grant P.K.j 2)(nmc m:ℕ) (Z V K W:ℝ→ℝ)
variable (uZ:BladeQ P.R Z W V K)(proofW:∀ᶠ s:ℕ in atTop,∀ᶠ i in atTop,∀ k,s<Y.uv k → stockedTap Y Pay kc Γ Tξ nmc m Z V K W s i k)(flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)
variable {η ι:Type}[Fintype ι][DecidableEq ι][Fintype η](F:ResolutionFrame ι)(C H A u:ℝ)


open Pail.Dew Swell.Porticus QuadClock.ShapeLab.ResolutionFrame
open Lampshade SignSlot Waxy Tap
set_option linter.flexible false
variable {a b c d U ε f r ψ:ℝ}{s i k:ℕ}
local notation "Bα"=> RootBook Y i k s
local notation "pβ" => (Bα).p
local notation "Λ" => P.Ctor (Y.ir i) s
local notation "V₀"=> (Y.voyage i).CapeT s
local notation "θ"=>lapQ Y s
local notation "ωs"=> hat P.R.L P.x s
local notation "ARE"=>stockRate (Bα).p
local notation "L★"=> P.R.L
include proofW flag
lemma cartLoan (z:0 ≤ Γ)(h:DayT 6 Γ) : ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k,s<Y.uv k → CartRoom P.U ((Y.voyage i).CapeT s) (RootBook Y i k s) (L★).val Γ P.h:=by -- notation implicit shadow P'.uv Y
 let u:= stockedBeam Y Γ Pay kc Tξ nmc m Z V K W flag proofW; filter_upwards [u, (turnover P).eventually (Oath.progP 2 6 100), (Work.E01.radiusB_tendsto.comp (turnover P)).eventually_ge_atTop 10] with s v w t
 filter_upwards [v,Y.ir_grows.tendsto_atTop.eventually_gt_atTop 32] with i z' p k u
 have v:= z' k u; obtain ⟨pB,e,O,P',U⟩:=p_meters Y i k s u
 have ht:32 < (P.Ctor (Y.ir i) s).val:= p.trans_le (amplit ..)
 let A:=P.Ctor (Y.ir i) s; have hz:3 ≤ A.val:=by unfold A; omega;
 exact ⟨v.2.1,P.height,⟨pB.symm ▸ t,(show 20<A.val from (by unfold A; omega)).trans_le (Nat.le_mul_of_pos_right _ two_pos),hz⟩,⟨z,O.symm ▸ h,hat P.R.L P.x s,O.symm ▸ P'.symm ▸ w,e,(by change 10 ≤ radiusB (hat P.R.L P.x s) at t; omega)⟩,fun i=> (v.2.2.1 i).2.2.1⟩
omit flag proofW
variable (p: GardenPlan Y s i k a b ψ f c (stencilReserve P.R.L)) (pB:0≤b)(pH:0<c)(vΩ:CartRoom P.U ((Y.voyage i).CapeT s) (RootBook Y i k s) (P.R.L).val Γ P.h)
variable (Hw:0<lapQ Y s) (w:s< Y.uv k) {Aψ:Hove.Grant P.K.j 2}
local notation "Goals" j:max F:max => Enlightenment F P.U V₀ Bα j 0 P.J.n (L★).val
lemma em_p (P':BudgetPoint)(Γ:ℝ):0 ≤ emGain P' Γ:=by unfold emGain duty_Q composeCost Δv; positivity
lemma cu_p (P':BudgetPoint)(Γ:ℝ)(L:ℕ):0 ≤ Θgain P' Γ L:=by unfold Θgain strive_E composeCost Extr_h; positivity
lemma crownRates (u:s<Y.uv k): emGain (Bα).p Γ =emGain HI Γ ∧ Θgain pβ Γ (L★).val= Θgain HI Γ (L★).val:=by
 obtain ⟨hb,hv,O,X,Vq⟩:=p_meters Y i k s u; unfold emGain Θgain; rw [O,X, show Δv (Bα).p Γ=Δv HI Γ from Ves HI (Bα).p O X Vq Γ, show Extr_h (L★).val (Bα).p Γ = Extr_h (L★).val HI Γ from μφ_c HI (Bα).p O X Vq (L★).val Γ]; exact ⟨rfl,rfl⟩ -- μ args ..
local notation "Wpp"=> floorMoney HI d P.h 24
abbrev growthPrice (c:ℝ):ℝ:=1+|floorMoney HI c 1 24|
abbrev vigorΩ (P:Preparation)(s:ℕ):= (pinpr P.R.L (hat P.R.L P.x s))/P.h^2
abbrev centerBase(P:Preparation)(a b d:ℝ)(x:ℝ):ℝ:= allotΨ P.R.L x * |YieldFull P a b d x|
abbrev originFare (P:Preparation)(a d:ℝ):ℝ:=2*|αlife a P.d d|
abbrev plutoX (P:Preparation)(a b d:ℝ)(x:ℝ):ℝ:= |YieldFull P a b d x|
lemma centerLitt (P:Preparation)(a b d:ℝ)(v:0<a):Litt P.R 2 (centerBase P a b d):= by
 unfold centerBase; simp_rw [mul_comm (allotΨ _ _)]; refine spade_grip ?_ (spade_one _); refine (pocket_R (P:=P) v b 1 1 d).2.2.tune (Eventually.of_forall (fun _=>?_)); exact le_of_eq (abs_abs _)
lemma floorAge (h d:ℝ) (v:0≤d)(u:1≤h): floorMoney HI d h 24 +1 ≤ growthPrice d * h^2:=by
 let a:= cashPoncho (KazZ HI d 1) HI.supportExponent 24; let b:= cashPoncho d HI.supportExponent 24
 have hb: 0≤b:= mul_nonneg v (Real.exp_pos _).le
 calc
  _ = a*h^2+b+1:=by unfold a b floorMoney KazZ cashPoncho; ring
  _ ≤ (1+(a+b))*h^2:=by nlinarith only [one_le_pow₀ (n:=2) u,hb]
  _ ≤ _:= mul_le_mul_of_nonneg_right (add_le_add_right (le_abs_self _) _) (sq_nonneg _)
local notation "λχ"=> vigorΩ P s
local notation "ΑC"=> centerBase P a b d ωs
local notation "Ηc"=> growthPrice d * θ
variable {F} (hp:F.Stretch C)
include p pB pH Hw w vΩ hp
-- fit input unscaled both pure onsite. stem inputs scaled only at Step entry. sector expected after smul bought.
lemma floraM {d ε:ℝ}(M:Pal)(hx:Moto.Fit (0:Site Λ) 2 1 d (bud_k (0:Site Λ) 0 0 M))
    (T:Site Λ→ Mark Λ)(x: Coords ι)(Te:orbitAverage BodyPull (0:Site Λ) (F.colors Λ) (onsiteOne (bud_k (0:Site Λ) 0 0 M))= T)
 (ξ: (vigorΩ P s) • arcLoad 0 (bud_k (0:Site Λ) 0 0 M)= F.atScale P.h θ x)
 (pε:0≤ ε)(r:ε≤1)
 (wε:let y:= hat P.R.L P.x s; let w:= DrillLoan P a b f c d y; let u:=YieldHeat P a b d y; AxStamp.Ρpost HI w+AxStamp.Ρpost HI u ≤ ε ∧ floorMoney HI d P.h 24+w+u ≤ floorMoney HI d P.h 24+ε):
   ∃ y: Coords ι, ‖y-x‖≤ C*ε ∧ (Goals (24*(Bα).p.B+12) F) ((vigorΩ P s) • T) y P.h θ ARE (centerBase P a b d ωs) (emGain HI Γ*(growthPrice d * θ)) (Θgain HI Γ (L★).val*(growthPrice d*θ)) (growthPrice d*θ) (originFare P a d*θ):=by
 have he:= P.height; have hu:1≤P.h^2:= one_le_pow₀ he
 have hz: 0 < λχ:= div_pos Hw (by positivity); have hx': λχ ≤ θ := div_le_self Hw.le hu
 have hd:0 ≤ d:=(Hove.paidp_p ..).trans hx.1
 let y:=ωs; let sB:= growthPrice d*θ; let J:= centerBase P a b d y; let I:=originFare P a d*θ; let F₀:=bud_k (0:Site Λ) 0 0 M
 have Hx: OnSite 0 F₀:= fun i j p=>⟨(gone_l 0 0 0 M i j p).1.symm,(gone_l 0 0 0 M i j p).2.symm⟩
 obtain ⟨K,h⟩:= drawPure Y pB pH p F₀ hx Hx w; let V:=onsiteOne F₀; let M':=firePlate V₀ (ρlens F₀)
 let G:= λχ • K; let M'':= arcLoad (0:Site Λ) F₀
 let H₀:= h.scaleP he (λχ:ℂ) -- order check
 rw [Complex.norm_real, Real.norm_of_nonneg hz.le] at H₀
 have hf:Totem P.U Bα V₀ P.J.n (L★).val 24 (24*(Bα).p.B+12) 0 G (λχ • V) (λχ • M') (F.atScale P.h θ x) P.h ARE J sB (θ*ε) I:=by
    rw [←ξ]; apply H₀.dawnV he -- ..
    · refine (mul_le_mul hx' (le_abs_self _) ?_ Hw.le); -- 0≤YieldFull? use left norm substitution order; prove via price.h.not
      obtain ⟨K,M,G,g,P,U⟩:=h.bill.yard.price; apply U.trans'; unfold voyageB; exact sum_nonneg fun i _=>by apply mul_nonneg _ (Real.exp_pos _).le; obtain ⟨f,h,_⟩:=(G i).forms; exact h.price
    · calc
       _ ≤ λχ * (growthPrice d * P.h^2):= mul_le_mul_of_nonneg_left (wε.2.trans ((add_le_add_right r _).trans (floorAge _ _ hd he))) hz.le
       _ = _:=by unfold sB vigorΩ lapQ; field_simp
    · refine (mul_le_mul_of_nonneg_left wε.1 hz.le).trans (mul_le_mul_of_nonneg_right hx' pε)
    unfold I originFare; exact (mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) (le_abs_self _)) hz.le).trans ((mul_le_mul_of_nonneg_right hx' (add_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq (by ring)) -- orientation!
 have v:orbitAverage BodyPull 0 (F.colors Λ) (λχ • V)=λχ • T:=by rw [←Te]; funext j; unfold orbitAverage alleyS; rw [Pi.smul_apply, smul_comm λχ]; congr 1; rw [Finset.smul_sum]; apply sum_congr rfl; intro t _; change (F.colors Λ).sgn t • BodyPull t (λχ • V) = λχ • _; rw [map_smul, smul_comm λχ ((F.colors Λ).sgn t)] -- tune
 obtain ⟨Gη,hz,vT⟩:= become hf vΩ (((F.representation _ _ _ _ Hw he).2 (LinearMap.mem_range_self _ _)).2) (F.kills Λ)
 rw [v,(crownRates (i:=i) Y Γ w).1,(crownRates (i:=i) Y Γ w).2] at vT
 obtain ⟨y,Y,a⟩:= sales_A vT x hz hp Hw he
 exact ⟨y,Y,a.increase le_rfl (Nat.zero_le _) le_rfl le_rfl le_rfl le_rfl le_rfl⟩ -- m may change; use .increase after modify Aspen! tune

end YM.CF.Py.Rate.LocalLimit.Preparation

import YM.CF.Jade.Move
import YM.CF.Vp929.Loan.Harvest
import YM.CF.Vp929.Loan.Candle
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
open Rush Scroll Paige Vault Phase Acorn Spire
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
local notation "Dα"=> radiusB x
local notation "Lo"=> Palot.leaf (Site (Domain m B))
local notation "Ω"=> Cord S'
local notation "G5'"=> Directions SU.group (Domain m B)
local notation "Ωs"=> V_→ Lo→ Raid D'
local notation "Ωx"=> V_→ Ride S'→ Orbit ι→ Cord S'→ Cipher ι
open Dialect Plume.Rate
variable {℘ κ b δ amp:ℝ}
namespace Engine

local notation "KZ"=> ↥(Sil S' z')
local notation "ρq"=> depot η
open Docket Nor

-- Increase the activity receipt instead of paying the potentially
-- enormous full stamp of the zoomed purchases. Provisions p. trim.
abbrev accountTh (p:BudgetPoint)(x:ℝ)(i:ℕ)(v:ℝ):=
 reserveT p.power p.order (radiusB x) 1 * (v*degreePrice (radiusB x) v 1 ^i*(1-degreePrice (radiusB x) v 1)⁻¹)

lemma account_double (p:BudgetPoint)(x A C:ℝ)(i:ℕ)(ha:0 ≤ A)(hc:2*A ≤ C)
    (hq:degreePrice (radiusB x) C 1 < 1): 2*accountTh p x i A ≤ accountTh p x i C:=by
 let K:=radiusB x
 let U:=reserveT p.power p.order (radiusB x) 1
 let f(w:ℝ):=degreePrice K w 1
 have u:0≤U:=by unfold U reserveT coin_n stilK; positivity
 have pF:0 ≤ f A:=by unfold f degreePrice Trees.stretch; positivity
 have v:f A ≤ f C := by unfold f degreePrice Trees.stretch; gcongr; linarith only [ha,hc]
 have qC:0<1-f C:=sub_pos.mpr hq
 change 2*(U*(A* f A^i*(1-f A)⁻¹))≤ U*(C* f C^i*(1-f C)⁻¹)
 rw [show 2*(U*(A*f A^i*(1-f A)⁻¹))=U*((2*A)*f A^i*(1-f A)⁻¹) from by ring]
 have yA:1-f C≤1-f A:=sub_le_sub_left v _
 have u1: (1-f A)⁻¹ ≤ (1-f C)⁻¹:=by simpa using (one_div_le_one_div_of_le qC yA)
 have qA:0 ≤ 1-f A:= qC.le.trans yA
 have q:0 ≤ C:= by linarith only [ha,hc]
 exact mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul hc (pow_le_pow_left₀ pF v _) (pow_nonneg pF _) q) u1 (inv_nonneg.mpr qA) (mul_nonneg q (pow_nonneg (pF.trans v) _))) u

local notation "PP"=> tolQ p
local notation "Sα"=> Stake.PondP
local notation "XX" k:max=> (Location.step V w) -- notation invalid? unused
local notation "LΩ"=> V_ → Lo → Site (Domain m B)
local notation "ΩR"=>Troupe S' z' (Words S') → Palot.leaf (Site (Domain m B)) → Raid (Scree.Dwell (Scree.mid m B))
private def coinsA (p:BudgetPoint)(h:ℝ)(i:ℕ)(Zr:ΩR)(a:V_→ℝ)(x0:Site (Domain m B))(J':LΩ):ℝ:=
 ∑ k:V_ with Palot.outC i k, ∑ Q:Lo with x0∈ Q.val,
   a k*(tolQ p).mass Q.val (∑ j:Finset D',Scree.tariff (tolQ p) (J' k Q) h j * Zr k Q j)

private theorem book_plus (p:BudgetPoint)(t0:ℝ)(i:ℕ)(Zr Zq:ΩR)(a:V_→ℝ)(x0:Site (Domain m B))(J':LΩ):
    let f:=fun z=> coinsA (V:=V) (D:=D) (w:=w) p t0 i z a x0 J'
    f (Zr+Zq) = f Zr + f Zq:=by
  intro f
  unfold f coinsA BudgetPoint.mass
  simp only [Pi.add_apply,mul_add,sum_add_distrib]

private theorem book_mono (p:BudgetPoint)(t0:ℝ)(i:ℕ)(Zr:ΩR)(v:0≤Zr)(a b:V_→ℝ)(x0:Site (Domain m B))(J':LΩ)(h':0≤t0)(h:a ≤ b) :
    coinsA p t0 i Zr a x0 J' ≤ coinsA p t0 i Zr b x0 J' := by
 unfold coinsA; refine sum_le_sum fun k _=> sum_le_sum fun q _=> mul_le_mul_of_nonneg_right (h k) ?_
 exact mul_nonneg (Real.exp_pos _).le (sum_nonneg fun j _=> mul_nonneg (by unfold Scree.tariff; positivity) (v ..))

private theorem book_const (p:BudgetPoint)(t0 g:ℝ)(i:ℕ)(Zr:ΩR)(x0:Site (Domain m B))(J':LΩ) :
   coinsA (V:=V) (D:=D) (w:=w) p t0 i Zr (fun _=>g) x0 J' =
     g* coinsA (V:=V) (D:=D) (w:=w) p t0 i Zr (fun _=>1) x0 J' :=by
 unfold coinsA; rw [mul_sum]; apply sum_congr rfl; intro k u; rw [mul_sum]; simp

variable {Hh Kk Ac Ad C₁ t0:ℝ}
local notation "ST"=> Wray.stampY (S:=S') (r:=z') Hh Kk
local notation "CC"=> fun i:V_=> min Hh (ST i)

#print axioms book_const
lemma scaledTwosome {Tt Tk:ΩR} (hh:1≤Kk)(hb:Kk ≤Hh)(ph:0≤ t0)
    (uJ:ScaledV (ST) (tolQ p) t0 Ac x 1 Tt) (T₁:Troupe (w.step V) z' (Words (w.step V)) → Lo → Orbit ι → Cipher ι)
    {α:ℝ}(s:Harvest (V:=V) (D:=D) p t0 Ad α T₁ Tk) (hA:0 ≤ Tt)(u:α*Hh≤1)
    (hz:0< Ac)(hy:0<Ad)(u₁:2*Ac≤C₁)(u₂:2*Ad≤C₁)(v:degreePrice (radiusB x) C₁ 1 < 1) :
    let allT:= Tt+Tk
    ScaledV (CC) (tolQ p) t0 C₁ x 1 allT∧ BudgetVb (tolQ p) t0 C₁ x 1 allT:=by
 intro D0
 have hv:0≤Hh:= zero_le_one.trans (hh.trans hb)
 suffices Q: ScaledV (CC) (tolQ p) t0 C₁ x 1 D0 by
    refine ⟨Q,fun o m X v=>?_⟩
    have ht: (fun _:V_=>(1:ℝ))≤ CC:=fun i=> le_min (hh.trans hb) (shelfX _ _ _ (hh.trans hb) hh) -- `..` invalid
    have hD:0 ≤ D0:=add_nonneg hA s.nonnegative
    have hx:= (book_mono p t0 m D0 hD _ _ o X ph ht).trans (Q o m X v)
    simpa only [coinsA,one_mul] using hx
 intro v' i y' fQ
 change coinsA p t0 i D0 (CC) v' y'≤accountTh (tolQ p) x i C₁
 apply (book_plus p t0 i Tt Tk (CC) v' y').trans_le
 let W:=accountTh (tolQ p) x i
 have x₁:2*coinsA p t0 i Tt (CC) v' y' ≤ W C₁:= by
    have hx:coinsA p t0 i Tt (CC) v' y'≤ W Ac:= (book_mono p t0 i Tt hA (CC) (ST) v' y' ph (fun i=> min_le_right ..)).trans (uJ v' i y' fQ)
    exact (mul_le_mul_of_nonneg_left hx zero_le_two).trans (account_double (tolQ p) x _ _ i hz.le u₁ v)
 have x₂:2*coinsA p t0 i Tk (CC) v' y'≤ W C₁:= by
    have hs: coinsA p t0 i Tk (fun _=>1) v' y' ≤ α * W Ad:= by simp only [coinsA,one_mul]; exact s.meter v' i y' fQ
    have hx: coinsA p t0 i Tk (CC) v' y'≤ Hh*(α * W Ad):=
      (book_mono p t0 i Tk s.nonnegative (CC) (fun _=>Hh) v' y' ph (fun i=> min_le_left ..)).trans
        ((book_const p t0 Hh i Tk v' y').trans_le (mul_le_mul_of_nonneg_left hs hv))
    have wA:0≤ W Ad:=by
          unfold W accountTh; have ht:0 ≤ degreePrice (radiusB x) Ad 1:=by unfold degreePrice Trees.stretch; positivity
          have he:degreePrice (radiusB x) Ad 1<1:= lt_of_le_of_lt (show degreePrice (radiusB x) Ad 1≤degreePrice (radiusB x) C₁ 1 by unfold degreePrice Trees.stretch; gcongr; linarith) v
          have hj:0 ≤ 1-degreePrice (radiusB x) Ad 1:=by linarith only [he]
          unfold reserveT coin_n stilK; positivity
    have hD:Hh*(α*W Ad)≤ W Ad:=by rw [←mul_assoc,mul_comm Hh]; exact mul_le_of_le_one_left wA u
    exact (mul_le_mul_of_nonneg_left (hx.trans hD) zero_le_two).trans (account_double (tolQ p) x _ _ i hy.le u₂ v)
 linarith only [x₁,x₂]

variable {Z:Cellar N0 o p p' c f ag Cg}
variable (hF:Location.gross p' D f F) (Qh:β∈ Year R x)
local notation "hs"=> Z.toLid.choice Qh hF
local notation "hp"=> (Z.toLid.crew β Qh).1
local notation "hp'"=> (Z.toLid.fend Qh (Z.toLid.scaler Qh))
local notation "bg"=> Z.toLid.ZoomB Qh
local notation "Px"=> Troupe S' z' (Words S') → Lo → Orbit ι→Cipher ι
-- aliases prefer existing Baker.Mull. A Pb. Apply harvest tack.
lemma growRespect {Tt Tk:ΩR} {Yb Vb:Px} (U' : GroV V D.pilot D.Z (X:=Xs β) (Y:=Ys β F) o.SheepR o.bags o.vista hp hs Tt Yb t0 Ac 1)
    (V':ΩR) (W':BaseL U w.G (Ys β F) w.coarse w.fine q J.d)
    (pV: GroV V (bg) D.Z (X:=Xs β) (Y:=Ys β F) o.SheepR o.bags o.vista hp' W' V' Vb t0 κ 1)
    {α:ℝ}(u:Harvest (V:=V) (D:=D) p t0 Ad α (Vb-Yb) Tk)
    (hh:1≤Kk)(hb:Kk ≤Hh)(ph:0≤t0)(uJ:ScaledV (ST) (tolQ p) t0 Ac x 1 Tt)(hE:α*Hh ≤ 1)
    (hz:0< Ac)(hy:0<Ad)(u₁:2*Ac≤C₁)(u₂:2*Ad≤C₁)(v:degreePrice (radiusB x) C₁ 1 < 1):
    let zq:= Tt+Tk
    ScaledV (CC) (tolQ p) t0 C₁ x 1 zq ∧ GroV V (bg) D.Z (X:=Xs β) (Y:=Ys β F) o.SheepR o.bags o.vista hp' W' zq Vb t0 C₁ 1:=by
  intro zc; obtain ⟨p,T0⟩:= scaledTwosome hh hb ph uJ _ u U'.grace hE hz hy u₁ u₂ v
  refine ⟨p,add_nonneg U'.grace u.nonnegative,T0,fun i v=>?_⟩ -- constructor brackets
  let Vq:=pV.quiet i v
  refine ⟨Vq.toLullT,Vq.priceP,fun b l q a ha j=>?_⟩
  have h:= Prism.tack ((U'.quiet i v).hoist b l q a ha j) (u.hoist i v b l q a ha j)
  -- simplify evaluation of Vb-Yb on crumb
  have he(s:Pane ι): crumb (Yb i v (s,b.2)).val j + crumb ((Vb-Yb) i v (s,b.2)).val j=crumb (Vb i v (s,b.2)).val j:= by
    change crumb (Yb i v (s,b.2)).val j+ (crumb (Vb i v (s,b.2)).val j-crumb (Yb i v (s,b.2)).val j)=_
    ring
  simp_rw [Function.comp_apply,he] at h
  exact h
end Engine
end Pitching
end YM.CF.Py.Rate
#check YM.CF.Py.Rate.Pitching.Engine.account_double
#check YM.CF.Py.Rate.Pitching.Engine.scaledTwosome
#print axioms YM.CF.Py.Rate.Pitching.Engine.growRespect

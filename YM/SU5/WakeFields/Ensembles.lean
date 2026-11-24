import YM.SU5.WakeFields.Geometry
import YM.SU5.WakeFields.Payments


set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option maxRecDepth 2500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Filter
open Function
open Metric
open MeasureTheory
open Lattice Cube Lat Skye Lifted EmberWind
open Py Py.Rate LocalLimit FullBill Preparation Yoke Journey
open Satin Fock
open Ballad
open scoped Topology BigOperators Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Onyx (riseX)
open YM.Stationary (Gaia)

namespace Resolving
open Jewel Jewel.Program
open Regis Regis.Head.Brecht Regis.Circuit
open Hiro.Crossing
open Hiro (shotL)
open EmberWind.MixedCards MixedCards.Receipt
open Scree

variable (P:Spine) {J:Type*} [Fintype J] (X: ℕ → J→ Staff) (L : List J) (D:J→MixedCards.Ticket)
variable {β: ℕ→ℝ} (f:ℕ→ℕ) (p : Tuned P f β) {I A b:ℝ} (hp:0 < I) (ha:0<A) (r:ℕ→ℕ)
variable {Q:Spine.Register P}{E:ℝ}{Mc:ℕ} (W:Spine.PreparedInvestment P Q E Mc)
local notation "Y" => P.run
local notation "Z" => P.calibration
local notation "ι" => physicalPeriod P f
local notation "ν" => physicalCut P f
local notation "κ" t:max => Jewel.κFix β t
local notation "δ" s:max A:max => sPow P.par s A
local notation "q"=> P.par.K.j
local notation "Γ" x:max => (side Y (ι x.2) x.1)
local notation "ℳ" x:max => (RootBook Y (ι x.2) (ν x.2) x.1).J.M
local notation "ph" s:max => Pressure.temp (Vale.hat P.par.R.L P.par.x s)
include p
lemma pads : ∀ᶠ x in towerLimit, Kea.Pad q (Γ x) := by
  have hv:StrictMono f := Pooling.up p
  rw [towerLate]; refine .of_forall fun s=> ?_; filter_upwards [(period_grows P f hv).tendsto_atTop.eventually (bone_pose Y (nontrivial_spin P.par) s)] with i v
  exact v.1

omit p
lemma units_pos : (0:ℕ) < Fintype.card SU.group.ColorIndex := by
  letI := Thera.yet_one.nontrivial_color
  have v : 0 < SU.group.lieDim := by rw [Gauge.lieDim, ← SU.group.colorIso.finrank_eq]; exact Module.finrank_pos
  simpa [Gauge.ColorIndex] using v

abbrev pGauge (A:ℝ) (x : ℕ×ℕ) (β:ℕ→ℝ) (t u : materialL J) := (δ x.1 A:ℂ)^4 * realHue Y x.1 (ι x.2) (ν x.2) (X x.1) (Jewel.κFix β x.1) t u
abbrev valueHue (F:J→PlaqAxes)(z:J→ Gaia)(u v:materialL J) :ℂ := (sch (G:=SU.group) u.2 v.2 : ℝ)*specter (F u.1) (F v.1) (z u.1-z v.1)
variable (F:J→PlaqAxes) (K:J→Twah.DirSpin)
variable (U V:J→Gaia) (z:J→Gaia)
variable (t:∀ i, ∀ᶠ s in atTop, (X s i).face.2 = F i)
variable (w:∀ i,Tendsto (fun s=> riseX (sPow P.par s A) (X s i).face.1) atTop (𝓝 (U i)))
variable (u:∀ i,∀ᶠ s in atTop,(X s i).spin = K i)
variable (g:∀ i,Appoint P.par A (fun s=> (X s i).u) (z i))
variable (h: ∀ i j,z i=z j→ ∀ᶠ s in atTop,(X s i).u=(X s j).u)
include p ha t w
lemma huePower (i j:materialL J) (W: U i.1 ≠ U j.1) : Tendsto
    (fun x:ℕ × ℕ=> pGauge P X f A x β i j) towerLimit (𝓝 (valueHue F U i j)) := by
  let D:ℂ:= Fintype.card SU.group.ColorIndex; let b:ℂ:= sch (G:=SU.group) i.2 j.2
  let c:ℂ:= specter (F i.1) (F j.1) (U i.1-U j.1); let B(x:ℕ×ℕ):ℂ:= reachCost P.run x.1 (ι x.2) (ν x.2) (κ x.1); have he': D≠0:=by unfold D; exact_mod_cast (units_pos).ne'
  have f':= gauge_limit P (fun s=> X s i.1) (fun s=>X s j.1) (F i.1) (F j.1) f (Pooling.up p) ha (t _) (t _) (((w i.1).sub (w j.1)).congr (fun s=>(riseSub ..).symm)) (sub_ne_zero.mpr W)
  have hx:Tendsto B towerLimit (𝓝 ((1:ℝ):ℂ)):=Complex.continuous_ofReal.continuousAt.tendsto.comp (gatheringOnTower P f p)
  rw [Complex.ofReal_one] at hx; have hX := ((hx.pow 2).mul_const (b/D)).mul f'
  rw [one_pow,one_mul,show speckleV (F i.1) (F j.1) SU.group (U i.1 - U j.1) = D*c from rfl, show b/D*(D*c)=b*c by field_simp] at hX -- need unfold
  apply hX.congr; intro x; unfold pGauge; rw [hueCoupon];
  let U' := X x.1 i.1; let V' := X x.1 j.1; let d:= More (Γ x)
  let H:= P.par.V.L.H ((Y).uv (ν x.2)- x.1); let e:=onsite Y x.1 (ι x.2); let r:ℂ:= rimble d H (e U') (e V'); let g:ℂ:= δ x.1 A
  change (B x)^2*(b/D)*(g^4*(D*r)) = g^4*((B x)^2*b*r)
  field_simp; try ring

omit t w
include g u h
abbrev pSpin (A:ℝ) (x:ℕ×ℕ) (i j:Twah.Stamp J):ℂ := (δ x.1 A:ℂ)^3 * (covRead P.par.K.j 1 (Staff.u ∘ X x.1) (Staff.spin ∘ X x.1) (Γ x) (ℳ x) i j)
abbrev valueSpin (i j:Twah.Stamp J) := (8:ℂ)*Twah.germRho (z ∘ Prod.fst) K i j

lemma oilprice (i j:J) : Tendsto (fun x:ℕ×ℕ=> (sPow P.par x.1 A:ℂ)^3*
   Hiro.dietary 1 (X x.1 i).u (X x.1 j).u (X x.1 i).spin (X x.1 j).spin (Γ x) q (ℳ x)) towerLimit (𝓝 (8*shotL (z i-z j) (K i) (K j))) := by
  let f' := period_grows P f (Pooling.up p); let G:= zoomR P.par A
  let a(s):=(X s i).u; let b(s):=(X s j).u; let C (x:ℕ×ℕ):= Hiro.dietary (G x.1) (a x.1) (b x.1) (X x.1 i).spin (X x.1 j).spin (Γ x) q (ℳ x)
  have B : Tendsto C towerLimit (𝓝 (shotL (z i-z j) (K i) (K j))) := by
     apply Metric.tendsto_nhds.mpr; intro ε e
     have w := ((appoint_as _ ha _ _).1 (g i)).sub ((appoint_as _ ha _ _).1 (g j)); rw [towerLate]
     filter_upwards [whole_feast q (K i) (K j) (nontrivial_spin P.par) G (zoom_grows P.par ha) (zoom_pos P A) b a (w.congr (fun _=>(riseSub ..).symm)) (fun w=> h _ _ (sub_eq_zero.mp w)) (ε/2) (by positivity),u i,u j] with s v h₁ h₂
     filter_upwards [((Papal.count_la Y s).comp f'.tendsto_atTop).eventually v] with n p
     unfold C; dsimp only; rw [h₁,h₂]; exact (p (Vale.val_e ..) _).trans_lt (half_lt_self e)
  have hF:Tendsto (fun x:ℕ×ℕ=> (frayR P.par A x.1:ℂ)) towerLimit (𝓝 ((1:ℝ):ℂ)):=Complex.continuous_ofReal.continuousAt.tendsto.comp ((fray_lift P.par ha).comp firstTends)
  have he:= ((hF.const_mul (2:ℂ)).pow 3).mul B
  rw [show (2*((1:ℝ):ℂ))^3=(8:ℂ) by norm_num] at he; apply he.congr; intro x
  let F:ℂ:=2*(frayR P.par A x.1:ℂ); let D(x:ℕ×ℕ)(t:ℕ) := Hiro.dietary t (a x.1) (b x.1) (X x.1 i).spin (X x.1 j).spin (Γ x) q (ℳ x); let m:= G x.1
  have hv:F*(m:ℂ)=(sPow P.par x.1 A:ℂ):=by unfold F; exact_mod_cast unfray P x.1 A
  change F^3* C x=_*D x 1; rw [show C x=(m:ℂ)^3*D x 1 from lodge_scale ..,←mul_assoc,←mul_pow,hv]

lemma spinprice (i j:Twah.Stamp J) : Tendsto (fun x:ℕ×ℕ=> pSpin P X f A x i j) towerLimit
    (𝓝 (valueSpin K z i j)) := by
  let G := pSpin P X f A; let t := valueSpin K z
  have price(i j:J)(a b:SU.Slot) : Tendsto (fun x=> G x (i,a,true) (j,b,false)) towerLimit (𝓝 (t (i,a,true) (j,b,false))) := by
    let B(x:ℕ×ℕ):= (δ x.1 A:ℂ)^3
    have hZ(x:ℕ × ℕ): G x (i,a,true) (j,b,false) = B x*(if a=b then Hiro.dietary 1 (X x.1 i).u (X x.1 j).u (X x.1 i).spin (X x.1 j).spin (Γ x) q (ℳ x) else 0):= congrArg (B x * ·) (Hiro.rank_hint 1 _ _ _ _ (Vale.val_e ..) _ _)
    simp_rw [hZ]; unfold t valueSpin; rw [Cordial.funds]; by_cases x:a=b
    · simp only [if_pos x]; exact oilprice P X f p ha K z u g h i j -- h reused
    simp only [if_neg x,mul_zero]; exact tendsto_const_nhds
  obtain ⟨i,a,x⟩:=i; obtain ⟨j,b,y⟩:=j
  change Tendsto (fun p=> G p _ _) _ (𝓝 (t _ _)); cases x <;> cases y
  · have e(x:ℕ × ℕ) : G x (i,a,false) (j,b,false)= 0:=by
       unfold G pSpin; rw [show covRead _ _ _ _ _ _ _ _ = 0 from Hiro.still (N:=(Γ x)) (j:=q) (M:=(ℳ x)) 1 (X x.1 i).u (X x.1 j).u (X x.1 i).spin (X x.1 j).spin a b, mul_zero]
    simp_rw [e]; unfold t valueSpin; rw [Cordial.dcash,mul_zero]; exact tendsto_const_nhds
  · have hx(x:ℕ × ℕ) : G x (i,a,false) (j,b,true)= -G x (j,b,true) (i,a,false):=by
       unfold G pSpin; rw [show covRead _ _ _ _ _ _ _ _ = -(covRead _ 1 _ _ _ _ (j,b,true) (i,a,false)) from ?_, mul_neg]; exact Hiro.flipcost ..
    simp_rw [hx]; unfold t valueSpin; rw [Cordial.funds_neg,mul_neg]; exact (price j i b a).neg
  · exact price i j a b
  · have e(x:ℕ × ℕ) : G x (i,a,true) (j,b,true)= 0:=by
       unfold G pSpin; rw [show covRead _ _ _ _ _ _ _ _ = 0 from Hiro.calm (N:=(Γ x)) (j:=q) (M:=(ℳ x)) 1 (X x.1 i).u (X x.1 j).u (X x.1 i).spin (X x.1 j).spin a b, mul_zero]
    simp_rw [e]; unfold t valueSpin; rw [Cordial.dcash,mul_zero]; exact tendsto_const_nhds

include w t
abbrev tariff : ℂ := bus L D [] [] (valueHue F U) (valueSpin K z)
lemma tariff_limit (m:L.Pairwise (fun i j=> U i ≠ U j)) :
    Tendsto (fun x:ℕ×ℕ => (sPow P.par x.1 A:ℂ)^ (scaleFee D L)*costMany Y x.1 (ι x.2) (ν x.2) (X x.1) D L (Jewel.κFix β x.1)) towerLimit
      (𝓝 (tariff L D F K U z)):=by
  have H:= busLimit (M:=fun i j=> U i ≠ U j) L D [] [] _ _ towerLimit (by exact (show (([] : Receipt.Deck J).map Prod.fst ++ L).Pairwise (fun i j=> U i ≠ U j) from m)) (fun i j f=> huePower P X _ p ha F U t w i j f) (spinprice P X _ p ha K z u g h)
  refine H.congr' ((pads P f p).mono (fun x w=> ?_)); dsimp only
  have e:= bright_bus L D ([]:Receipt.Deck J) [] (realHue Y x.1 (ι x.2) (ν x.2) (X x.1) (Jewel.κFix β x.1)) (covRead q 1 (Staff.u ∘ X x.1) (Staff.spin ∘ X x.1) (Γ x) (ℳ x)) 0 rfl (sPow P.par x.1 A:ℂ); rw [actual_seat]; swap; · exact w
  simp only [List.length_nil,mul_zero,add_zero] at e; exact e

#print axioms pads
#print axioms tariff_limit
end Resolving
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

import Lucent.Wide
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition

open Spine Preparation.Yoke Lucent EmberWind
variable (P:Spine)
local notation "Ξ" => household (P.calibration)
local notation "φ" => P.groundZero 3
local notation "Kₚ" => P.calibration

universe v0
variable {I:Type}[Fintype I]
variable {β:ℕ→ℝ}{R:ℕ→ℝ}{r:ℕ→ℕ}
variable {W:ℕ→I→Staff} {S:Stencil I} {m a:ℕ}{b:ℕ→ℕ}{d:FieldPlan I}

local notation "mu" => P.pillars 3

abbrev soundOf(β R:ℕ→ℝ)(W:ℕ→I→Staff)(b:ℕ→ℕ)(S:Stencil I)(m a:ℕ) :=
  fun s=> riding P.par β (W s) (b s) S s (R s) m a
local notation:max "gong" => soundOf P β R W b S m a
local notation "via" => P.par
variable {B:ℝ}{l:ℕ→ℕ}
lemma songrent (h:DanceCost B R W b l):
    ∀ᶠ s in atTop,P.Wide (gong s) (Lucent.band (W s) (b s)):=by
 filter_upwards [h] with s q
 exact (charter_price _ _ Kₚ _ _ (Chartered (W s) q.paid)).smul _ -- eta

structure Whelk (R:ℕ→ℝ)(r b:ℕ→ℕ)(W:ℕ→I→Staff)(S:Stencil I)(m a:ℕ)(d:FieldPlan I):Prop where
  purse: ∃ B l,DanceCost B R W b l
  song: ∀ᶠ s in atTop,Singing (W s) S
  tier: S.degree m a
  venue: MeasureAt d W R r
  chalk:Dusty d S

-- Whelk P binder omitted? 
variable (U:P.WickAtNative β)(T:Velocity P.par R r)
include U T in
lemma revenue (h:Whelk R r b W S m a d) :
    Tendsto (fun s=>P.E s (Ξ (gong s))) atTop (𝓝 (faq d S)):= by
 obtain ⟨_,_,z⟩:=h.purse; obtain ⟨A,p,q⟩:=DanceCost.collect T z h.song
 exact U p T h.tier q h.chalk h.venue.receipt
include T in
lemma Whelk.chamber(h:Whelk R r b W S m a d): ∀ᶠ n in atTop, Whelk R r b (nightS via r W n) (night S) (m+m) (a+a) (trio via n d):=by
 obtain ⟨B,l,z⟩:=h.purse
 filter_upwards [h.venue.nightwide T,dustBoth (P:=via) h.chalk] with n t e
 exact ⟨⟨_,_,(during T n z).2.2⟩,h.song.mono (fun _ p=>nightSong _ p),nightPay h.tier,t,e⟩
#check @soundOf

local notation "sect" => faq d S
local notation "priceR" n:max => faq (lane P.par n d) (dawn S)
local notation "priceL" n:max => faq (legato P.par n d) (dusk S)
local notation "priceN" n:max => faq (trio P.par n d) (night S)
local notation "planeF" n:max s:max => takeoff P.par.block (soundOf P β R W b S m a s) 3 (disturb r n s)
variable (h:Whelk R r b W S m a d)
include U T h
lemma Whelk.reflectFar : ∀ᶠ n in atTop, priceR n=sect ∧ priceL n=star sect:=by
 obtain ⟨B,l,z⟩:=h.purse
 have ht:= revenue P U T h
 filter_upwards [z.launch T P.calibration.ℓ] with n g
 have e : ∀ᶠ s in atTop,P.E s (Ξ (fluent 3 0 (planeF n s)))=star (P.E s (Ξ (gong s))) ∧ P.E s (Ξ (planeF n s))=P.E s (Ξ (gong s)):=by
   filter_upwards [songrent (β:=β) (m:=m) (a:=a) (S:=S) P z,g] with s t q; exact P.wide_note s _ t q
 have eR : Tendsto (fun s=>P.E s (Ξ (planeF n s))) atTop (𝓝 (priceR n)):=by
   have t: Whelk R r b (frontS via r W n) (dawn S) m a (lane via n d):= ⟨⟨_,_, (during T n z).1⟩, h.song.mono fun _ p=>dawnSong _ p,dawnPay h.tier,h.venue.walk T n,dustRight n h.chalk⟩

   apply (revenue P U T t).congr'
   filter_upwards [z] with s k
   exact congrArg (P.E s ∘ Ξ) (dawnMove S (liftum P.par r n s) (Jewel.κFix β s) (YM.Pressure.temp (Vale.hat P.par.R.L P.par.x s)) (R s) (b s) m a k.day).symm
 have eL:Tendsto (fun s=>P.E s (Ξ (fluent 3 0 (planeF n s)))) atTop (𝓝 (priceL n)):=by
   have t: Whelk R r b (rearS via r W n) (dusk S) m a (legato via n d):= ⟨⟨_,_, (during T n z).2.1⟩,h.song.mono fun _ p=>duskSong _ p,duskPay h.tier,h.venue.behind T n,dustLeft n h.chalk⟩
   apply (revenue P U T t).congr'
   filter_upwards [z] with s k
   exact congrArg (P.E s ∘ Ξ) (duskMove S (liftum P.par r n s) (Jewel.κFix β s) (YM.Pressure.temp (Vale.hat P.par.R.L P.par.x s)) (R s) (b s) m a k.day).symm
 exact ⟨tendsto_nhds_unique eR (ht.congr' (e.mono fun _ e=>e.2.symm)),tendsto_nhds_unique eL (ht.star.congr' (e.mono fun _ e=>e.1.symm))⟩
#check @dawnMove

local notation "Dad" n:max s:max => Ξ (father P.par.block 3 (gong s) (disturb r n s))
lemma Whelk.tempest: ∀ᶠ n in atTop,Tendsto (fun s=>P.E s (Dad n s)-sect*star (P.E s (Ξ (gong s)))-star sect*P.E s (Ξ (gong s))+star sect*sect) atTop (𝓝 (priceN n-star sect * sect)):= by
 obtain ⟨_,_,z⟩:=h.purse
 have g:= revenue P U T h
 filter_upwards [h.chamber P T] with n t
 have e:Tendsto (fun s=>P.E s (Dad n s)) atTop (𝓝 (priceN n)):=by
   apply (revenue P U T t).congr'
   filter_upwards [z] with s k
   exact congrArg (P.E s ∘ Ξ) (nightMove S (Jewel.κFix β s) (YM.Pressure.temp (Vale.hat P.par.R.L P.par.x s)) (R s) (b s) m a _ (disturb r n s) k.day).symm
 have f:= ((e.sub (g.star.const_mul sect)).sub (g.const_mul (star sect))).add_const (star sect * sect)
 convert f using 2 <;> ring

local notation:max "nightword" n:max => faq (trio P.par n d) (night S)
-- far clustering input
structure Wisp (P:Spine)(d:FieldPlan I)(S:Stencil I):Prop where
    flow:Tendsto (fun n=> faq (trio P.par n d) (night S) - faq (legato P.par n d) (dusk S) * faq (lane P.par n d) (dawn S)) atTop (𝓝 0)
#check @nightMove
lemma Whelk.poll (Z:Wisp P d S)(f:ℕ→P.Test)(e:∀ᶠ s in atTop,(f s).val=Ξ (gong s)):
   WakePoll P f sect:=by
 constructor; intro χ p
 obtain ⟨_,_,z⟩:=h.purse
 have hh:∀ᶠ n in atTop,‖nightword n - star sect*sect‖ <χ :=by
    have t:= (Metric.tendsto_nhds.mp Z.flow χ p)
    filter_upwards [t,h.reflectFar P U T] with n u k
    rw [dist_zero_right,k.1,k.2] at u; exact u
 obtain ⟨n,t,p₀,u⟩:= ((z.launch T P.calibration.ℓ).and ((h.tempest P U T).and hh)).exists
 filter_upwards [p₀.norm.eventually (gt_mem_nhds u), t,songrent (β:=β) (m:=m) (a:=a) (S:=S) P z,e] with s ht y a v
 rw [show f s=P.gateK a from Subtype.ext v]; exact lt_of_le_of_lt (P.wide_invoice s _ sect a y) ht

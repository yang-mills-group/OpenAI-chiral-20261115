import Lucent.Swim
import Lucent.Port

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter MeasureTheory
open scoped Topology
open Py Py.Rate LocalLimit Preparation Preparation.Yoke Lucent Jewel EmberWind
universe u
variable (P:Spine) 

def WickAtNative (β:ℕ→ℝ):Prop :=
 ∀{I:Type}[Fintype I] {S:Stencil I} {m a:ℕ} {A:ℝ} {R:ℕ→ℝ} {r b:ℕ→ℕ} {W:ℕ→I→Staff} {d:FieldPlan I},
   0<A → Velocity P.par R r → S.degree m a →
   (∀ᶠ s in atTop, Expense P.par s A S (W s) (b s)) → Dusty d S → OnScale d W R r →
     Tendsto (fun s=> P.E s (rider P.par β P.calibration (W s) (b s) S s (R s) m a))
       atTop (𝓝 (faq d S))

variable {P} {K:P.Register}{M:ℝ}{Mc:ℕ}{f:ℕ→ℕ}{β:ℕ→ℝ}
lemma Port.wick (G:Port.{u} P K M Mc f β):P.WickAtNative β:=by
 intro I _ S m a A R r b W d p v h e k on_
 let D:=max (dues S) (candied S M m a)
 have u:0≤ D:= (dues_pos S).trans (le_max_left ..)

 exact coupon P.run P.law P.history m a R r β S W b v h e k on_ G.pooled (G.wavetable _ D A m a u p) (le_max_left ..) (le_max_right ..)

theorem oratorio (X:TintDemand)(Mc:ℕ):
 ∃ (P: Spine) (K:P.Register) (M:ℝ), ∀ (u:ℕ→ℕ),StrictMono u → ∃ (q:ℕ→ℕ) (β:ℕ→ℝ),
    Port.{u} P K M Mc (u ∘ q) β ∧ StrictMono q ∧ P.WickAtNative β:=by
 obtain ⟨P,K,M,g⟩:=wakeWithAnArmy.{u} X Mc
 refine ⟨P,K,M,fun u h=>?_⟩; obtain ⟨q,w,t,z⟩:= g u h; exact ⟨q,w,z,t,z.wick⟩
#print WickAtNative
#print Port
#print Lucent.AtClinic
#print Lucent.MixedBox
#print Lucent.Velocity
#print Lucent.OnScale
#print Lucent.Expense
#print Lucent.AtClinic
#print oratorio
#check @oratorio
#print axioms oratorio

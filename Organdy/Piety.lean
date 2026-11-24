import Organdy.Amberlight
import Organdy.Obelisk
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry

open Yoke Yoke.Bazaar
open Optic
open Larva (Chip Domaine dint)
open Hookah.Rake
open Pressure Worth BProof
open Papal


def PieCharge(P:Spine)(c:Cuts)(s i k:ℕ):Prop:=
 ∀ W A, aims P c s i k W A→
    ∀ D D':ℕ, Plait (webX (guineas P s)) D→ Plait (webX (guineas P s)) D'→2*D≤D'→
      (premium Optic.argent c.γ)≤ (D:ℝ)^8 * (candles P s i k A (ice _ D)-candles P s i k A (ice _ D'))

structure Pied(P:Spine)(c:Cuts)(s:ℕ):Prop where
 mood:AmberMood P c s
 four:∀ D:ℕ, Plait (webX (guineas P s)) D→ (D:ℝ)^8*lakeZ (guineas P s) ≤ (premium Optic.argent c.γ)/4
 pair:∀ᶠ i in atTop,∀ᶠ k in atTop,PieCharge P c s i k
open Regis
variable {P:Spine}{c:Cuts}
lemma piety {v:ℝ} (y:c.legacy P)
 (Z:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s≤P.run.uv k→ ShelterCost v P.run s i k):
 ∀ᶠ s in atTop,Pied P c s:=by

 let R:=P.par
 have d:=y.2.2.1
 obtain ⟨u,ux,ul⟩:=giltEdge R.K.top.clip R.V.W.parcel c.cost R.K.width (one_pos.trans_le R.V.up) d

 have f:=premium_pos argent_pos d
 have h:=turnover R
 filter_upwards [
   moods y Z,
   h.eventually (aisleWide u),h.eventually (oceania (_/4) (div_pos f (by norm_num)))]
     with s g t q
 refine ⟨g,q,?_⟩
 have p':=g.plus
 have hy:((shaft P s+6:ℕ):ℝ) ≤ (webX (guineas P s)) :=by
    have l:(shaft P s:ℝ)+20≤(webX (guineas P s)):=t.depth
    push_cast
    linarith only [l]
 filter_upwards [spreadEven P.run s (webX (guineas P s)) u (one_pos.trans_le ux)] with i r
 filter_upwards [ferry_later P.run s i] with k e W A J D D' hx hy' p
 have ev:Even (More ((kitGap P s i))).val:= ⟨_,(mul_two ((kitGap P s i)).val)⟩
 let n:=P.run.uv k - s
 have z:=R.V.L.roof n
 obtain ⟨_,_,_,v',_⟩:=Papal.prices_plot P.run s i k e.enters
 let ρ:=Real.sqrt (guineas P s)* Next.SectorChange.coupling (RootBook P.run i k s).beta
 have a':1/2≤|ρ| ∧ |ρ|≤2:=by
   have a:1/2≤ρ ∧ ρ≤2:=Head.Etch.railB v'.1 v'.2 p'
   rw [abs_of_pos ((by norm_num : (0:ℝ)<1/2).trans_le a.1)];exact a

 have e1:=ul _ _ t.gw t.veil _ ev r D _ hx hy
     z.1 (z.2.1 _) (z.2.2 _) (R.V.L.tied n) (R.V.L.mood n) ρ a'.1 a'.2 _ J.1.purse J.1.inside J.2
 have e2:=ul _ _ t.gw t.veil _ ev r D' _ hy' hy
     z.1 (z.2.1 _) (z.2.2 _) (R.V.L.tied n) (R.V.L.mood n) ρ a'.1 a'.2 _ J.1.purse J.1.inside J.2
 have a:= march hx (ux.trans t.gw) -- fix
 exact reducegap e1 e2 f a.2 (by exact_mod_cast p)
#print axioms piety



variable {s:ℕ}
local notation "H" => P.calibration
local notation "gu" => guineas P s
local notation "w✽" => webX (gu)
local notation "g'" => (shaft P s+6)
local notation "A'" => premium argent c.γ
local notation "ℰ"=> meterC (gu)
local notation "h'"=> knock (gu)
local notation "S'"=> station P s

local notation "w✤" => walkF (gu)
local notation "ε₁" => yieldt (gu)


variable {I:Type}{u:Ultrafilter I}{d:Stores}{i k:I→ℕ}
 {X:Suits P s i}{F:PackE I P}{x:Lot P}
local notation "uf" => (↑u:Filter I)
local notation "W" => raw P s i k X
local notation "G'" => (∀v,Treasure (tunnel P s i v))

variable (p:Parade (↑u:Filter I) P c d s i k X F x)
 (m:Pied P c s)

include m p
lemma biplane
 (Z:P.Register)(z:P.Test)(h:z.val=x .horn)(r r':ℕ)
 (e:Plait w✽ (2*r))(f:Plait w✽ (2*r'))(v:2*(2*r)≤2*r')(j:Axis)(w:P.Spectrum0 j):
 A'/2 ≤ (planted r)^8 * (glitz P z w s r gu - glitz P z w s r' gu):=by
 obtain ⟨A,q⟩:=p.review
 obtain ⟨J,t⟩:=highs (u:=u) q
 rw [planted_eq]
 obtain ⟨a,b⟩:=t (2*r)
 obtain ⟨a₁,b₁⟩:=t (2*r')

 have p₁:=sees_light m.mood p q Z z h w e b a
 have p₂:=sees_light m.mood p q Z z h w f b₁ a₁
 have p₃:=m.four _ e
 let y:=((2*r:ℕ):ℝ)
 have p₄:=mul_le_mul_of_nonneg_left (abs_le.mp p₁).1 (by positivity:0≤y^8)
 have p₅:=mul_le_mul_of_nonneg_left (abs_le.mp p₂).2 (by positivity:0≤y^8)
 have d₁:A' ≤ y^8 * (J (2*r)-J (2*r')) :=

    ge_of_tendsto ((b.sub b₁).const_mul (y^8))
      ((p.rate.both m.pair).mono fun n h=>h _ _ (q n) _ _ e f v)
 linarith only [p₄,p₅,d₁,p₃]
/-- Equivalent scaling, *two* glitzes incl arbitrary coarser fat. -/
lemma biplanar
 (Z:P.Register)(z:P.Test)(h:z.val=x .horn)(r r':ℕ)
 (e:reach gu r)(f:Plait w✽ (2*r'))(t:2*r≤r')
 (j:Axis)(w:P.Spectrum0 j)(a β:ℝ)(b:gu/2≤β):
 gleamδ c.γ * (a/(β* distanceP r^4))^2 ≤
   glitz P z w s r a - glitz P z w s r' a:=by
 obtain ⟨v,n⟩:=planted_plait m.mood r e
 have h:=biplane p m Z z h r r' n f (by omega) j w
 have y:=m.mood.plus
 rw [show a=a/gu*gu from (div_mul_cancel₀ a y.ne').symm,
    fraction_glitz, fraction_glitz, div_mul_cancel₀ a y.ne']
 have g:0<planted r:=by unfold planted;positivity
 apply (mul_le_mul_iff_left₀ (pow_pos g 8)).mp
 exact (equalBudget y m.mood.γpos b v).trans ((mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq
    (by ring))

#print axioms biplanar

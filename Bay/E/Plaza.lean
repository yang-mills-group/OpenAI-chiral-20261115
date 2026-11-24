import Bay.E.Match
import Bay.D.Laneway

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell


namespace Silk
open Buffered Lifted D StressExchange

open Buffered.Afterglow.Tower SlabMark
open Girt
open scoped YM.CF.Buffered

local notation "Ways" => Buffered.Family

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow Journey Tower Tapestry VacuumSelection
local notation "VΩ"=>VacuumSelection.Spine
set_option maxRecDepth 5000

open Pressure Vale
variable (P:VΩ)(A:Armor)(s:ℕ)
local notation "Ω"=>D.scale P s
local notation "BΩ"=>radiusB Ω
local notation "τ"=>Pressure.temp Ω
local notation "qX"=>qSet P s
local notation "K"=>P.calibration
local notation "ox"=>nodeC corner
local notation "Band₀"=>Band ox BΩ


variable {i k:ℕ→ℕ}
abbrev oilS:=Silo Axis (nodeC corner) (radiusB (D.scale P s))
def Dress(v:ℕ → oilS P s)(f:oilS P s):Prop:=Hangs τ P.par.d A.b v f
def PaintTest(f:oilS P s):Prop:=Neutral K (nips K f) ∧ ∀a,Neutral K (wing K f a)
abbrev onButton(r:ℕ)(X:Diadem (port P s i k r)):=
 Button (port P s i k r) X.f A.b τ P.par.d corner BΩ
abbrev ownSticker(r:ℕ)(X:Diadem (port P s i k r)):oilS P s := sticker _ corner X.f BΩ

def Faded (T:Mission P s i k) (φ:ℕ→ℕ):Prop:=
  ∃x:ℕ → oilS P s,∃f:oilS P s,Hangs τ P.par.d A.b x f∧(∀n,PaintTest P s (x n))∧∀ᶠ r:ℕ in atTop, onButton P A s (φ r) (T (φ r)) ∧
        x r =ownSticker P s (φ r) (T (φ r))


variable {P A s} {T:Mission P s i k}{φ ψ:ℕ→ℕ}

lemma peelThin (p:Faded P A s T φ)(v:Retains φ ψ) :
 Faded P A s T ψ:=by
 obtain ⟨x,f,xh,d,h⟩:=p
 obtain ⟨w,u,e⟩:=v
 have g: Hangs τ P.par.d A.b (x ∘ w) f:=by
   refine ⟨fun _ _=>xh.owns ..,xh.lands,fun i=>Metric.tendstoUniformly_iff.mpr fun ε d=>?_⟩
   exact u.eventually (Metric.tendstoUniformly_iff.mp (xh.earns i) _ d)
 refine ⟨_,_,g,(fun n=>d _),?_⟩
 filter_upwards[e,u.eventually h] with j u v
 rw [←u];exact v

lemma owned (p:NamedCrew P s i k A T)(g:Row P i k):
 ∀ᶠr in atTop,onButton P A s r (T r):=by
 filter_upwards [((Journey.momentum P.run s).comp g.growing).eventually (separates K Band₀),p] with r e v
 apply quilt v.cradle v.swell.1 v.cradle.sizeB rfl rfl
 change AtEase Band₀ (P.par.Ctor (P.run.ir (i r)) s)
 exact (Journey.terrain P.run P.large (P.run.ir (i r)) s) ▸ (show AtEase Band₀ (P.calibration.c (momentm P.run (i r) s)) from e)

lemma doubleZ (g:Row P i k)(p:NamedCrew P s i k A T)(v:StrictMono φ):
 ∃ζ:ℕ→ℕ,StrictMono ζ∧ Stills P s A T (φ ∘ ζ)∧Faded P A s T (φ ∘ ζ):=by
 obtain ⟨ψ,b,w⟩:=friezes g p v
 let h:= ((v.comp b).tendsto_atTop.eventually (owned p g))
 obtain ⟨l,d⟩:=eventually_atTop.mp h
 let z(r):= φ (ψ (l+r))
 let f(r:ℕ):=ownSticker P s (z r) (T (z r))
 have pay(r):∀i,SilkPay ox BΩ τ P.par.d A.b (f r i):=(d _ (Nat.le_add_right _ r)).pay
 obtain ⟨ξ,q',a,t⟩:=hangar (r:=f) pay
 let j:=fun n=>l+ξ n
 have y: StrictMono j:= fun _ _ h=>Nat.add_lt_add_left (q' h) l
 refine ⟨ψ∘j, b.comp y,w.thin ⟨j,y.tendsto_atTop,EventuallyEq.refl _ _⟩,?_⟩ -- syntax
 refine ⟨_,_,t,(fun i=>⟨(d _ (Nat.le_add_right l (ξ i))).hue,(d _ (Nat.le_add_right l (ξ i))).holds⟩),?_⟩
 exact Eventually.of_forall fun i=>⟨d _ (Nat.le_add_right l (ξ i)),rfl⟩
variable (P A) 
open GrainDiag (Stairs slash carries rises)
-- common diagonal for all paid
variable (i k)
lemma doublon (d:Row P i k) (T:(s:ℕ)→Mission P s i k):
 ∃ψ, StrictMono ψ∧∀s,NamedCrew P s i k A (T s)→
      Stills P s A (T s) ψ ∧ Faded P A s (T s) ψ:=by
 let B(n):=fun ψ=>NamedCrew P n i k A (T n)→
      Stills P n A (T n) ψ∧ Faded P A n (T n) ψ
 have p(n:ℕ)(φ:SetRoll):∃ q:SetRoll,B n (φ ∘ q):=by
    by_cases e:NamedCrew P n i k A (T n)
    · obtain ⟨v,t,x⟩:=doubleZ d e φ.2
      exact ⟨⟨v,t⟩,fun _=>x⟩
    exact ⟨⟨id,strictMono_id⟩,fun z=>False.elim (e z)⟩
 choose q h using p
 let D:Stairs:=Nat.rec (motive:=fun _=>SetRoll) ⟨id,strictMono_id⟩
     (fun n p=>⟨p ∘ q n p,p.2.comp (q n p).2⟩)
 have a:GrainDiag.More D:=fun n=>⟨_,(q n (D n)).2,rfl⟩
 exact ⟨slash D,rises _ a,fun s e=> ⟨((h s (D s) e).1).thin (carries D a (s+1)),peelThin (h s (D s) e).2 (carries D a (s+1))⟩⟩
end YM.CF.Bay.Silk

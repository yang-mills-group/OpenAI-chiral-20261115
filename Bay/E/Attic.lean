import Bay.E.Plaza

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
local notation "QΩ"=>qSet P s
local notation "K"=>P.calibration
local notation "ox"=>nodeC corner
local notation "Band₀"=>Band ox BΩ


variable (i k:ℕ→ℕ)
def Relic:Prop:=
 ∃u:Setpiece P A s i k,Faded P A s u.t id
def PortDual:Prop:=
 ∃i k:ℕ→ℕ,Roadie P i k ∧∀ᶠs:ℕ in atTop,Relic P A s i k

variable {P A s i k} {x:Mission P s i k}{ψ:ℕ→ℕ}
lemma salvage (p: Stills P s A x ψ)(v:Faded P A s x ψ)
    (h:StrictMono ψ)(g:NamedCrew P s i k A x):
 Relic P A s (i∘ψ) (k∘ψ):=by
 obtain ⟨⟨b,r⟩,⟨a,y⟩,w,l⟩:=p
 exact ⟨⟨fun n=>x (ψ n), h.tendsto_atTop.eventually g, w,l,b,r,a,y⟩,v⟩
theorem dual (d:Armor.Strong P A):PortDual P A:=by
 obtain ⟨t,e⟩:=spot P
 obtain ⟨q,g,u⟩:= doublon P A _ _ e.rowing (fun _ _=>strikes _ A)
 refine ⟨_,_,e.opens g,?_⟩
 filter_upwards [e.ready A d] with s b
 exact salvage (u s b).1 (u s b).2 g b


variable {U:Mission P s i k}
variable {l:ℕ → oilS P s}{f:oilS P s}
local notation "w" n:max => port P s i k n
abbrev mintTag (T:Silo Axis (nodeC corner) (radiusB (D.scale P s))) :=yieldY K QΩ τ T

-- slots with any such observers: convergence for actual matching, NOT a
-- bound on the limiting modulo fee through Reg-Schur.
abbrev openY(n:ℕ)(a:Diadem (w n)):= orderMark _ ((w n).Y128 (centerC (w n)) a.f (tabW P))
lemma echoY (d:Row P i k)
 (h:Hangs τ P.par.d A.b l f)
 (v:∀ᶠn in atTop, onButton P A s n (U n) ∧ l n= ownSticker P s n (U n))
 {C:Finset Cover}{F:ℕ→ Ways K}{G:Ways K}(t:BQueue C F G):
 Tendsto (fun n=>Journey.compass P.run (i n) (k n) s
   (openY n (U n)* instrument (w n) (F n))) atTop
    (𝓝 (P.E s (mintTag f*G))):=by
 have z:=quickens P s d (((yieldsX K QΩ τ h).2.2).multiply t)
 apply z.congr'
 filter_upwards[v] with n b

 have e: instrument (w n) (mintTag (l n))=openY n (U n):=
    (congrArg (fun x=>instrument (w n) (mintTag (P:=P) (s:=s) x)) b.2).trans (matchesWing b.1)
 exact (actualRead _ _ _ _ _ _).trans (congrArg (Journey.compass _ _ _ _)
            ((actual_product _ _ _ _ _ _).trans (congrArg (fun x=>x* instrument (w n) (F n)) e)))

end YM.CF.Bay.Silk

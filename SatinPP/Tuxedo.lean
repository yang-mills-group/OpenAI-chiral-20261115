
import SatinPP.Applause
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Set MeasureTheory
open Silk OS OS.Semigroup Spectral Boundary Probe Hierarchy.Seld
open YM.Quays YM.SatinJets
open scoped Topology Matrix BigOperators InnerProductSpace NNReal ContDiff
open Ballad DoseTravel -- check Lean
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "G"=> P.ManyF 3 (P.advocate 3 x 3)
local notation "π'"=>P.wealth 3 (P.advocate 3 x 3)
local notation "η"=>P.enter 3 (P.advocate 3 x 3)
local notation "ε"=>P.seasons 3 (P.advocate 3 x 3)
local notation "E"=> (P.seasons 3 (P.advocate 3 x 3)).E
local notation "Ω"=>P.heaven 3 (P.advocate 3 x 3)
local notation "Γ"=>P.cartage 3 (P.advocate 3 x 3)
local notation "ℜ"=> Lead.Clan 
variable (w:ℜ→Prism)(V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
variable (D:P.Concert x)
local notation "X'"=> P.headliner x D w

local notation "Ω'"=>P.occupant x

variable (A:ℕ→P.Apron)(Y:ℜ→Spool (P.ManyF 3 (P.advocate 3 x 3)))
local notation "λ₁"=>P.flare1 x Y
local notation "λ₂"=>P.flare2 x Y
local notation "V₁"=>P.leaderW x w D
local notation "V₂"=>P.laterW x w D
local notation "S'"=>P.scoreW x Y
variable {P x Y w V D A}(r:Played P x w V D A Y)
variable {F U:SampleDose} {l u q t μ:ℝ}

-- index sold consultations i,t
variable {c s n:ℕ→ℕ}{X:P.HandleWith x c s A n}

variable {g k i₀:ℕ}{K:P.Register}(J:P.Ellis 3 x)
variable (R:P.FullPrismLab x A c s n w V g k X 1 F U reviewEarlierBox reviewLaterBox (c i₀) (s i₀) K)

-- CP18 full disclosure lab fitted exactly
abbrev PrimePlay (P:Spine)(x:P.Spectrum0 3)(w:ℜ→ Prism)
   (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
   (A:ℕ→P.Apron) (c s n:ℕ→ℕ)
   (Y:ℜ→Spool (P.ManyF 3 (P.advocate 3 x 3))) (F U:SampleDose):Prop :=
   P.Encore x w V A Y F U (-2) (-1) 1 2 1 c s n

include R in
lemma day :Agenda 1 F U (-2) (-1) 1 2:=by
 have H:Strict (-2) (-1) F:=fun _ h=>R.keeps.earlier h 3 (mem_univ _)
 have I:Strict 1 2 U:=fun _ h=>R.keeps.laterProbe h 3 (mem_univ _)
 exact ⟨zero_lt_one, fun p h=> (by linarith only [(H p h).2]),
     fun p h=>(I p h).1.le,by norm_num,zero_le_one,by norm_num,H,I⟩


variable (P x Y F U)
def InteractionW : Prop :=
  -- Wick one original sure positive
  (∃d,0<d∧LoudMargin (S' F U (-2) (-1) 1 2 1) d) ∧
  -- ordered REAL loud sometimes, in ANY open interval
  ∀ a b:ℝ,0≤a→a<b→∃ t∈Ioo a b, ∃ g:0<t, ∃d,0<d∧LoudMargin
      (P.MinkAnswer x Y (puffup F g) (puffup U g)) d
variable {P x Y F U}

include R J r
lemma curtain :
   P.PrimePlay x w V A c s n Y F U ∧ P.InteractionW x Y F U:=by
 let y:=encore r (day R) J R.armada
 refine ⟨y,?_,fun a b h q=>?_⟩
 · rw [y.one]
   exact loud_choose _ R.all_six
 obtain ⟨z,i,h,p⟩:=y.rank R.all_six h q
 exact ⟨z,i,h,loud_choose _ p⟩
#check curtain
#print InteractionW


/-- Encore: same unpack, choose and expose ACTUAL PROGRAMS,
actual release on this vacancy (occupied) etc. -/
def Gala: Invoice:=fun P _ c s x _ _ F U A n w V g k _ =>
   Attested P x g k A ∧ ∃ D Y,
     P.Played x w V D A Y ∧ P.PrimePlay x w V A c s n Y F U ∧ P.InteractionW x Y F U

omit J r R

theorem gala: Affirmed Gala:=by
 obtain ⟨P,K,c,s,x,R,i₀,F,U,beta,e,y,nf,nu,bf,bu,h,t,A,n,w,V,g,k,X,
   ⟨z,D,M⟩,p,b,j,a⟩:=sold_out
 obtain ⟨Y,r⟩:=played_exist P x w V D A M
 exact ⟨P,K,c,s,x,R,i₀,F,U,beta,e,y,nf,nu,bf,bu,h,t,A,n,w,V,g,k,X,
   ⟨z,D,Y,r,curtain r R p⟩, p,b,j,a⟩

#print Gala
#print axioms gala
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

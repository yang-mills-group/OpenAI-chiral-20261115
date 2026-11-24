
import SatinPP.Airplay
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

local notation "ρ"=> (P.occupant x).y
variable (P x Y F U)
def MinkF(a:ℜ):Bench (ε)→ₗ[ℂ]Bench (ε):=
   (Y a).dual.Mink (ε) (puff F)
def MinkU(a:ℜ):Bench (ε)→ₗ[ℂ]Bench (ε):=
   (Y a).Mink (ε) (puff U)
def MinkAnswer:CrossRead:=Matrix.of (fun a b=>
   inner ℂ (Ω) (P.MinkF x Y F a (P.MinkU x Y U b (ρ))).val)
local notation "M₁"=>P.MinkF x Y
local notation "M₂"=>P.MinkU x Y

variable {P x Y F U}(e:Agenda μ F U l u q t)
variable {g k:ℕ}(J:P.Ellis 3 x)(B:P.ThinArmada x A c s n w X V g k)
include e
lemma score_broadcast {d:ℝ}(h:0<d):
   S' F U l u q t (sideways d)=P.MinkAnswer x Y (puffup F h) (puffup U h):=by
  ext1 a b
  simp only [MinkAnswer,scoreW,Matrix.of_apply,MinkF,MinkU,puffup_ok]
  exact pair_mink _ _ _ _ _ _ _ _ _ _ (bandp e.strict) (bandp e.widen) h


include r J B
lemma lone_broadcast {d:ℝ}(h:0<d)(a:ℜ):
   inner ℂ (Ω) (M₁ (puffup F h) a (ρ)).val=0 ∧
   inner ℂ (Ω) (M₂ (puffup U h) a (ρ)).val=0:=by
 have k':= lone_shell r J B e a (sideways d) (sideways_sheath h)
 rw [flare1,flare2,solo_mink _ _ _ _ _ _ (bandp e.strict) h,solo_mink _ _ _ _ _ _ (bandp e.widen) h] at k'
 unfold MinkF MinkU
 rw [puffup_ok,puffup_ok]
 exact k'

omit r J B
lemma recover_eu {N:TableW}(p:Sea N) {a b:ℝ}(h:0≤a)(f:a<b)
   (v:∀ d:ℝ, d∈Ioo a b→∀ g:0<d,N (sideways d)=P.MinkAnswer x Y (puffup F g) (puffup U g)):
   EqOn N (S' F U l u q t) sheath:=by
 intro z Z; ext1 i j
 have y:Harbor (fun z=>N z i j-S' F U l u q t z i j):=
    (p i j).sub (score_harbors e i j)
 exact sub_eq_zero.mp (vanish_seam y h f (fun d w=>by
    have k:=h.trans_lt w.1
    rw [score_broadcast e k,v _ w k,sub_self]) Z)
include r

lemma deliver (p:ReadsSix (P.readPrism x V w μ F U))
    {a b:ℝ}(h:0≤a)(f:a<b):
 ∃ d∈Ioo a b, ∃ g:0<d, ReadsSix (P.MinkAnswer x Y (puffup F g) (puffup U g)):=by
 rw [←score_value r e] at p
 obtain ⟨d,w,y⟩:=Harbor.flare (score_harbors e) p h f
 refine ⟨d,w,h.trans_lt w.1,?_⟩
 rw [←score_broadcast e]; exact y

#print axioms deliver


omit e r
variable (P x w V Y A c s n F U μ l u q t)
local notation "put"=>P.Screen w A c s n F U
/-- Wick Program releases. Panel lengths true u-l, t-q. Agenda forces
gap q-u positive. Paired applies pressure there, no other heat inserted
(unused support clearance, not extension of panel). -/
structure Encore:Prop where
 ready : Agenda μ F U l u q t
 -- continuation OF CONSULTATIONS, actual credit
 analytic : put (P.trueScan x) (S' F U l u q t)
 one : S' F U l u q t 1=P.readPrism x V w μ F U
 posed (b:ℝ)(d:0<b):
   S' F U l u q t b=P.readPrism x V w (b*μ) (puffup F d) (puffup U d)
 sea_of_opponents(W:P.Canvas)(h:IsOpponent P W): put W 0
 opp_is:IsOpponent P (P.splitScan x)
 only(W:P.Canvas){M N:TableW}(h:put W M)(g:put W N):EqOn M N sheath
 centered(a:ℜ)(z:ℂ)(p:z∈sheath):
   λ₁ F l u a z=0 ∧ λ₂ U q t a z=0
 local_curve(d:ℝ)(g:0<d):
   S' F U l u q t (sideways d)=P.MinkAnswer x Y (puffup F g) (puffup U g)
 local_zero(d:ℝ)(g:0<d)(a:ℜ):
   inner ℂ (Ω) (M₁ (puffup F g) a (ρ)).val=0 ∧
   inner ℂ (Ω) (M₂ (puffup U g) a (ρ)).val=0


 -- even pins the full table from unpadded Mink products on ANY positive interval.
 by_edge (N:TableW)(p:Sea N) {a b:ℝ}(h:0≤a)(f:a<b)
   (v:∀ d:ℝ, d∈Ioo a b→∀ g:0<d,N (sideways d)=P.MinkAnswer x Y (puffup F g) (puffup U g)):
        EqOn N (S' F U l u q t) sheath
 rank(p:ReadsSix (P.readPrism x V w μ F U))
    {a b:ℝ}(h:0≤a)(f:a<b):
   ∃ d∈Ioo a b, ∃ g:0<d, ReadsSix (P.MinkAnswer x Y (puffup F g) (puffup U g))
variable {P x w V Y A c s n F U μ l u q t}
#check Encore
#check Screen.score


include e r J B
lemma encore :
 P.Encore x w V A Y F U l u q t μ c s n:=
 ⟨e,Screen.score r J B e,score_value r e, fun _=>spin r e,
   fun _=>Screen.nullify J B e,split_opposes,
   fun _ _ _=>Screen.identify, lone_shell r J B e,
   fun _=>score_broadcast e,fun _=>lone_broadcast r e J B,
   fun _=>recover_eu e, deliver r e⟩
#print axioms encore
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

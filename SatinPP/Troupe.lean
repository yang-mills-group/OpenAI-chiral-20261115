
import SatinPP.Breezy
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 1100000
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


variable (A:ℕ→P.Apron)(Y:ℜ→Spool (P.ManyF 3 (P.advocate 3 x 3)))

/- instantaneous prices represented on Bench and Spool. In the other (earlier)
role use the adjoint mark, WITHOUT reversing the positions of the test;
under order its REFLECTED vacuum ket corresponds to F. -/
structure Played : Prop where
 m : Matinee P x D V A w
 tick (a:ℜ): (Y a).Token (ε) (X' a)

lemma played_exist (m: Matinee P x D V A w):∃ Z, Played P x w V D A Z:=by
 have h(a):∃ t:Spool (G), t.Token (ε) (X' a):=by
   obtain ⟨n,c,r⟩:=m.pp a
   obtain ⟨B,h⟩:=role_exists _ r
   exact ⟨⟨n+1,B⟩,h⟩
 choose t s using h
 exact ⟨t,m,s⟩

lemma Played.back (p:Played P x w V D A Y) (a:ℜ):
   (Y a).dual.Token (ε) (Turn (X' a)):= (p.tick a).turn

-- programs early/late
local notation "Ω'"=>P.occupant x
def flare1 (F:SampleDose)(l u:ℝ)(a:ℜ):ℂ→ℂ:=solo (ε) (Ω') (Y a).dual (puff F) l u
def flare2 (U:SampleDose)(l u:ℝ)(a:ℜ):ℂ→ℂ:=solo (ε) (Ω') (Y a) (puff U) l u


def scoreW (F U :SampleDose)(l u q t:ℝ)(z:ℂ):CrossRead :=
   Matrix.of (fun a b=>Silk.pair (ε) (Ω') (Y a).dual (puff F) l u
                                    (Y b) (puff U) q t z)

local notation "λ₁"=>P.flare1 x Y
local notation "λ₂"=>P.flare2 x Y
local notation "V₁"=>P.leaderW x w D
local notation "V₂"=>P.laterW x w D


local notation "S'"=>P.scoreW x Y
variable {P x Y w V D A}(r:Played P x w V D A Y)
variable {F U:SampleDose} {l u q t μ:ℝ}

-- index sold consultations i,t
variable {c s n:ℕ→ℕ}{X:P.HandleWith x c s A n}

structure Agenda (μ:ℝ)(F U:SampleDose)(l u q t:ℝ):Prop where
 cash : 0<μ
 ago : backwardSite F μ
 soon : forwardSite U μ
 L:u≤0
 R:0≤q
 sep:u<q
 strict:Strict l u F
 widen:Strict q t U

variable (e:Agenda μ F U l u q t)(a b:ℜ)
variable (W:P.AuthorizedPair x A c s n w V X μ F U)

-- scoreW at 1
include e r
lemma score_value :
 S' F U l u q t 1=P.readPrism x V w μ F U:=by
 ext1 a b
 unfold scoreW
 rw [Matrix.of_apply, Silk.pair_eu (ε) (Ω') l u q t (puff F) (puff U)
    ((Y a).dual) (Y b) (r.m.pp' a) (r.m.pp b) (Played.back _ _ _ _ _ _ _ r a) (r.tick _) (bandp e.strict) (bandp e.widen)]
 change inner ℂ (Ω) (V₁ a F l u
     (E (q-u).toNNReal (V₂ b U q t (Ω))))=
    inner ℂ (DoseTravel.beam (G) F (P.earlierProfile x V w μ a))
    (DoseTravel.beam (G) U (P.laterProfile x V w μ b))


 rw [←matIn r.m U b e.widen e.soon e.R,←matOut r.m F a e.strict e.ago e.L]
 have h : (q-u).toNNReal=(-u).toNNReal+q.toNNReal:=by
    rw [← Real.toNNReal_add (neg_nonneg.mpr e.L) e.R,add_comm,sub_eq_add_neg]

 rw [← ContinuousLinearMap.adjoint_inner_left,h, (ε).time,ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_left,(ε).sym];rfl

include W
lemma lone_value :
 (λ₁ F l u a 1 = 0) ∧ (λ₂ U q t a 1=0):=by
  have g:= W.centered a
  rw [←matOut r.m F a e.strict e.ago e.L,
      ←matIn r.m U a e.widen e.soon e.R] at g
  have d(v:ℝ≥0)(y:G): inner ℂ (Ω) (E v y)=inner ℂ (Ω) y:=by
      rw [←ContinuousLinearMap.adjoint_inner_left,(ε).sym,P.heaven_hot]
  rw [d,d,show ∀z:G, star (inner ℂ (Ω) z)=inner ℂ z (Ω) from fun z=> inner_conj_symm ..,
      ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left] at g
  unfold flare1 flare2
  rw [solo_eu _ _ _ _ _ _ (r.m.pp' a) (Played.back _ _ _ _ _ _ _ r a)
       (bandp e.strict),solo_eu _ _ _ _ _ _ (r.m.pp a) (r.tick a) (bandp e.widen)]
  exact g

#print axioms lone_value
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

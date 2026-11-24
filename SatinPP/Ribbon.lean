import SatinPP.Awning
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk
open Quays
open Function Filter Metric Set OS OS.Semigroup Hierarchy.Seld Complex MeasureTheory
open Spectral Boundary Probe
open scoped Topology BigOperators NNReal InnerProductSpace

variable {H:Hilbert} {a:Axis}

variable (S:OS.Semigroup H a)(A:H.Op)(p:Commute A (saucer S))

local notation "M"=>park S A (autumn S A p)
lemma road_park {Y:ℂ→Bench S}(h:Road S Y):
  Road S (fun z=> M (Y z)):=by
 intro n
 refine ((h n).pass A).use (fun z he=>?_)

 exact park_κ S n _ A A _ (p.pow_right n)

variable (w:Sleeper S)(l u:ℝ)(g f:Test4)(P Q:Spool H)
def ribbon (z:ℂ):ℂ:=
 inner ℂ w.y.val (P.WickPath S g l 0 z
           (M (Q.WickPath S f 0 u z w.y))).val
lemma ribbon_harbor (r:Band a l 0 g)(s:Band a 0 u f):
  Harbor (ribbon S A p w l u g f P Q):=
 ((Wick_harbor S l 0 P.cell r P.d (road_park S A p
   (Wick_harbor S 0 u Q.cell s Q.d (road_const S w.y)))).under).pass (innerSL ℂ w.y.val)
lemma ribbon_mink (r:Band a l 0 g)(s:Band a 0 u f){b:ℝ}(h:0<b):
 ribbon S A p w l u g f P Q (sideways b)=
   inner ℂ w.y.val (P.Mink S (rev a h g) (M (Q.Mink S (rev a h f) w.y))).val:=by
 unfold ribbon Spool.WickPath
 simp only [Wick_edge S l 0 P.cell r P.d h,Wick_edge S 0 u Q.cell s Q.d h,LinearMap.comp_apply,border_vac,w_border,
    neg_zero,zero_mul];simp only [Spool.Mink,border,zero_smul,uh_zero] -- ?border_vac

variable {X D:Stamp H}(T:∃ m c,Paid S m c X)(C:∃ m c,Paid S m c D)
 (x:P.Token S X)(y:Q.Token S D)
include x T y C
lemma ribbon_eu (r:Band a l 0 g)(s:Band a 0 u f):
 ribbon S A p w l u g f P Q 1=
    inner ℂ w.y.val (voyage S X l 0 1 g (A (voyage S D 0 u 1 f w.y.val))):=by
 unfold ribbon Spool.WickPath;obtain ⟨_,_,c⟩:=T; obtain ⟨_,_,d⟩:=C
 rw [opens c r eu x,←opens d s eu y];rfl

#print axioms ribbon_mink
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk

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


variable (P x Y F U)
variable (Q:(P.ManyF 3 (P.advocate 3 x 3)).Op)(h:Feather (P.seasons 3 (P.advocate 3 x 3)) Q)
include h in
lemma feathery:Commute Q (saucer (ε)):=by
 obtain ⟨t,p,_⟩:=h.leaves
 exact (ship_left (ε) Q fun z=>(Roy.costT (ε) z).jointly p).symm
-- actual multiplication of Q between, on Bench
abbrev fanOut (Q:(G).Op)(h:Feather (ε) Q) :Bench (ε) →ₗ[ℂ]Bench (ε):= park (ε) Q (autumn (ε) Q (P.feathery x Q h))

def timeLike (Y:ℜ→Spool (G))(F U:SampleDose)(Q:(G).Op)(h:Feather (ε) Q):TableW:=fun z=> Matrix.of (fun i j=>
 Silk.ribbon (ε) Q (P.feathery x Q h) (Ω') (-2) 2 (puff F) (puff U)
    (Y i).dual (Y j) z)

/-- Literal MinkAnswer, with Q resolving in-between momentum. -/
def MinkSplay (Y:ℜ→Spool (G))(F U:SampleDose)(Q:(G).Op)(h:Feather (ε) Q):CrossRead:=Matrix.of (fun a b=>
   inner ℂ (Ω) (P.MinkF x Y F a (P.fanOut x Q h (P.MinkU x Y U b (Ω').y))).val)

variable {P x Y F U Q} (e:Agenda 1 F U (-2) (-1) 1 2)
local notation "Tl"=>P.timeLike x Y F U Q h

include e

lemma moreF:Strict (-2) 0 F:= fun _ t=> ⟨(e.strict _ t).1,lt_trans (e.strict _ t).2 (by norm_num)⟩
lemma moreU:Strict 0 2 U:=fun _ t=> ⟨lt_trans zero_lt_one (e.widen _ t).1,(e.widen _ t).2⟩

lemma feathSea:Sea (Tl) := fun a b=>
 ribbon_harbor (ε) Q (P.feathery x Q h) (Ω') (-2) 2 (puff F) (puff U) (Y a).dual (Y b) (bandp (moreF e)) (bandp (moreU e))
lemma feathMink{d:ℝ}(u:0<d):
 Tl (sideways d)= P.MinkSplay x Y (puffup F u) (puffup U u) Q h:=by
 ext1 a b
 simp only [MinkSplay,timeLike,Matrix.of_apply,MinkF,MinkU,puffup_ok,fanOut]
 exact ribbon_mink _ _ _ _ _ _ _ _ _ _ (bandp (moreF e)) (bandp (moreU e)) u
include r in
lemma feathVelvet :
 Tl 1= oneBox (P.wave x V w false 1 F) (P.wave x V w true 1 U) Q:=by
 ext1 a b
 simp only [oneBox,timeLike,Matrix.of_apply]
 rw [ribbon_eu _ _ _ _ _ _ _ _ _ _ (r.m.pp' a) (r.m.pp b) (Played.back _ _ _ _ _ _ _ r a) (r.tick _) (bandp (moreF e)) (bandp (moreU e))]
 change inner ℂ (Ω) (V₁ a F (-2) 0 (Q (V₂ b U 0 2 (Ω))))=
    inner ℂ (DoseTravel.beam (G) F (P.earlierProfile x V w 1 a))
    (Q (DoseTravel.beam (G) U (P.laterProfile x V w 1 b)))
 rw [←matIn r.m U b (moreU e) e.soon le_rfl,←matOut r.m F a (moreF e) e.ago le_rfl,
    ← ContinuousLinearMap.adjoint_inner_left,neg_zero,Real.toNNReal_zero,(ε).eZero]
 rfl

omit e in
lemma tollTogether (M N:TableW)(t:Sea M)(u:Sea N)(v:ReadsSix (M 1))(v':ReadsSix (N 1))
  {a b:ℝ}(ha:0≤a)(hb:a<b):
 ∃s∈Ioo a b, ReadsSix (M (sideways s)) ∧ ReadsSix (N (sideways s)):=by
 let K z := pennies (M z)* pennies (N z)
 have pe (L:TableW)(r:Sea L): Harbor (pennies ∘ L) :=(Harbor.det r).mul (Harbor.prod _ (f:=fun i z=>L z i i) fun i=>r i i)
 have r:Harbor K :=(pe M t).mul (pe N u)
 have h(z:ℂ):K z≠0 ↔ ReadsSix (M z) ∧ ReadsSix (N z):= mul_ne_zero_iff.trans ((pennies_iff _).and (pennies_iff _))
 by_contra! w
 exact (h 1|>.mpr ⟨v,v'⟩) (vanish_seam r ha hb
    (fun s p=>not_not.mp (fun y=>w s p ((h _).mp y).1 ((h _).mp y).2))
    (inside_subset_sheath eu))

include r
lemma feathBoth
 (y:ReadsSix (oneBox (P.wave x V w false 1 F) (P.wave x V w true 1 U) Q))
 (t:ReadsSix (P.readPrism x V w 1 F U))
  {a b:ℝ} (ha:0≤a)(hb:a<b):
 ∃s∈Ioo a b,∃g:0<s,
      ReadsSix (P.MinkAnswer x Y (puffup F g) (puffup U g)) ∧
      ReadsSix (P.MinkSplay x Y (puffup F g) (puffup U g) Q h):=by
 rw [← score_value r e] at t
 rw [← feathVelvet r h e] at y
 obtain ⟨s,p,k,j⟩:=tollTogether _ _ (score_harbors e (P:=P) (x:=x) (Y:=Y)) (feathSea h e) t y ha hb
 refine ⟨s,p,ha.trans_lt p.1,?_⟩
 rw [← score_broadcast e, ←feathMink h e]
 exact ⟨k,j⟩
#print axioms feathBoth

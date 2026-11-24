
import SatinPP.Puff
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


lemma Q_cart (j:Axis) (z:P.Spectrum0 j)(p:E4):
 Silk.Q (P.seasons j z) p = P.cartage j z (roll p):=by
  change P.cartage j z (roll (SEP j p).val)=_
  unfold cartage
  congr 1
  funext i
  change (p-p j • basis j : E4) i.val=p i.val
  simp [basis,i.property,Ne.symm i.property]
lemma sleeper_bed: (Ω)∈Bench (ε):=by
 rw [←P.heaven_hot 3 _ 1]
 exact ray (ε) (Ω) 1 zero_lt_one



/-- Uses the actual invariant vacuum on the election. -/
def occupant:Sleeper (ε):= ⟨⟨Ω,P.sleeper_bed x⟩,P.heaven_hot _ _⟩

variable (A:ℕ→P.Apron)
-- bounded Wick value of program on real rotation
def leaderW (a:ℜ)(F:SampleDose)(l u:ℝ): (G).Op:=
    voyage (ε) (Turn (X' a)) l u 1 (puff F)
def laterW (a:ℜ)(F:SampleDose)(l u:ℝ): (G).Op:=
    voyage (ε) (X' a) l u 1 (puff F)
local notation "V₁"=> P.leaderW x w D
local notation "V₂"=> P.laterW x w D

variable {P x D w V A}(m:Matinee P x D V A w)(F:SampleDose)(a:ℜ)

include m
private lemma ingress {n c}{l u v:ℝ}
   (r:Paid (ε) n c (X' a))(p:E4)(t:ℝ≥0)(g:0<l)(f:0<u)(e:(t:ℝ)+l=v):
    E t (Silk.Q (ε) p (X' a l u (Silk.Q (ε) (-p) (Ω))))=
     Γ (roll p) (P.profilesZ x V w a v):=by
 have k:=r.fits g f (show l≤v from e ▸ le_add_of_nonneg_left t.property) le_rfl
 have j:(v-l).toNNReal=t:=by rw [←e,add_sub_cancel_right, Real.toNNReal_coe]
 let S:=ε


 have i:E t * Silk.Q S p=Silk.Q S p * E t:= S.independent ..
 rw [Q_cart _ _ _ (-p),cart_empty,
     ← (show ∀H I,∀ y:(G),(H*I: (G).Op) y=H (I y) from fun _ _ _=>rfl) (E t),i]
 have c':= m.vac a v u (e ▸ add_pos_of_nonneg_of_pos t.property g) f
 rw [← c',k,sub_self]
 change Silk.Q S p (E t (X' a l u (Ω)))= Γ (roll p) (E (v-l).toNNReal (X' a l u (E (0:ℝ).toNNReal (Ω))))
 rw [j,P.heaven_hot]
 rw [show Silk.Q S p=Γ (roll p) from P.Q_cart 3 _ p]

variable {l u:ℝ}(v:Strict l u F)
include v

def nearP (h:ℝ)(p:Vantage):= Γ p (P.profilesZ x V w a (h-p 3))
def farP (h:ℝ)(p:Vantage):= Γ p (P.profilesZ x V w a (p 3-h))

lemma matFar (t:ℝ≥0):
    E t (V₂ a F l u (Ω))=
      DoseTravel.beam (G) F (farP (P:=P) (V:=V) (x:=x) (w:=w) a (l-t)):=by
  obtain ⟨n,c,r⟩:=m.pp a
  unfold laterW DoseTravel.beam
  rw [voyage_val r (bandp v) eu,← (E t).integral_comp_comm (litI _ (held_sail r (bandp v) eu) _),
      ← roll_price (f:=fun p:Vantage=>_)]
  congr 1 with p
  rw [map_smul,puff_at]
  by_cases h :roll p∈tsupport F.val
  · have c:p∈tsupport (puff F):=(puff_inv F).ge h
    have ⟨e,y⟩:=v _ h
    unfold Silk.lit farP
    rw [shore_eq r (bandp v) c]
    have j:t.val+(fore 3 l p)=(roll p) 3-(l-t):= by change t.val+(p 3-l)=p 3-(l-t.val);ring
    exact congrArg _ (ingress m a r p t (sub_pos.mpr e) (sub_pos.mpr y) j)
  simp [image_eq_zero_of_notMem_tsupport h]

lemma matNear (t:ℝ≥0):
    E t (star (V₁ a F l u) (Ω))=
      DoseTravel.beam (G) F (nearP (P:=P) (V:=V) (x:=x) (w:=w) a (t+u)):=by
  obtain ⟨n,c,r⟩:=m.pp a
  have s:=r.turn
  let e:=held_sail s (bandp v) eu
  unfold leaderW Silk.voyage DoseTravel.beam
  rw [salon_star e,← (E t).integral_comp_comm
      (show Integrable (fun p:E4=>star (puff F p) •
       Silk.lit (ε) (fun p=>star (Silk.sail (ε) (Turn (X' a)) l u 1 p)) p (Ω)) volume from ?_),
      ← roll_price (f:=fun p:Vantage=>_)]
  · congr 1 with p
    rw [map_smul,puff_at]
    rw [show star ((F.val (roll p):ℂ))=_ from Complex.conj_ofReal _]
    by_cases h :roll p∈tsupport F.val
    · have k:p∈tsupport (puff F):=(puff_inv F).ge h
      have ⟨e,y⟩:=v _ h
      unfold Silk.lit nearP
      dsimp only
      rw [shore_eq s (bandp v) k]
      unfold mat Turn
      rw [star_star]
      have j:t.val+(aft 3 u p)=t+u-(roll p) 3:= by change t.val+(u-p 3)=t.val+u-p 3;ring
      exact congrArg _ (ingress m a r p t (sub_pos.mpr y) (sub_pos.mpr e) j)
    simp [image_eq_zero_of_notMem_tsupport h]
  simpa only [bar_at] using litI _ (held_star e) (Ω)

variable {μ:ℝ}
lemma matIn (h:forwardSite F μ)(q:0≤l):
 E l.toNNReal (V₂ a F l u (Ω)) =
    DoseTravel.beam (G) F (P.laterProfile x V w μ a):=by
 rw [matFar m F a v, Real.coe_toNNReal _ q, sub_self]
 unfold DoseTravel.beam
 congr 1 with p
 by_cases i:p∈tsupport F.val
 · unfold laterProfile farP; rw [max_eq_right (h _ i),sub_zero]
 simp [image_eq_zero_of_notMem_tsupport i]
lemma matOut (h:backwardSite F μ)(q:u≤0):
 E (-u).toNNReal (star (V₁ a F l u) (Ω)) =
    DoseTravel.beam (G) F (P.earlierProfile x V w μ a):=by
 rw [matNear m F a v, Real.coe_toNNReal _ (neg_nonneg.mpr q), neg_add_cancel]
 unfold DoseTravel.beam
 congr 1 with p
 by_cases i:p∈tsupport F.val
 · unfold earlierProfile nearP; rw [max_eq_right (h _ i),zero_sub]
 simp [image_eq_zero_of_notMem_tsupport i]
#print axioms matOut
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

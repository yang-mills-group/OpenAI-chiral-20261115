
import Organdy.Glee
import Organdy.Coy
import Organdy.Hyssop
import Organdy.Emitter
/-! Relative payX covariance, adapting YM/CF/Stax/Bust.star_R and leap.
Do not require injection here. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Tulip Lat Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive  Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Urn Tenant Hake Salt Spire Nacre Dial SU
variable (s:Sweep n)
local notation "T"=> γS s
local notation "D₁" => detX s.s
local notation "B₁" => s.charge
local notation "JS"=> Single n
local notation "Fz"=> FC (Dwell n)

section Leap
variable {δ:ℕ}{P: BudgetPoint}{z z':Aura n→ℝ}
local notation "σX'"=> σX (n:=n) P
local notation "Ta"=> Salt.actY s
local notation "Tu"=> moldA s
local notation "VX"=> Aura n
variable {H J:Bag n}{F' F₀:Copy n}(D:Support (More n))(V:Orbit n)(c:Bias δ H P h z)(d:Bias δ J P h z')
local notation "W'"=> yellA s V
variable (hb:∀ i:Orbit n,∀ X:Aura n,J (moldA s X) (yellA s i)=sauce s.charge (detX s.s) (γS s) (H X i))
include hb c d
lemma star_R (X Y:Aura n)(t: Bias.αt Y X D δ):coll_T P (Tu X) (Ta D) (J (Tu Y)) W'=sauce s.charge (detX s.s) (Sour.γS s) (coll_T P X D (H Y) V):=by
 let a:=moldA s X; have hv:= (optic s D Y X δ).mpr t; let Λ:=sauce s.charge (detX s.s) (γS s); let Qv:=σX' X D; let Kv:=c.scope X Y D t.1 t.2.1 t.2.2; let Ku:=d.scope (moldA s X) (moldA s Y) (actY s D) hv.1 hv.2.1 hv.2.2
 by_cases f:Gates Qv X.val V.1; swap
 · unfold coll_T; rw [if_neg ?_,if_neg f,sauce,singT,win_z,map_zero]; exact mt (lights_V ..).mp f -- tune
 obtain ⟨Y',q,v⟩:=f; let Z:Orbit n:=(Y',V.2); let X':= σX' a (Ta D); have he: Agrees _ _ _ ∧ Set.EqOn _ _ _:=yellow s V Z X.val v (fun _ _=>rfl)
 let U:= yellA s Z; rw [Kv.toCrate.latch V Z v (fun _ _=>rfl),Kv.toCrate.pointV Z q,Ku.toCrate.latch _ U he.1 he.2, Ku.toCrate.pointV _ (show U.1 ∈ X' from ((Salt.lights_C ..)).mpr q),hb Z] -- tune
lemma leap (X Y:VX)(g:F' W'=suit_Y s (F₀ V)):d.payX (Tu X) (Ta D) (Tu Y) F' W'=suit_Y s (c.payX X D Y F₀ V):=by
 by_cases hA:Bias.αt Y X D δ; swap; · unfold Bias.payX; rw [dif_neg hA,dif_neg (fun t=> hA ((optic s D Y X δ).mp t)),Pi.zero_apply, Pi.zero_apply,map_zero]
 apply Subtype.ext; rw [d.truth _ _ _ _ ((optic s D Y X δ).mpr hA) _, g]; change Sault.rind (coll_T _ _ _ _ _ *sauce _ _ _ _) =sauce _ _ _ (c.payX X D Y F₀ V).val; rw [c.truth _ _ _ _ hA _,Sault.plower,star_R s D V c d hb X Y hA,show (sauce _ _ _) (coll_T P X D (H Y) V*(F₀ V).val)= _ from singm ..]
end Leap


variable {J:Type}[LinearOrder J][Fintype J]
variable {σ:I→Seat n}{V:I→Bag n}{A B:I→Aura n→ℝ}
variable {σ':J→Seat n}{V':J→Bag n}{A' B':J→Aura n→ℝ}
open QuadClock
variable (w:Pollen p q h σ V A B)(w':Pollen p q h σ' V' A' B')
variable {i:I}{j:J}(r:ℝ)
variable (e:whirlB s (V i)=r • V' j)

lemma swipeKey(x:ℝ):
    swipe V (realKey i x)= x • V i:=by
 funext u
 rw [swipe,Finset.sum_eq_single i]
 · unfold realKey; rw [update_self,Complex.coe_smul]; rfl
 · intro b _ ne; unfold realKey; rw [update_of_ne ne]; exact zero_smul ..
 · simp

lemma whirlReal (x:ℝ)(v:Bag n): whirlB s (x • v)=x • whirlB s v:=by
 rw [←Complex.coe_smul,←Complex.coe_smul,whirlV]; unfold cirrhose cSignX;split_ifs <;> simp
include e
lemma wish (x:ℝ):
   whirlB s (swipe V (realKey i x))= swipe V' (realKey j (x*r)):=by
 rw [swipeKey,swipeKey,whirlReal,e,smul_smul]

local notation "A₁"=> w.soar
local notation "A₂"=> w'.soar

lemma wishing (x:ℝ)
 (U:Orbit n)(X:Aura n) (D:Support (More n)) (Y:Aura n) (a b:Copy n)
 (l:b (yellA s U)=suit_Y s (a U)):
 A₂ (realKey j (x*r)) (moldA s X) (actY s D) (moldA s Y) b (yellA s U)=
 suit_Y s (A₁ (realKey i x) X D Y a U):=
 leap s D U (w.vat _) (w'.vat _)
    (fun i M=>by rw [←wish s r e x];exact wheel ..) X Y l

lemma wist (x:ℝ): PassingK s (A₁ (realKey i x)) (A₂ (realKey j (x*r))):=
  fun U _ => wishing s w w' r e x U

local notation "y"=> yellA s
local notation "Λ"=> suit_Y s
omit e
lemma elbow (x:ℝ)(U:Orbit n)(X:Aura n):
  A₁ (realKey i x) X ∅ X 1 U=x • pendulum w i X U:=by
 rw [lurch]
 rw [Finset.sum_eq_single i]
 · unfold realKey; rw [update_self,Complex.coe_smul]
 · intro b _ ne; unfold realKey; rw [update_of_ne ne]; exact zero_smul ..
 · simp

include e
lemma zig (U:Orbit n)(X:Aura n):
  r • pendulum w' j (moldA s X) (y U)=Λ (pendulum w i X U):=by
 have h:=wishing s w w' r e 1 U X ∅ X 1 1 (map_one _).symm
 have ht: actY s ∅=(∅:Support _) := map_empty _
 rw [ht,one_mul,elbow,elbow,one_smul] at h
 exact h
lemma passingPend
  (g:(boxA s).symm (σ i)=σ' j):
  passingR n s (pend w i) (r • pend w' j):=by
  intro X z
  have ht:(moveHub s X).val.1=σ' j ↔ X.val.1=σ i:=
     g ▸ (boxA s).symm.injective.eq_iff
  simp only [Pi.smul_apply,pend,ht]
  split_ifs; swap; · rw [Pi.zero_apply,Pi.zero_apply,map_zero,smul_zero]
  let U:Orbit n:=(z,Classical.arbitrary _)
  let M:=lagE X
  exact Eq.trans (congrArg (r • ·) (circle w' j (moldA s M) (y U) _).symm)
    (zig s w w' r e U M)
end YM.CF.Organdy

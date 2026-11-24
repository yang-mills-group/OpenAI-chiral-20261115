import Velour.Arabesque.Lore
import YM.SU5.FiniteGaugeData.Poin.Mint
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2800
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} (S:Semigroup H timeAxis)


open Boundary Probe
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

variable {S}
variable {κ:Type}(L:S.Livery κ)
variable {n:ℕ}
local notation "ℓ"=> Fin n→ℝ
local notation "ℒ"=> Fin n→ℂ
local notation "σ"=> Equiv.Perm (Fin n)
variable (u:Fin n→κ)(X:Fin n→E4)
namespace Livery
local notation "D"=>S.muslin
local notation "Ω"=>L.Ω
local notation "Y"=>L.Y
local notation "U"=>S.liftL
local notation "τ"=>κ × Test4
local notation "ℙ"=>List (κ × Test4)

open Mink Mink.Lorentz YM.Motifs

open Distribution

def feels(i:κ)(v:S.muslin): Test4 →L[ℂ] H where
 toFun f:=(Y i f v).val
 map_add' f g:=by rw [map_add]; rfl
 map_smul' c f:=by rw [map_smul]; rfl
 cont:=continuous_iff_continuousAt.mpr fun x=>
   (((L.sewn i).touch.surges (show Tendsto (fun f:Test4=>f) (𝓝 x) (𝓝 x) from continuousAt_id)).at_one v).plain

variable (h:L.Blithe)
include h in
lemma lullaby (l s:ℙ)(i:κ): ∃d:Distn E4,∀f,d f=L.song (l++(i,f)::s):=by
 obtain ⟨A,p,t⟩:=h.fray.faces (P:=Set.univ) (fun _ _=>trivial)
    (L.line_in l (fun _ _=>trivial))
 exact ⟨(innerSL ℂ (A Ω).val).comp (L.feels i (L.gem s)),fun f=> by
   rw [song,gem,gem,line_append,line_cons, Module.End.mul_apply, ←t.symm]
   rfl⟩


def outThere:Set (E4×E4):={v|v.2-v.1∈spacelike}
def Spaced (f g:Test4):=tsupport f ×ˢ tsupport g ⊆outThere

def vowel(r s:ℙ)(x y:τ):ℂ:=
 L.song (r++[x,y]++s)
include h in
theorem clearVoice(r s:ℙ)(i j:κ)(u:CompactW r)(v:CompactW s)
 (f g:Test4)(q:Spaced f g): L.vowel r s (i,f) (j,g)=L.vowel r s (j,g) (i,f):=by
  have w(i j:κ):∃d:Test4→ Distn E4,∀f g,d f g=L.vowel r s (i,f) (j,g)-L.vowel r s (j,g) (i,f):=by
     choose A z using fun f=>L.lullaby h (r++[(i,f)]) s j
     choose B y using fun f=>L.lullaby h r ((i,f)::s) j
     refine ⟨fun f=>A f-B f,fun f g=>?_⟩
     rw [sub_apply,z,y]
     simp [vowel]
  obtain ⟨A,a⟩:=w i j
  obtain ⟨B,b⟩:=w j i
  apply sub_eq_zero.mp
  rw [←a]
  refine Mint.disperse f g A (fun x=>- B x) outThere ?_ ?_ q
  · intro f g; rw [a,neg_apply,b,neg_sub]
  constructor; intro x y t
  obtain ⟨E,e,F,m,p⟩:=L.locale h r s u v x y t
  obtain ⟨k,hk,r⟩:=Metric.mem_nhds_iff.mp e
  obtain ⟨l,hl,s⟩:=Metric.mem_nhds_iff.mp m
  refine ⟨_,_,Metric.isOpen_ball,Metric.mem_ball_self hk,Metric.isOpen_ball,Metric.mem_ball_self hl,?_⟩
  intro f y' g z
  rw [a,sub_eq_zero]
  have w':∀{f:Test4}{x:E4}{r:ℝ},tsupport f ⊆ Metric.ball x r → LocalTest f:=fun y=>
       (isCompact_closedBall ..).of_isClosed_subset (isClosed_tsupport _)
         (y.trans Metric.ball_subset_closedBall)
  exact p (i,f) (j,g) (w' y') (w' z) (y'.trans r) (z.trans s)
#print axioms clearVoice

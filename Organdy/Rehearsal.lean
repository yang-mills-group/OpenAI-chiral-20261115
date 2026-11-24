import Organdy.Spark
import Organdy.DraftK
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Urn Tenant Hake Salt Spire Nacre Dial SU Tulip Lat
open Roots
open Vale Buffered QuadClock Neon MeasureTheory
open Swell Hom

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
variable (P:Spine) (i k t:ℕ)
local notation "Λ"=>P.par
local notation "x'"=> Vale.hat (Λ).R.L (Λ).x t
local notation "N'"=> age P.run i t
local notation "KL"=> (P.run.voyage i).CapeT t
local notation "R✤"=>RootBook P.run i k t
local notation "p'" => (R✤).p
local notation "q'" => (Λ).J.n
local notation "h'" => (Λ).h

variable (s:Sweep (age P.run i t))

structure Guided (o:Site N')(S:Support (More N'))(D:Mark N')(U:phy N')(V:Bag N')
    (c a b:ℝ):Prop extends Spring P i k t o S D V c a b where
 glow: Cymbal S D U c
 wire: smoothRide P i k t U V

variable {M:ℕ}{L:Side}
local notation "L₁"=>L.val
local notation "Tax"=> outfit L₁

abbrev Rolls (L:Side)(o:I→Site N')(V:I→Bag N'):= Tassel p' (R✤).K q' h'
   (node ∘ o) (incline (node ∘ o) L.val p' V)
variable {S:I→Support (More (age P.run i t))}{D:I→Mark (age P.run i t)}
 {V:I→Bag (age P.run i t)}{U:I→phy (age P.run i t)}{C:I→ℝ}
 {o:I→Site (age P.run i t)}
structure Recital
   (L:Side) (M:ℕ)(a b γ μ W:ℝ) 
   (o:I→Site N')(S:I→Support (More N'))(D:I→Mark N')
   (U:I→phy N')(V:I→Bag N')(C:I→ℝ)
   (w:Rolls P i k t L o V):Prop where
   roll : w.f=outfit L.val a ∧ w.g=outfit L.val b ∧ w.M=M ∧ w.γ=γ
   learns:Force_M (p').B (node ∘o) M
   tipped: Reverberate P i k t o S D C U w.Ev w.Fv
   taught: Wintergate P i k t L W μ μ 1 o w.Ev w.Fv

variable {μ γ W:ℝ}
lemma Kyanite.rehearsal (j:Kyanite P i k t M L a b γ μ W)
   (v:∀ x:I,Guided P i k t (o x) (S x) (D x) (U x) (V x) (C x) a b)
   (z:Force_M (p').B (node ∘o) M):
   ∃ w,Recital P i k t L M a b γ μ W o S D U V C w:=by
  obtain ⟨_,g,A,B,r,T⟩:=playSpring P i k t j.launch (sunny _ _ z) fun x=>(v x).toSpring
  let W': Rolls P i k t L o V:=⟨M,Tax a,Tax b,γ,A,B,r,T⟩
  obtain ⟨α,d⟩:=j.pressed
  refine ⟨W',⟨rfl,rfl,rfl,rfl⟩,z,ariseGuide P i k t T U (fun x=>(v x).plus)
      (fun x=>(v x).glow) (fun x y g e=>?_),tickets P i k t T z g d j.house⟩
  have l:(∑ X:Aura N', incline (node ∘o) L.val p' V x X y)=∑ X:Aura N', V x X y:=
   by rw [←Finset.sum_apply,←Finset.sum_apply];exact congrFun (giveExpand ..) y
  rw [l]; exact (v x).wire y g e

variable {J:Type}[LinearOrder J][Fintype J]
lemma harmony
   {p:J→Site N'} {G:J→Bag N'}
   (w:Rolls P i k t L o V) (v:Rolls P i k t L p G)
   (x:I)(y:J)(g:(boxA s).symm (node (o x))=node (p y))
   (h:t≤P.run.uv k)
   {r:ℝ}(j:|r|≤1)
   (e:whirlB s (V x)=r • G y):
    passingR N' s (νTip w.Ev x) (r • νTip v.Ev y) ∧
    passingF N' s (emberTip w.Fv x) (r • emberTip v.Fv y):=by
   obtain ⟨a,b,_,p_⟩:=(floats P i k t h).fares
   have z:passingF N' s (R✤).K (R✤).K:=
     fun j v u=>p_.face s trivial _ (spinZ ..) j v.1 v.2 u
   exact w.bric v s z x y r j g (glide s _ _ _ _ e _ _ _ g)

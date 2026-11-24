import Merino.Brooch.Frosted
import YM.SU5.Exchange.Stack.Racket

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Brooch
open Function Finset Fock Scroll Spire Sault
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Lattice Cube Scree Skye Sour Drapes Tulip Lat Branch Swell
open Thera Hest Levier
variable {N:Side}
local notation "Jk"=> Single N

open RG Dial Vow

-- Two panes: inspecting and kernel
abbrev LatticeFieldEstimates (n:Side):= Pane n → Pane n → FC (Single n)
def strike(Y:SOp N):LatticeFieldEstimates N:=fun _ V=>(Y (profile V)).trace • 1
def metal(Y:SOp N):LatticeFieldEstimates N:=fun _ V=>dg (Y (profile V))

def move(s:Sweep N): FC Jk→FC Jk := tourP (actSpin s) (actB s) (actR s)
def back(s:Sweep N):=flashA s
def scene0(s:Sweep N) (K:Scree.Loom N)(F:LatticeFieldEstimates N):phy N := fun x=> move s (F (back s x.1) (back s (K x)))
variable (s:Sweep N){P W:SOp N}{X:SOp N}{K:Scree.Loom N}{o:Seat N}{q l:ℕ}
lemma call_plus (S:Scree.Loom N)(F G:LatticeFieldEstimates N):scene0 s S (F+G)=scene0 s S F+scene0 s S G:= funext fun _=> sew_add ..
lemma call_less (S:Scree.Loom N)(F G:LatticeFieldEstimates N):scene0 s S (F-G)=scene0 s S F-scene0 s S G:= funext fun _=> sew_sub ..
lemma call_sum (S:Scree.Loom N){α:Type*}(A:Finset α)(F:α→LatticeFieldEstimates N):scene0 s S (∑i∈A,F i)=∑i∈A,scene0 s S (F i):=by
 classical
 induction A using Finset.induction_on with


 |empty =>
   rw [sum_empty,sum_empty]
   have e:=call_less s S 0 0
   rw [sub_self,sub_self] at e; exact e
 |insert i A e h =>rw [sum_insert e,sum_insert e,call_plus,h]

variable {p:BudgetPoint}{a b c d h t u v z:ℝ}
local notation "U"=> reefCost l p z h
local notation "C"=> treeEarnings l p z h a c
local notation "L"=> Tenant.quota^2
def txFee(l:ℕ)(p:BudgetPoint)(z h v:ℝ):=
   reefCost l p z h*(Tenant.quota^2*v)
def foFee(l:ℕ)(p:BudgetPoint)(z h a c v:ℝ):=
   txFee l p z h v + treeEarnings l p z h a c*(Tenant.quota^2*v)
local notation "G"=> Fence P W K p q l (boxA s o) h z

variable (D:DockPulse p K t d a h z l q)
include D
lemma act_trace(Y :Soak o X a v d):
   G (scene0 s K (strike X)) (txFee l p z h v) (txFee l p z h v):=by
  have g:scene0 s K (strike X)=blazePlate K (icyPose s X):=by
    funext x
    rw [show scene0 s K (strike X) x= _ from coin (actB s) (actR s) (actSpin s) (X (profile (flashA s (K x)))), blazePlate,icy_equation]
  rw [g]; exact glowTrace h D (icy_purchase s Y)


variable (H:Solo a c P d)(Q:Solo a c W d)
include H Q
lemma act_metal(Y :Soak o X a v d):
   G (scene0 s K (metal X)) (foFee l p z h a c v) (foFee l p z h a c v):=by
  have j:=icy_purchase s Y
  let Z:=icyPose s X
  let F:= G
  have g(x): scene0 s K (metal X) x = if actR s then blazePlate K Z x - firePlate K Z x else firePlate K Z x:=by
     rw [show scene0 s K (metal X) x=_ from dd (actB s) (actR s) (actSpin s)
       (X (profile (flashA s (K x)))), ←icy_equation]
  let rc:= reefCost l p z h * (Tenant.quota^2 * v)
  have Tr:F (blazePlate K Z) rc rc:=glowTrace h D j
  have m:=trimQ h D H Q j
  rw [funext g]; by_cases e:actR s
  · simp_rw [if_pos e]; exact Tr.sub m
  simp_rw [if_neg e]
  obtain ⟨A,⟨B,M,_⟩,_⟩:=Tr.stock
  have r:0≤rc:=?_ -- barrage nonneg maybe
  exact m.smaller (le_add_of_nonneg_left r) (le_add_of_nonneg_left r)


  obtain ⟨Bv,bv,k,_,G0,_⟩:=M.price
  refine le_trans ?_ G0
  exact sum_nonneg fun i _=>mul_nonneg (k i).tube.price (Real.exp_pos _).le
omit D H Q

def front (P W:SOp N)(V:Op Jk):LatticeFieldEstimates N:=fun _ U' => kerLocal (P (profile U')) (tickA N) V (W (profile U'))
structure Steers (s:Sweep N)(P W:SOp N)(d:ℝ) : Prop extends Staffer P W d where
  law :∀ (V:Pane N),Guard V d→
     let p1:=profile V; let p2:=profile (back s V)
     sings (actB s) (actSpin s) (P p2)=swapX (actR s) (P p1) ∧ W p1=jazz (actR s) (sings (actB s) (actSpin s) (W p2))

abbrev fhFee(l:ℕ)(p:BudgetPoint)(z h a c v:ℝ):=
 let R:=payΩ a c (Tenant.quota^2*v)
 let w:= reefCost l p z h
 w*(2*(R*(Real.exp a+c)))+ w*(2*(c*R))

include D H Q
lemma act_front(Y:Op Jk)(j:Soak o (fun _=>Y) a v d)
 (e:Steers s P W d):
 G (scene0 s K (front P W Y)) (fhFee l p z h a c v) 0:=by
 let Z:=form (actB s) (actR s) (actSpin s) Y
 have F:=icy_purchase s j
 rw [icy_fixed] at F
 have I:=spinPlasma h D H Q Z F


 let A:phy N:=fun x=>front P W Z x.1 (K x)
 have j1 : scene0 s K (front P W Y) = hing (actR s) A:=by
   funext x; obtain ⟨g,z⟩:=e.law (K x) (D.roof.paid x)
   have d:=e.projection _ (D.roof.paid x)
   have E:=compass (actB s) (actR s) (actSpin s) (T:= W (profile (back s (K x)))) g d (tickA N) (tickA N) Y
   rw [← z] at E
   have h1 : hing (actR s) A x = hing (actR s) (A x):=by unfold hing; split<;>rfl
   rw [h1]; exact E
 rw [j1]; unfold hing; split
 · simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using
       (show G A (fhFee l p z h a c v) 0 from I).scale (-1)
 exact I
end YM.CF.Merino.Brooch


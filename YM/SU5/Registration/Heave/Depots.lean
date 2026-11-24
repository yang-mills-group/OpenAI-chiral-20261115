import YM.SU5.Registration.Heave.StillFront
import YM.SU5.Registration.Rise.AtFull
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

set_option quotPrecheck false
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
namespace Spine
open Aria
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "H"=> P.ColorHil j x
local notation "T"=> (P.physicalEnergy j x).E
local notation "M" s:max u:max=>whenly (timeMesh P.par) s u
/-! # combine heated physical aprons at common width

works for some height≥ every component's own height, point time center is always zero.
Can change width & hold all-axis survey arguments separate. Here do not claim
movement along non-time axes under a strobe.
-/
variable (s w:ℕ)(hw:0<w+w)
local notation "z"=> M s w
local notation "ζ" t:max=> T (t-z)

def Deposited (F:P.Test)(U:ℝ≥0→(P.ColorHil j x).Op):Prop:=∀ t:ℝ≥0, (M s w) ≤ t→∃ f:P.InCase j s (w+w) (P.shifts j (w:ℤ) F), T (t-z)* f.charges x hw * T (t-z)= U t
namespace Deposited
variable {F G:P.Test}{A B':ℝ≥0→(P.ColorHil j x).Op}(p:P.Deposited j x s w hw F A)
local notation "h" => hw
include p
lemma scale (e:ℂ): P.Deposited j x s w hw (e • F) (e • A):=by
 intro t v; obtain ⟨f,h'⟩:=p t v; let f':P.InCase j s (w+w) (P.shifts j (w:ℤ) (e • F)):=by rw [map_smul]; exact f.scale e
 refine ⟨f',?_⟩; rw [InCase.charges_eq f' x (f.scale e) rfl rfl (map_smul ..),f.charges_scale x e, P.stage_scale_r j x, h']; rfl
lemma add (U:P.Deposited j x s w hw G B'): P.Deposited j x s w hw (F+G) (A+B'):=by
 intro t v; obtain ⟨f,h'⟩:=p t v; obtain ⟨f',p'⟩:=U t v; let q:P.InCase j s (w+w) (P.shifts j (w:ℤ) (F+G)):=by rw [map_add]; exact f.append f'
 refine ⟨q,?_⟩; rw [q.charges_eq x (f.append f') rfl rfl (map_add ..), f.charges_add x f' hw,mul_add,_root_.add_mul,h',p']; rfl
lemma sub (U:P.Deposited j x s w hw G B'): P.Deposited j x s w hw (F-G) (A-B'):=by
 let p':= p.add P j x s w h (U.scale P j x s w h (-1)); simpa only [sub_eq_add_neg, neg_one_smul] using p'
omit p
lemma blank : P.Deposited j x s w hw 0 0:=by
 intro t v; have f:P.InCase j s (w+w) (P.shifts j (w:ℤ) 0):=by rw [map_zero]; exact InCase.zeros ..
 refine ⟨f,?_⟩; have hf:f.charges x hw=0:=by rw [f.charges_eq x (InCase.zeros P j s (w+w)) rfl rfl (map_zero _) h]; exact (congrArg ((P.colorSpace j x) ·) (InCase.rations_zero (s:=s) h)).trans (map_zero _)
 rw [hf,mul_zero,zero_mul]; rfl
lemma sum {ι:Type*}(Y:Finset ι)(X:ι→P.Test)(v:ι→ℝ≥0 → (P.ColorHil j x).Op)(p:∀ i∈ Y, P.Deposited j x s w hw (X i) (v i)): P.Deposited j x s w hw (∑ i∈Y,X i) (∑ i∈Y,v i):=by
 classical
 induction Y using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; exact blank P j x s w hw
 | @insert i S h' ih=>rw [sum_insert h',sum_insert h']; exact add P j x s w h (p i (mem_insert_self ..)) (ih (fun i v=> p i (mem_insert_of_mem v)))
end Deposited
open Deposited
variable (A:P.Apron)(u:ℕ)
local notation "k"=> A.zoom P s j
local notation "v"=> A.full P s
local notation "wV"=> (A.allowance P j)
local notation "Θ"=> M s u
local notation "τ" => P.stageH j x A
include hw
lemma shifted_deposit (p:A.s≤ s)(U:A.zoom P s j+u ≤ w): P.Deposited j x s w hw (P.shifts j (u:ℤ) v) (fun t=> τ (t+Θ) (t-Θ)):=by
 -- algebra
 intro t w₀; let X:= P.shifts j (w:ℤ) (P.shifts j (u:ℤ) v)
 have he:k ≤ w+u:=by omega
 have hX:k ≤ w-u:= Nat.le_sub_of_add_le U
 let f:= A.entrusted P j s p (w+u) (w-u) he hX
 have hz:w+w=w+u+(w-u):=by omega
 have hx:X=P.shifts j ((↑(w+u:ℕ)):ℤ) v:=by unfold X; rw [P.shifts_sum,Nat.cast_add];
 have f':P.InCase j s (w+w) X:=by rw [hx,hz]; exact f
 have hu: u≤w:=by omega
 have h:(Θ) ≤ z:= (when_le ..).2 hu
 have hm₁:(M s (w+u))=z+Θ:= when_add ..
 have hm₂:(M s (w-u))=z-Θ:=by
    have he:M s (w-u)+(M s u)=z:=by rw [←when_add,Nat.sub_add_cancel hu]
    rw [←he,add_tsub_cancel_right]
 have hy:wV ≤ (M s (w+u)) := (zoomMoney P j A s p).symm.trans_le ((when_le ..).2 he)
 have hc:wV ≤ (M s (w-u)) := (zoomMoney P j A s p).symm.trans_le ((when_le ..).2 hX)
 have hb:= A.entrusted_pays P j x s p (w+u) (w-u) he hX (hz ▸ hw)
 refine ⟨f',?_⟩; rw [f'.charges_eq x f rfl hz hx hw,hb]; dsimp only
 have h₁:(M s (w+u))≤ t+(Θ):= hm₁.trans_le (by gcongr)
 have h₂: (M s (w-u))≤ t-(Θ):= hm₂.trans_le (by gcongr)
 rw [P.stage_more j x A hy h₁ hc h₂,hm₁,hm₂, add_tsub_add_eq_tsub_right,show t-Θ-(z-Θ)=t-z from ?_]; rw [←add_tsub_add_eq_tsub_right (t-Θ) Θ (z-Θ),tsub_add_cancel_of_le h,tsub_add_cancel_of_le (h.trans w₀)]
lemma leaf_deposit (p:A.s≤ s)(U:A.zoom P s j≤w): P.Deposited j x s w hw v (fun t=> τ t t):=by
 have he:= P.shifted_deposit j x s w hw A 0 p (by omega); simpa only [Nat.cast_zero, shifts_zero,when_zero,tsub_zero,add_zero] using he
omit hw
lemma deposited_retains {U:ℝ≥0→(P.ColorHil j x).Op}(p:A.s≤ s)(V:P.Deposited j x s (A.zoom P s j) (add_pos (A.zoomP P j s) (A.zoomP P j s)) v U)(t:ℝ≥0)(u:wV ≤ t) : τ t t= U t := by
 obtain ⟨f,q'⟩:= V t ((P.zoomMoney j A s p).trans_le u); rw [f.charges_eq x (A.anchored P j s p) rfl rfl rfl _,(A.retains P j x s p),P.zoomMoney j A s p] at q'; exact q'
lemma deposit_at_finger {U:ℝ≥0→(P.ColorHil j x).Op}(v₁:P.Deposited j x A.s (A.u j) (add_pos (A.pos j) (A.pos j)) A.F U)(t:ℝ≥0)(u:wV ≤ t): τ t t= U t := P.deposited_retains j x A.s A le_rfl (U:=U) (by have h1:∀ i:ℕ, A.u j=i → ∀ hw : 0 < i+i,P.Deposited j x A.s i hw A.F U:=fun i p=> p ▸ fun _=>v₁; have h2:=h1 _ (A.zoom_at P j).symm; rw [A.full_at P]; exact h2 _) t u
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.shifted_deposit
#print axioms Spine.deposited_retains
#print axioms Spine.Deposited.sum
#print axioms Spine.Deposited.sub

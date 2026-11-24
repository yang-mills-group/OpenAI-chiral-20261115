import YM.SU5.Reconstruction.AnglePath.Ribbon
/-!
# Phase budgets passed via Friedrichs comparison (the second Clasp). Generic.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame.Cardio
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {K J H D:Hilbert} {X:Type}
open Clasp

namespace Organ
variable [AddCommGroup X][Module ℂ X](A:Organ X H D)(G:Clasp K H H)(p:A.Pre G)(C:Clasp J H D)(q:A.Core C)
open Multiplier Chirp
variable (e:ℝ) (b:e=1∨e=-1) {Y:Type*}[MeasurableSpace Y] (P:PVM H Y)(L:Y→ℝ)(f:Measurable L)(g:0≤L)
local notation "V"=> singers P L
variable (h: Tide G L L e P P)
noncomputable def crossing (e u:ℝ):ℝ:=wages e (u/2)
include p b q f g h
lemma packT(u:ℝ): ∃ (x:D.Op)(y:D.Op), C.ScalePass (P.region (onboard L)) x (singers P L u) y (crossing e u):= by
 apply fundRibbon A G p C q (G.link L f g L f g e b P P h u) (wages_pos ..)
 unfold wages; rw [←Real.exp_add]; congr 1; ring
omit p q b f g h
local notation "τ"=> lengthen
lemma fareProof(u t:ℝ) : sing u (crossing e t * crossing e t)=sing t (lengthen e (u/2)) := by unfold lengthen crossing wages sing; rw[←Real.exp_add,Real.log_exp,Real.log_exp]; push_cast; congr 1; ring
include p q b f g h
-- CP5 Catch.weightTransport proof now at THE NEW TOKEN
lemma around (d:ℝ→ℂ)(l:Tag d)(u:ℝ): C.cLeft u * order P (d ∘ L)= order P (d ∘ (fun x=> τ e (u/2) * L x))* C.cLeft u:= by
 set D':= lengthen e (u/2); set R:= C.cLeft u; let k(x:Y):= D'*L x; have hd:0<D':= Real.exp_pos _; have hm: onboard k=onboard L:=by ext x; change 0<D'*L x ↔ _; simp [hd,onboard]
 have r1:Measurable k:=f.const_mul _
 let Z:=P.region (onboard L)
 refine recover P P L k f r1 g (fun x=> mul_nonneg hd.le (g x)) R _ l ?_ (fun i=>?_)
 · rw [hm]; obtain ⟨a,v,t⟩:= packT A G p C q e b P L f g h 0; exact (hourComm C t u).eq
 obtain ⟨F,η,v⟩:=packT A G p C q e b P L f g h i; let A':= V i; let x:ℂ:=sing i D'
 have he:R*A'*star R=A'*(1-Z)+x • (A'*Z):= by
    have ht:= C.passage v u; rw [fareProof] at ht; exact ht
 change R * _= _ * R
 have hx: singers P k i=A'*(1-Z)+x • (A'*Z):= by
   have u:=sings P L f i; have t:=Registers.box P (arc L f); refine (sings P k r1 i).single (((u.times ((Registers.one P).sub t)).add ((u.times t).scale x)).agrees (sings P k r1 i|>.price) ?_); intro v; refine Eventually.of_forall fun w=>?_
   by_cases q:w∈ onboard L
   · change 0<L w at q; have q':w∈ onboard L:=q
     simp [q',smul_eq_mul,k]; rw [voices i _ _ hd q]
   have hs:L w=0:= le_antisymm (le_of_not_gt q) (g w); simp [hs,q,k]
 rw [hx,← he,mul_assoc, (C.left_credentials u).2.2.1,mul_one]
end Organ
end YM.CrossedFrame.Cardio

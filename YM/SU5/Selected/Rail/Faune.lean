import YM.SU5.Selected.Rail.Sola
/-! # Exact upper support. Real clocks in Cover, lower site for every representer.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Rail
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Airy Fock Topology
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2*π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
open Finset Lat
variable {n k t:ℕ}{q:Type*}[Fintype q][DecidableEq q]
-- C support on simply prefix expansion. Color product/finite expansion.
abbrev Stream(v:Cover):Prop:=∃ i:ℕ,v=pick i
abbrev Blade(f:Coast→ℂ):Prop:= Color Stream f
lemma stream_add {v w:Cover}(h:Stream v)(p:Stream w):Stream (v+w):=by obtain ⟨i,rfl⟩:=h; obtain ⟨j,rfl⟩:=p; exact ⟨i+j,by unfold pick; rw [picked,add_zero,Nat.cast_add]⟩
lemma stream_zero: Stream 0:= ⟨0,by unfold pick; ext1 i; cases i using Fin.lastCases <;> simp [Ε]⟩
lemma stream_one:Blade 1:=by
 have hp:prefixG (0:Cover)=(1:Coast→ℂ):=funext (fun i=>prefix_zero i); rw [←hp]; exact .mode _ stream_zero
lemma stream_mul {f g:Coast→ℂ}(p:Blade f)(u:Blade g):Blade (f*g):=by
 induction p with
 | zero=> rw [zero_mul]; exact .zero
 | mode v p=> induction u with
   | zero=> rw [mul_zero]; exact .zero
   | mode j h=> rw [show prefixG v*prefixG j=prefixG (v+j) from funext (fun k=> (prefix_add ..).symm)]; exact .mode _ (stream_add p h)
   | @smul z f h q=> rw [Algebra.mul_smul_comm]; exact q.smul _
   | @add f g p q u v=> rw [mul_add]; exact u.add v
 | @smul z f h q=> rw [Algebra.smul_mul_assoc]; exact q.smul _
 | @add f g p q h k=> rw [add_mul]; exact h.add k
lemma stream_pow {f:Coast→ℂ}(h:Blade f)(k:ℕ):Blade (f^k):=by induction k with| zero=> rw [pow_zero]; exact stream_one| succ k ih=> rw [pow_succ]; exact stream_mul ih h
lemma stream_lac : Blade lacuna:=by rw [show lacuna=1+(-1:ℂ) • prefixG (pick 1) from funext (fun i=>by simp [lacuna,sub_eq_add_neg])]; exact stream_one.add (.smul _ (.mode _ ⟨_,rfl⟩))
lemma stream_sum {X:Type*}[DecidableEq X](f:X → Coast→ℂ){L:Finset X}(h:∀ i, Blade (f i)):Blade (∑ i∈L,f i):= by induction L using Finset.induction with| empty=>rw [sum_empty]; exact .zero| insert i L hi ih=> rw [sum_insert hi]; exact (h _).add ih
variable (W:FaceL)(Z:q→basisRule)
lemma stream_hull (i:q):Blade (fun w=>hull k Z w i):=by
 let F(z:ℕ):=Z i z • prefixG (pick z); have hv(i:ℕ): Blade (F i):=.smul _ (.mode _ ⟨_,rfl⟩); have ht:(lacuna^k*(∑ z∈ (Z i).support,F z))=(fun w=>hull k Z w i):=by ext1 j; simp [F,hull,Finset.sum_apply]
 rw [← ht]; exact stream_mul (stream_pow stream_lac _) (stream_sum F hv)
lemma stream_shift (i:q)(s:SpinIdx): Color (fun v:Cover=>s=0 ∧ Stream v) (fun w=>ShiftY k Z w s i):=by
 by_cases p:s=0
 · subst s; unfold ShiftY tilt; simp_rw [Matrix.of_apply,if_true]; exact Color_mono (stream_hull Z i) (fun a u=>⟨trivial,u⟩)
 unfold ShiftY tilt; simp_rw [Matrix.of_apply,if_neg (Ne.symm p)]; exact .zero
lemma stream_late (i:Fin n)(s:SpinIdx): Color (fun v:Cover=> v= -(stick W t i)∧ s=2) (fun w=> Spouse W n t w s i):=by
 by_cases p:s=2; · subst s; unfold Spouse tilt; simp_rw [Matrix.of_apply,if_true]; exact .mode _ ⟨rfl,trivial⟩
 unfold Spouse tilt; simp_rw [Matrix.of_apply,if_neg (Ne.symm p)]; exact .zero
variable {N:Side}(u x:Site N)(s:SpinIdx)
lemma exact_line (k:ℕ) : ∀ᶠ K:ℕ in atTop,∀ N:Side,∀ (u x:Site N) (s:SpinIdx) (i:q), (exactU Z N u k) (x,s) i≠0 →s=0∧ ∃ a:ℕ,a≤K∧ x=u-wrap N (pick a):=by
 filter_upwards [eventually_all.mpr fun i:q=> eventually_all.mpr fun s:SpinIdx=> hedge (stream_shift (k:=k) Z i s)] with K p N u x s i v; obtain ⟨w,⟨g,p,r,u'⟩,z⟩:= leaves (F:= ShiftY k Z) x u s i (p i s) (fun q=> v ((profile ..).trans q)) -- orientation tune
 subst w; have he:=g 3; simp only [pick,node₃,Int.natAbs_natCast] at he; exact ⟨p,_,he,z⟩ -- binder p might overwritten Prod destruct
lemma exact_late (i: Fin n)(p: (clerks W N u n t) (x,s) i≠0): s=2∧ x=u+wrap N (stick W t i):=by
 obtain ⟨v,⟨e,l⟩,z⟩:= leaves (F:= Spouse W n t) x u s i (stream_late W i s) (fun v=> p ((profile ..).trans v)); subst v; simpa [z] using (show s=2 from l)
end YM.CF.Crest.Rail
open YM.CF.Crest.Rail
#print axioms exact_line
#print axioms exact_late
#print exactU

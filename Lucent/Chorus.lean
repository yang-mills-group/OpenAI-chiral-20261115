import Lucent.Shadows
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

open Pannier.Chancel Rous Pressure
open Peaks Scree
open RG Buffered.Afterglow
open Lamour Lamour.Bridge
open Morn Journey
variable {P:Preparation}{I J:Type}
open Onyx
open Stationary (Gaia)
open Vale Morn
set_option quotPrecheck false
variable {W:ℕ→I→Staff} {R:ℕ→ℝ} {r b l:ℕ→ℕ}(T:Velocity P R r){B:ℝ}
variable [Fintype I]

structure MeasureAt (d:FieldPlan I) (W:ℕ→I→Staff)(R:ℕ→ℝ)(r:ℕ→ℕ):Prop where
  hear: FairRoad W R d.hands
  see(i:I): climb (fun s=>(r s:ℝ)) (fun s=>seat (W s) i) (d.roles i).pt
  feel(i:I)(s:ℕ): body (W s) i=(d.roles i).voice
  touch(i j:I):(d.roles i).pt=(d.roles j).pt → ∀ᶠ s in atTop,seat (W s) i=seat (W s) j
variable {d:FieldPlan I}
lemma MeasureAt.receipt (h:MeasureAt d W R r): OnScale d W R r:=by
 refine ⟨h.hear,fun s=>funext fun i=> h.feel i s,?_,?_⟩
 · rintro ⟨i,e|e⟩ <;> exact h.see i
 rintro ⟨i,e|e⟩ ⟨j,f|f⟩<;> exact h.touch i j
abbrev relabel (F:Gaia→Gaia)(G:Twah.DirSpin→Twah.DirSpin)(d:FieldPlan I):FieldPlan I :=
 ⟨fun i=>⟨F (d.hands i).p,(d.hands i).shade⟩,
  fun i=>⟨F (d.roles i).pt,G (d.roles i).voice⟩⟩
abbrev league (u:FieldPlan I)(v:FieldPlan J): FieldPlan (I⊕J):= ⟨Sum.elim u.hands v.hands,Sum.elim u.roles v.roles⟩
abbrev sed (P:Preparation)(n:ℕ):Gaia→Gaia:= (leg P · n)

abbrev lane (P:Preparation)(n:ℕ) (d:FieldPlan I):= relabel (sed P n) id d
abbrev opp (d:FieldPlan I):=relabel Shuttle.opposite Prod.swap d
abbrev legato (P:Preparation)(n:ℕ)(d:FieldPlan I):=opp (lane P n d)
abbrev trio (P:Preparation)(n:ℕ)(d:FieldPlan I) := league (legato P n d) (lane P n d)
include T
lemma MeasureAt.walk (n:ℕ)(h:MeasureAt d W R r): MeasureAt (lane P n d) (frontS P r W n) R r where
   hear i:=⟨(h.hear i).1, on_hand T n (h.hear i).2⟩
   see i:=on_foot T n (h.see i)
   feel i s:= (Prod.swap_swap _).trans (h.feel i s)
   touch i j e:= (h.touch i j (add_right_cancel e)).mono fun s u=> congrArg ((plane 3 (liftum P r n s)).flee ∘ (plane 3 0).flee) u
lemma MeasureAt.backward (h:MeasureAt d W R r): MeasureAt (opp d) (fun s=> rods 0 (W s)) R r where
   hear i:=⟨(h.hear i).1,back_hand (h.hear i).2⟩
   see i:=back_foot T (h.see i)
   feel i s:=congrArg Prod.swap (h.feel i s)
   touch i j e:= (h.touch i j (Shuttle.flip_inj e)).mono fun s u=> congrArg (plane 3 0).flee u

lemma MeasureAt.behind(n:ℕ)(h:MeasureAt d W R r): MeasureAt (legato P n d) (rearS P r W n) R r:=(h.walk T n).backward T -- dot
omit T
lemma MeasureAt.mix [Fintype J] {V:ℕ→J→Staff} {a:FieldPlan J}(h: MeasureAt d W R r)(u:MeasureAt a V R r)
   (q:∀ i j,(d.roles i).pt≠(a.roles j).pt) :
   MeasureAt (league d a) (fun s=>Sum.elim (W s) (V s)) R r:=by
 constructor
 · rintro (i|i); exact h.hear i; exact u.hear i
 · rintro (i|i); exact h.see i; exact u.see i
 · rintro (i|i); exact h.feel i; exact u.feel i
 rintro (i|i) (j|j)
 · exact h.touch i j
 · exact fun e=>(q i j e).elim
 · exact fun e=>(q j i e.symm).elim
 exact u.touch i j

lemma opposite_far (t:I→Gaia)(P:Preparation):∀ᶠ n in atTop, ∀ i j, shade P (t i) n ≠ leg P (t j) n:= Filter.eventually_all.mpr fun i=> Filter.eventually_all.mpr fun j=> (Shuttle.foreign P (t i) (t j)|>.eventually_gt_atTop 0).mono (fun n u=>dist_pos.mp u)
include T
lemma MeasureAt.nightwide (h:MeasureAt d W R r):
    ∀ᶠ n in atTop, MeasureAt (trio P n d) (nightS P r W n) R r:= (opposite_far (fun i=>(d.roles i).pt) P).mono (fun n u=> MeasureAt.mix (h.behind T n) (h.walk T n) u)

omit T
variable {S:Stencil I}
lemma castDust (h:Dusty d S): Dusty d (castDown S):= by intro t v; obtain ⟨i,z,rfl⟩:=List.mem_map.mp v; exact h i z

lemma swept (h:Dusty d S) (F:Gaia→Gaia)(G:Twah.DirSpin→Twah.DirSpin) (g: Injective F): Dusty (relabel F G d) S:= fun t v=>(h t v).imp fun {_ _} hx e=>hx (g e) -- tune
lemma eitherDust [Fintype J] {a:FieldPlan J} {U:Stencil J}
    (h:Dusty d S)(k:Dusty a U)(e:∀ i j,(d.hands i).p≠(a.hands j).p):
    Dusty (league d a) (S.remake Sum.inl * U.remake Sum.inr):=by
 intro t v; obtain ⟨i,q,l⟩:= List.mem_flatMap.mp v
 obtain ⟨j,q',rfl⟩:=List.mem_map.mp l; obtain ⟨x,p,rfl⟩:=List.mem_map.mp q; obtain ⟨y,p',rfl⟩:=List.mem_map.mp q'
 apply List.pairwise_append.mpr; refine ⟨List.pairwise_map.mpr (h _ p),List.pairwise_map.mpr (k _ p'),?_⟩
 intro i u j v; obtain ⟨x,_,rfl⟩:=List.mem_map.mp u; obtain ⟨y,_,rfl⟩:=List.mem_map.mp v; exact e x.1 y.1

lemma dustRight (n)(h:Dusty d S):Dusty (lane P n d) (dawn S):= castDust (castDust (swept h _ _ (fun _ _ e=>add_right_cancel e)))
lemma dustLeft (n)(h:Dusty d S):Dusty (legato P n d) (dusk S):=castDust (swept (dustRight n h) _ _ Shuttle.flip_inj)
lemma dustBoth (h:Dusty d S):∀ᶠ n in atTop,Dusty (trio P n d) (night S):= (opposite_far (fun i=>(d.hands i).p) P).mono (fun n u=> eitherDust (dustLeft n h) (dustRight n h) u)

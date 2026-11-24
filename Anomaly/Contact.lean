import Anomaly.PitchMark
import YM.CF.Buffered.StepIdentity
/-!
128--129. Bridge between the actual finite local Mark and the aperture
opening on the *same pane* including all its flags. Including in an ordered
product of stencil inputs. This file handles exact finite contact,
not polynomial pin/key budgeting yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Skye Jet Scroll Finset
open RG MeasureTheory Salt Metric Drapes Tulip Lat Branch Cube Tenant Rill
open Buffered StressExchange
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Moto Oath Font Haro Spire Dial
variable {N : Side}
local notation "Ω" => Single N

/-- Outer rim of the local observable. Use only with `offsetMask`
capturing any inspections to cardinal schedules (`PinLocal`). -/
def rootRim (b:BudgetPoint)(m:ℕ)(o:Site N) := offsetMask (b.B+12+2*m) o

structure Contact {N:Side} (K:Scree.Loom N)(S:Support (More N))(Y:Mark N)(V:phy N) : Prop where
  pitch : AtSupport false S Y
  oscillator : ∀ x:Orbit N, Sector (modesIn N S) false (V x)
  bra : ∀ x:Orbit N,
    acts (star (Y (x.1,K x))) (mateK N) = acts (star (V x)) (mateK N)

namespace Contact
variable {K:Scree.Loom N} {S: Support (More N)} {V V': phy N} {M M':Mark N} (h:Contact K S M V)

include h
lemma scale (z:ℂ): Contact K S (z • M) (z • V) :=
  ⟨h.pitch.smulM _, fun x=> (h.oscillator x).scale _, fun x=>by simp only [Pi.smul_apply,star_smul,act_smul,h.bra]⟩

lemma add (w:Contact K S M' V') : Contact K S (M+M') (V+V') :=
  ⟨h.pitch.addM w.pitch, fun x=> (h.oscillator x).add (w.oscillator x),fun x=>by simp only [Pi.add_apply,star_add,act_add,h.bra,w.bra]⟩

lemma sub (w:Contact K S M' V') : Contact K S (M-M') (V-V') := by
  simp_rw [sub_eq_add_neg]; simpa using h.add (w.scale (-1))

lemma money(x:Orbit N)(y:Phys N): letterRead (M (x.1,K x)) y= beamZ N (acts (V x) y):=by
  change inner ℂ (mateK N) (acts (M (x.1,K x)) y) = _
  unfold beamZ; rw [←act_inner,←act_inner,h.bra]
lemma currency(Z : Orbit N → Phys N) (den:ℂ) :
    markedRead M K Z/den=(∫ x, beamZ N (acts (V x) (Z x))∂city N)/den:= by
  unfold markedRead
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x=> h.money x (Z x))

omit h
lemma sum {ι:Type*}(t:Finset ι)(F:ι→Mark N)(Y:ι→phy N)(w:∀ i∈ t,Contact K S (F i) (Y i)):
    Contact K S (∑ i∈t,F i) (∑ i∈t,Y i) := by
  induction t using Finset.induction_on with
  | empty => rw [sum_empty,sum_empty]; exact ⟨AtSupport.zeroM,fun _=> Sector.zero _,fun _=>rfl⟩
  | insert i t v ih => rw [sum_insert v,sum_insert v]; exact (w i (mem_insert_self ..)).add (ih fun j v=>w j (mem_insert_of_mem v))

end Contact

variable {b:BudgetPoint} {r k m:ℕ} {t d a v : ℝ} {K : Scree.Loom N} (o : Site N)
    (h: Roof N t d r K) (l:0<d) (p:b.threshold≤t) (q:k+r+10≤b.B) (ha:0≤a)
variable {X:SOp N}(g:Trunk (node o) X k a v d)
include h l g p q ha

lemma bar_contact (w:24*m ≤ b.B) :
    Contact K (rootRim (N:=N) b m o) (gaugeMark b K o X)
      (houseK b (offsetMask b.B o) (blazePlate K X-barS0 N m o)) := by
  let V := offsetMask (b.B+12) o
  let S := rootRim (N:=N) b m o
  have hS : V ⊆ S := Corona.halo_mono (Nat.le_add_right ..) le_rfl
  refine ⟨(gaugeWindow o h l g p q ha).ticket.mono hS,?_,?_⟩
  · intro x
    by_cases hx:x∈ pingMask b (offsetMask b.B o)
    · rw [houseK, Set.indicator_of_mem hx]; dsimp only [blazePlate,Pi.sub_apply,barS0]
      let pA:= pair_charge (wind_support o m _ w)

      have v':offsetMask b.B o⊆S:= (Corona.halo_mono (Nat.le_add_right b.B 12) (le_refl ({node o}:Finset _))).trans hS
      have hu (A B : FC Ω)(p:Sector (modesIn N S) false A)(t:Sector (modesIn N S) false B) : Sector (modesIn N S) false (A-B):=by rw [sub_eq_add_neg]; exact p.add (by simpa only [neg_one_smul] using t.scale (-1:ℂ))
      exact hu _ _ (Sector.one.scale _) (hu _ _ (lift_v pA (modes_monotone v')) (Sector.one.scale _))
    rw [houseK, Set.indicator_of_notMem hx]; exact Sector.zero _
  intro x
  rw [show gaugeMark b K o X _=_ from (show gaugeMark b K o X (x.1,K x) = traceMeter b K o X x.1 • 1 from rfl),traceMeter,
    pinMatrix_eval h l g p q x, houseK]
  by_cases hx:x∈ pingMask b (offsetMask b.B o)
  · simp only [offsetMask] at hx ⊢; rw [Set.indicator_of_mem hx,Set.indicator_of_mem hx, Pi.sub_apply, star_sub,act_sub,
      barS0_bra o m x,sub_zero]
  simp only [offsetMask] at hx ⊢; rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem hx,Matrix.trace_zero,zero_smul]

lemma move_contact {y:Site N} (w:separation o y ≤ m):
    Contact K (rootRim (N:=N) b m o) (moveMark b K o y X) (coverLine K b o y X) := by
  let V:= offsetMask (b.B+12) y
  let S:= rootRim b m o
  let f := co_Ψ y o X
  have G:= g.station y
  let A:= pinMatrix b K (node y) f
  have he: V⊆ S:=shift_fits o y _ _ _ w le_rfl
  have hp(x:Orbit N) : coverLine K b o y X x=dg (A x.1) := by
    unfold A
    rw [pinMatrix_eval h l G p q x,coverLine,houseK]
    by_cases hx:x∈ pingMask b (offsetMask b.B y)
    · simp only [offsetMask] at hx ⊢; rw [Set.indicator_of_mem hx,Set.indicator_of_mem hx]
    simp only [offsetMask] at hx ⊢; rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem hx]; simp [dg,dyad]
  refine ⟨(spinWindow y h l G p q ha).ticket.mono he,fun x=> ?_,fun x=> ?_⟩
  · have v':offsetMask k y ⊆V:= Corona.halo_mono (show k≤b.B+12 by omega) le_rfl
    rw [hp]; exact lift_v (pair_charge (pinMatrix_support h l G p q x)) (modes_monotone (v'.trans he))
  rw [hp]; exact (bra_eq _ (Cascade.plus_P N) (mateK N) (tickB N)).symm

variable {Y:Axis→ SOp N} (w : ∀ i:Axis,Trunk (node o) (Y i) k a v d)
include w

theorem jointContact (v:24*m ≤ b.B) : Contact K (rootRim (N:=N) b m o)
    (jointMark b K o m X Y) (puffLine K b o Y X m) := by
  refine (bar_contact o h l p q ha g v).add (?_ : Contact K (rootRim b m o) (diffMark b K o m Y) (highLine K b o Y m))
  refine Contact.sum univ _ _ fun i _=> ?_
  exact (move_contact o h l p q ha (w i) (stopBeam o i m).1).sub (move_contact o h l p q ha (w i) (stopBeam o i m).2)

end YM.CF.Swell

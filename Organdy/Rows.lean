import Organdy.Cymbal
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra


variable {N:Side}
local notation "Ω"=>Single N

/-- no assumption on period; overlaps allowed with multiplicity. -/
lemma boxProp {Z:Type*}[AddCommMonoid Z](Q:ℕ → Z→Prop)(m:ℕ)
 (L:List Axis)(x:Site N)
 (h: Q 0 0) (u:∀ j k a b,Q j a→ Q k b→ Q (j+k) (a+b))
 (f:Site N→ Z)
 (g:∀ y:Site N,separation x y≤L.length*(3*m) → Q 1 (f y)) :
 Q ((2*m)^L.length) (squareSum f m L x):=by
 have inS(J:ℕ)(A:Finset ℕ)(F:ℕ→Z)(p:∀ i∈A,Q J (F i)): Q (A.card*J) (∑ i∈A,F i):=by
    induction A using Finset.induction_on with
    |empty=> simpa using h
    |insert i t v ih=>rw [card_insert_of_notMem v,sum_insert v,
                     show (t.card+1)*J=J+t.card*J by ring]
                      ; exact u _ _ _ _ (p i (mem_insert_self ..)) (ih (fun j t' =>p _ (mem_insert_of_mem t')))
 induction L generalizing x with
 |nil=>rw [List.length_nil,pow_zero]; exact g x (by simp [separation_self])
 |cons i L ih=>
    have h' := inS ((2*m)^L.length) (range (2*m))
     (fun j=> squareSum f m L (moveSite (x-m • step i) i (j+1))) (fun j v=>ih _
        (fun y w=>g _ ((separation_triangle x _ y).trans ((Nat.add_le_add (leap_strip x i m j (mem_range.mp v)) w).trans (by rw [List.length_cons]; exact Nat.le_of_eq (by ring))))))
    · rw [List.length_cons,pow_succ']
      rwa [card_range] at h'


lemma mill_Q(x:Site N):millQ x = cutM ((univ:Finset Ω).filter (fun i=>i.1.1=x)):=by
 ext ⟨⟨y,i⟩,a⟩ ⟨⟨z,j⟩,b⟩
 simp only [millQ, Matrix.sum_apply, panel, Matrix.of_apply,cutM,Matrix.diagonal_apply,Matrix.one_apply,Prod.mk.injEq,mem_filter,mem_univ,true_and]
 simp [ite_and]; split_ifs with h <;> simp_all -- tune

lemma cutM_edge {I:Type*}[Fintype I][DecidableEq I](S T:Finset I): Commute (cutM S) (cutM T):=by
 change _*_=_*_
 rw [cutM,cutM,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
 congr 1; funext; exact mul_comm ..
lemma tick_wing(m:ℕ)(x:Site N)(S:Support (More N))
  (p:lensBox (24*m) (node x)⊆ S):
    Commute (tickA N) (windmill x m)∧
    cutM (modesIn N S)*windmill x m *cutM (modesIn N S)=windmill x m:= by
 let A:=tickA N; let M:=modesIn N S; let B:=cutM M
 let Q(_ :ℕ)(Z:Op Ω):= Commute A Z∧ B*Z*B=Z
 have t (j k:ℕ)(X Y:Op Ω)(u:Q j X)(v:Q k Y): Q (j+k) (X+Y):=
    ⟨u.1.add_right v.1,by rw [mul_add,add_mul,u.2,v.2]⟩

 refine boxProp Q m _ x ⟨Commute.zero_right _,by simp⟩ t _ (fun y v=>?_)
 have hp:separation (node x) (node y)≤24*m:=by rw [Hove.ζdist]; have xv: separation x y ≤4*(3*m):=v; omega
 have h: node y ∈ S:=p (halo_spec.mpr ⟨_,mem_singleton_self _,hp⟩)
 rw [mill_Q]
 refine ⟨by simp only [A,touchP]; exact cutM_edge ..,?_⟩
 let T:Finset Ω:=(univ:Finset Ω).filter (fun i=>i.1.1=y)
 have k: cutM T*cutM T=cutM T:= (cutM_idp _).isIdempotentElem
 refine cutCover (s:=T) (X:=cutM T) (by rw [k,k]) ?_
 intro z e; exact (modes_at S z).mpr ((mem_filter.mp e).2.symm ▸ h)

lemma barOrder (x:Site N)(m:ℕ) (S:Support (More N))(p:lensBox (24*m) (node x)⊆S):
 let W:= barS0 N m x
 ∀ U, Sector (modesIn N S) false (W U) ∧
   acts (star (W U)) (mateK N)=0:=by
 obtain ⟨u,v⟩:=tick_wing m x S p
 intro W U
 change Sector _ _ (dg (windmill x m)-Matrix.trace _ • 1) ∧ acts (star (dg (windmill x m)-Matrix.trace _ • 1)) _=_
 rw [star_sub,star_smul,star_one,act_sub,act_smul,act_one,sandwichV _ (by rw [touchP]; exact cutM_idp _) u _ (tickB N)]
 refine ⟨?_,sub_self _⟩
 rw [sub_eq_add_neg, ←neg_smul]
 exact (pair_charge v).add (Sector.one.scale _)

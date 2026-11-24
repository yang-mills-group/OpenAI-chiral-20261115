import Merino.Garter.Core
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Garter
open Function Lattice Finset RG Wilson Metric Exterior Work.F03
open Regis.Head MeasureTheory
open scoped Topology ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}

open Cuff Hem
variable {I:Type*}
open Tree Filter Precision Next.Rank.Spindle Pressure ProbabilityTheory
open Gleam Next.SectorChange Next.SectorChange.Gaussian
open Etch -- (includes river)
open StepIn
variable {c:Side}{r:Ratio c n}{H:Bed}{m:ℕ}{p:BudgetPoint}{q:Clip}{v η S C δ w β:ℝ}{A:Support c}{N:Finset (Cell n)}{Z:PathData G}
 
lemma ball_large(x:Site n)(d:ℕ)(t:2*d≤n.val):d+1≤(baseball d x).card:=by
 let y(i:ℕ):Cover:=fun _=>(i:ℤ)
 let z(i):=x+wrap n (y i)
 let R:=range (d+1)
 have p0:0<n.val:=n.property
 have h(i:ℕ)(p:i∈R):Lattice.lift (wrap n (y i))=y i:=
   lift_eq_iff.mpr ⟨rfl,fun _=>by have hi:=mem_range.mp p; unfold y; constructor <;> omega⟩
 have u:Set.InjOn z R:=by
   intro i hi j hj p
   have he:wrap n (y i)=wrap n (y j):=add_left_cancel p
   have hu:=congrArg Lattice.lift he; rw [h i hi,h j hj] at hu
   exact Nat.cast_injective (R:=ℤ) (congr_fun hu 0)
 rw [← card_range (d+1),← card_image_iff.mpr u]
 refine card_le_card (fun i hi=>?_)
 obtain ⟨i,p,rfl⟩:=mem_image.mp hi
 refine halo_spec.mpr ⟨x,mem_singleton_self _,?_⟩
 rw [separation_comm,separation,show z i - x=wrap n (y i) from add_sub_cancel_left ..]
 unfold pdist; rw [h i p]
 exact Finset.sup_le fun _ _=> (by simpa [y] using Nat.le_of_lt_succ (mem_range.mp p))


variable [Fintype I]
abbrev uncalled(r:Ratio c n)(m:ℕ)(A)(N)(j:I→StepIn n):=
 univ.filter fun i:I=>¬Deep r A N (living m) (j i).there

lemma field_gate (e:Odd r.count.val)(u:hallBill m≤r.count.val/2)(j:I→StepIn n)
   (h:Packs (wiggle m) j):
    (uncalled r m A N j).card*(wiggle m+1)≤ surfaceBill r (hallBill m) A N:=by
 let X:=uncalled r m A N j
 let F(i:I):=baseball (wiggle m) (j i).there
 have k:2*wiggle m≤n.val:=by
   rw [r.exact_size]
   apply le_trans _ (Nat.le_mul_of_pos_left r.count.val c.property)
   unfold hallBill Sequest at u; unfold wiggle; omega
 have v:(X.biUnion F).card=∑ i∈X,(F i).card:=
   card_biUnion fun i _ d _ ht=>h ht
 refine ((sum_le_sum (s:=X) fun i _=>ball_large (j i).there (wiggle m) k)
   |>.trans ((v.ge).trans ((card_le_card ?_).trans (field_wall (A:=A) (W:=N) e u)))) |>.trans' (le_of_eq (by simp [X]))
 intro x hx; obtain ⟨i,p,z⟩:=mem_biUnion.mp hx
 refine mem_filter.mpr ⟨mem_univ _,fun d=>(mem_filter.mp p).2 (d.turn ?_)⟩
 have y: separation x (j i).there ≤wiggle m:=by
   rw [separation_comm]; simpa [F,baseball,halo_spec] using z
 unfold living; apply (Nat.add_le_add_right y _).trans; unfold hallBill Sequest wiggle; omega



lemma gates (e:Odd r.count.val)(u:hallBill m ≤ r.count.val/2){g:Duo n}{j:I→StepIn n}
   (h:Pavilion (wiggle m) g j)(F:I→ℝ){D:ℝ}(z:0≤D)
   (b:∀ i,F i≤(wiggle m:ℝ)+1)
   (y:∀ i,Deep r A N (living m) (j i * g.1).there →
           Deep r A N (living m) (j i * g.2).there→ F i ≤ D):
   2*(∑ i,F i) ≤ 2 * (Fintype.card I*D)+fritTrap r m A N:=by
 let X:=uncalled r m A N (fun i=>j i*g.1)
 let Y:=uncalled r m A N (fun i=>j i*g.2)
 let R(i:I):= D+(if i∈X then (wiggle m:ℝ)+1 else 0)+(if i∈Y then (wiggle m:ℝ)+1 else 0)
 have w: ∀ i,F i≤R i:=by
   intro i; unfold R
   split
   · exact (b i).trans ((le_add_of_nonneg_left z).trans (le_add_of_nonneg_right (by split;positivity; simp)))
   next p=>
     rw [add_zero]
     split
     · exact (b i).trans (le_add_of_nonneg_left z)
     next q=>
       rw [add_zero]; apply y
       · simpa [X,uncalled] using p
       simpa [Y,uncalled] using q


 refine (mul_le_mul_of_nonneg_left (sum_le_sum (s:=univ) fun i _=>w i) zero_le_two).trans ?_
 unfold R
 rw [sum_add_distrib,sum_add_distrib,←sum_filter,←sum_filter]
 simp only [sum_const,nsmul_eq_mul,card_univ,filter_mem_eq_inter,univ_inter]
 let T:ℝ:=surfaceBill r (hallBill m) A N
 have d:X.card*((wiggle m:ℝ)+1)≤T := by
    unfold T; exact_mod_cast (field_gate (A:=A) (N:=N) e u _ h.1)
 have d':Y.card*((wiggle m:ℝ)+1)≤T:= by
    unfold T; exact_mod_cast (field_gate (A:=A) (N:=N) e u _ h.2)
 rw [show fritTrap r m A N=4*T from by unfold fritTrap T surfaceBill; push_cast; rfl]
 linarith only [d,d']
end YM.CF.Merino.Garter

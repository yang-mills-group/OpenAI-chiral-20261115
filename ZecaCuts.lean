import ZecaNova
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)
local notation "R" => saucer S

open Poin Tower.Aria

variable {α:Type}(t y z:α→ℝ)(L:List α)

structure Drape :Prop where
 inner : ∀i∈L,y i<t i ∧ t i<z i
 seam : ∀i j (u v:List α), L=u++i::j::v → z i=y j

lemma drape_get (h:L.Pairwise fun i j=> t i < t j): ∃ y z,Drape t y z L:=by
 classical
 have v:L.Nodup:=h.imp (by intro i j p; exact (ne_of_apply_ne _ p.ne)) --?
 obtain ⟨C⟩:=choose_curtains t t L v (weaves_sorted t t L h)
 exact ⟨C.first,C.last,fun i p=>⟨C.inside i p,C.outside i p⟩,C.joins⟩

variable {t y z L}
lemma Drape.tail {i}(d:Drape t y z (i::L)):Drape t y z L:=
   ⟨fun j h=>d.inner j (List.mem_cons_of_mem i h),
    fun j k s v w=> d.seam j k (i::s) v (by rw [w];rfl)⟩

lemma Drape.order (d:Drape t y z L): L.Pairwise fun i j=> z i ≤ y j:=by
 induction L with
 | nil=>simp
 | cons i L ih=>
   have e := ih d.tail
   refine List.pairwise_cons.mpr ⟨?_,e⟩
   intro j h
   cases L with
   | nil=>simp at h
   | cons k L=>
      rw [d.seam i k [] L rfl]
      rcases List.mem_cons.mp h with rfl | u
      · exact le_rfl
      obtain ⟨a,b⟩:= d.tail.inner k List.mem_cons_self
      exact (a.trans b).le.trans (List.pairwise_cons.mp e|>.1 _ u)

abbrev frontP (t y:α→ℝ)(i:α):ℝ≥0:=(t i-y i).toNNReal
abbrev rearP (t z:α→ℝ)(i:α):ℝ≥0:=(z i-t i).toNNReal
lemma Drape.pair (d:Drape t y z L):
 L.Pairwise (padBefore t (frontP t y) (rearP t z)):=by
 -- imp_of_mem
 apply d.order.imp_of_mem
 intro i j p q h
 unfold padBefore frontP rearP
 rw [Real.coe_toNNReal _ (sub_nonneg.mpr (d.inner i p).2.le),
     Real.coe_toNNReal _ (sub_nonneg.mpr (d.inner j q).1.le),add_sub_cancel,sub_sub_cancel]
 exact h

variable (D:α→Moment H)(sp:α→Cross a)
local notation "X"=> padOp S D sp (frontP t y) (rearP t z)
local notation "Y"=> padGap S t (frontP t y) (rearP t z)
lemma drapeNil (d:Drape t y z L): Film X Y L = (L.map X).prod:=by
 induction L with
 | nil=>rfl
 | cons i L ih=>
    rw [Film_step,ih d.tail,List.map_cons,List.prod_cons]
    cases L with
    | nil=>simp [clip]
    | cons k L=>
       rw [show clip Y i (k::L)=1 from ?_,one_mul]
       have p:= (d.inner i (by simp)).2.le
       have q:= (d.inner k (by simp)).1.le
       change S.E (Real.toNNReal (t k - (frontP t y k)-(t i+(rearP t z i))))=1
       unfold frontP rearP
       rw [Real.coe_toNNReal _ (sub_nonneg.mpr p),
          Real.coe_toNNReal _ (sub_nonneg.mpr q),add_sub_cancel,sub_sub_cancel,
          d.seam i k [] L rfl,sub_self, Real.toNNReal_zero,S.eZero]
       rfl

lemma quoteCuts (Ω:H)(o:R Ω=Ω) (d:Drape t y z L):
 quoteL S Ω D sp t L =
 inner ℂ Ω ((L.map X).prod Ω) :=by
 rw [quoteL_paid S Ω D sp t (frontP t y) (rearP t z) o _
    (fun i u=> Real.toNNReal_pos.mpr (sub_pos.mpr (d.inner i u).1))
    (fun i u=> Real.toNNReal_pos.mpr (sub_pos.mpr (d.inner i u).2)) d.pair]
 unfold quotePaid; rw [drapeNil S D sp d]

end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca

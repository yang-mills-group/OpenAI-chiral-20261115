import YM.CF.Font.Trail
/-! # Torus edge update, unit-forward-minus-backward (Stratum 1 of Eq.126)

 No picture payment required (replace grid assumptions). Pay incidence up to radius.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.StressExchange
open Function Filter Metric Lattice Finset
open scoped Topology BigOperators Classical
variable {N:Side}
abbrev LinksV (N:Side)(M:Type*):= Edge (Site N)→ M
variable {M:Type*}[AddCommGroup M]
def desc (J:LinksV N M) (x:Site N) : M := ∑ i:Axis, (J (x,i)-J (x-step i,i))
lemma desc_add (J K:LinksV N M) (x:Site N):desc (J+K) x=desc J x+desc K x:=by unfold desc; rw [←sum_add_distrib]; apply sum_congr rfl; intro i _; rw [Pi.add_apply,Pi.add_apply]; abel
lemma desc_sum {I:Type*}(S:Finset I)(J:I→LinksV N M)(x:Site N):desc (∑ i ∈ S,J i) x=∑ i ∈ S,desc (J i) x:=by induction S using Finset.cons_induction with| empty=> simp [desc]| cons a L p h=>rw [sum_cons,sum_cons,desc_add,h]
/-- scalar-free shipment -/
def posFlux (a:Edge (Site N)) (Y:M): LinksV N M:= Pi.single a Y
lemma desc_pos (x y:Site N)(d:Axis)(Y:M): desc (posFlux (y,d) Y) x= (if x=y then Y else 0)-(if x=y+step d then Y else 0):=by
 classical
 unfold desc; rw [sum_eq_single d]
 · unfold posFlux; rw [Pi.single_apply,Pi.single_apply]; simp only [show (x,d)=(y,d) ↔ x=y by simp,show (x-step d,d)=(y,d) ↔ x=y+step d by simp [sub_eq_iff_eq_add]]
 · intro i _ u; simp [posFlux,u,Pi.single_apply]
 simp
def sendFlux (x:Site N)(W:Walk)(Y:M) : LinksV N M := match W with
 | [] => 0
 | s::t => posFlux (s.used x) (if s.neg then -Y else Y) + sendFlux (x+s.vec) t Y
lemma shipping (x y:Site N)(W:Walk)(Y:M) : desc (sendFlux y W Y) x=(if x=y then Y else 0)-(if x=stop y W then Y else 0):=by
 induction W generalizing y with
 | nil=> by_cases x=y <;> simp_all [sendFlux,desc,stop]
 | cons d W ih=>
    rcases d with ⟨i,z⟩; cases z
    · change desc (posFlux (y,i) Y+sendFlux (y+step i) W Y) x=_; rw [desc_add,desc_pos,ih]; change _=_-(if x=stop (y+step i) W then Y else 0); abel
    change desc (posFlux (y-step i,i) (-Y)+sendFlux (y+ -step i) W Y) x=_-(if x=stop (y+ -step i) W then Y else 0)
    rw [desc_add,desc_pos,←sub_eq_add_neg, ih,sub_add_cancel]; split_ifs<;>abel
lemma notFar (x:Site N)(e:Edge (Site N))(W:Walk)(Y:M)(p: sendFlux x W Y e ≠ 0) : separation x e.1 ≤ W.length∧ separation x (e.1+step e.2) ≤ W.length := by
 induction W generalizing x with
 | nil=> exact False.elim (p rfl)
 | cons d W ih=>
   have hu:separation x (x+d.vec)≤ 1:= Font.small x d
   by_cases b:e=d.used x; swap
   · rw [sendFlux,Pi.add_apply,posFlux, Pi.single_apply, if_neg b, zero_add] at p; obtain ⟨w,v⟩:=ih _ p
     rw [List.length_cons,add_comm _ 1]; exact ⟨(separation_triangle x _ _).trans (add_le_add hu w),(separation_triangle x _ _).trans (add_le_add hu v)⟩
   rw [b]; unfold Step.used; split
   next g=> rw [Step.vec,if_pos g,←sub_eq_add_neg] at hu; exact ⟨hu.trans (by simp),by simp⟩ -- unused generalization e ih? ok
   next g=> rw [Step.vec,if_neg g] at hu; exact ⟨by simp,hu.trans (by simp)⟩
lemma flux_pay {M:Type*}[NormedAddCommGroup M](x:Site N)(W:Walk)(e:Edge (Site N))(Y:M) : ‖sendFlux x W Y e‖ ≤ W.length*‖Y‖:=by
 induction W generalizing x with
 | nil=> simp [sendFlux]
 | cons d W h =>
   rw [sendFlux,Pi.add_apply]; apply le_trans (norm_add_le _ _); rw [List.length_cons,Nat.cast_add,Nat.cast_one, add_comm _ 1,add_mul,one_mul]; apply add_le_add _ (h _);
   unfold posFlux; rw [Pi.single_apply]; split; next _=>cases d.neg<;>simp
   next _=>simp

variable (X:Site N→Site N→M)
def micropath (e:Edge (Site N)) : M:=∑ x:Site N,∑ y:Site N, sendFlux x (Font.shiftH x y) (X x y) e
lemma routes (x:Site N): desc (micropath X) x=∑ y:Site N,(X x y-X y x):=by
 have ht: micropath X=∑ x:Site N,∑ y:Site N, sendFlux x (Font.shiftH x y) (X x y):=by ext; simp only [Finset.sum_apply,micropath] -- tune
 rw [ht]; simp_rw [desc_sum,shipping,Font.stopH,sum_sub_distrib]; rw [sum_comm (f:=fun y z=> if x=y then X y z else 0)]; simp
end YM.CF.StressExchange

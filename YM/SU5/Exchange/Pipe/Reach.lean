import YM.CF.Font.Trail
set_option autoImplicit false
noncomputable section
namespace YM.CF.Font
open Function Filter Lattice Finset Exterior
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {n:Side} (x z:Site n)
abbrev spit (b:Edge (Site n))(c:Edge (Site n)):ℝ:= if c=b then 1 else 0
abbrev arcFuel (W:Walk)(a:Axis):= linkSum (spit (z,a)) x W
lemma arcFee (W:Walk)(a:Axis): |arcFuel x z W a|≤ W.length:=by
 induction W generalizing x with
 |nil=> simp [arcFuel,linkSum]
 |cons j l h=> rw [arcFuel,linkSum]; let U:ℝ:= if j.neg then -spit (z,a) (j.used x) else spit (z,a) (j.used x); have he:|U|≤1:=by unfold U spit; split_ifs <;> norm_num
               exact (abs_add_le ..).trans ((add_le_add he (h _)).trans_eq (by simp [add_comm]))
lemma arcPaid (W:Walk)(a:Axis)(p: arcFuel x z W a≠0):separation x z≤ W.length:=by
 induction W generalizing x with
 |nil => exact False.elim (p rfl)
 |cons j l h=>
    let y:= x+j.vec; have hg:separation x y≤1 := small x j; by_cases v:arcFuel y z l a=0; swap
    · exact (separation_triangle x y z).trans ((add_le_add hg (h y v)).trans_eq (by simp [Nat.add_comm]))
    have he:j.used x=(z,a):=by by_contra h; apply p; unfold arcFuel; rw [linkSum,show linkSum (spit (z,a)) y l=0 from v]; unfold spit; rw [if_neg h]; split<;>simp
    rw [Step.used] at he; split_ifs at he with u
    · change ((x-step j.dir,j.dir):Edge (Site n))=_ at he; have hx:y=z:=by unfold y; rw [Step.vec,if_pos u,← sub_eq_add_neg]; exact (Prod.ext_iff.mp he).1
      rw [←hx]; exact hg.trans (by simp)
    rw [show x=z from (Prod.ext_iff.mp he).1,separation_self]; exact Nat.zero_le _

private lemma peekEdge (c:Edge (Site n)): (∑ a:Axis,(spit (x,a) c - spit (x-step a,a) c))=(if x=c.1 then 1 else 0)-(if x=c.1+step c.2 then 1 else 0):=by
 rw [sum_eq_single c.2]; unfold spit; let a:=c.2; rcases c with ⟨i,j⟩
 · simp only [Prod.mk.injEq,and_true]; simp_rw [show (i=x) ↔ x=i from eq_comm, show (i=x-step j) ↔ x=i+step j from Iff.trans eq_comm sub_eq_iff_eq_add ]
 · intro j _ h; have hm:j≠c.2:=h; unfold spit; simp [Prod.ext_iff,hm.symm]
 simp
lemma arcShift (W:Walk)(t:Site n)(a:Axis): arcFuel (x+t) (z+t) W a=arcFuel x z W a:=by
 induction W generalizing x with
 |nil=>rfl
 |cons j l h=>
    unfold arcFuel; rw [linkSum,linkSum]; rw [show x+t+j.vec = x+j.vec+t by abel, show linkSum _ _ l=_ from h (x+j.vec)]; congr 1
    unfold spit Step.used; by_cases p:j.neg=true; · simp [p,show x+t-step j.dir=x-step j.dir+t from by abel]
    simp [p]
lemma arcCharge (W:Walk): (∑ a:Axis,(arcFuel x z W a-arcFuel x (z-step a) W a))=(if z=x then 1 else 0)-(if z=stop x W then 1 else 0):=by
 induction W generalizing x with
 |nil => simp [arcFuel,linkSum,stop]; split_ifs <;> ring
 |cons j l h=>
    let c:=j.used x; let y:= x+j.vec
    let σ(a:Axis):ℝ:= if j.neg then -(spit (z,a) c-spit (z-step a,a) c) else spit (z,a) c-spit (z-step a,a) c
    have he:(∑ a:Axis,σ a)=(if z=x then 1 else 0)-(if z=y then 1 else 0):=by
       rcases j with ⟨b,g⟩; cases g
       · unfold σ; simp only [Bool.false_eq_true,ite_false]; exact (peekEdge z c).trans (by rfl)
       unfold σ; simp_rw [ite_true,sum_neg_distrib,peekEdge]; simp only [c,y,Step.used,Step.vec,ite_true]; rw [←sub_eq_add_neg,sub_add_cancel]; abel
    have hp(a:Axis): arcFuel x z (j::l) a- arcFuel x (z-step a) (j::l) a=σ a+(arcFuel y z l a-arcFuel y (z-step a) l a):=by
       unfold arcFuel σ; rw [linkSum,linkSum]; dsimp only [y,c]; split_ifs<;>abel
    simp_rw [hp]; rw [sum_add_distrib,he,h]; unfold y; rw [stop]; abel
abbrev pipeFlow (x y z:Site n)(a:Axis):= arcFuel x z (shiftH x y) a
lemma pipeHome (y:Site n)(a:Axis)(v:pipeFlow x y z a≠0):separation x z ≤ 4*separation x y:= (arcPaid x z (shiftH x y) a v).trans (short x y)
lemma pipeStep(y t:Site n)(a:Axis): pipeFlow (x+t) (y+t) (z+t) a=pipeFlow x y z a:=by
 unfold pipeFlow; rw [show shiftH (x+t) (y+t)=shiftH x y from (by unfold shiftH; rw [add_sub_add_right_eq_sub]),arcShift]
lemma pipeBill(y:Site n)(a:Axis): |pipeFlow x y z a|≤ 4* (separation x y:ℝ):=by
 apply (arcFee ..).trans; exact_mod_cast (short x y)
lemma pipeBirth (y:Site n): (∑ a:Axis,(pipeFlow x y z a-pipeFlow x y (z-step a) a))=(if z=x then 1 else 0)-(if z=y then 1 else 0):=by simpa only [pipeFlow,stopH] using arcCharge x z (shiftH x y)
end YM.CF.Font

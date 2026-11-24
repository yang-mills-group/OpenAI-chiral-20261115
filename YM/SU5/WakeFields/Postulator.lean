import YM.CF.Emu.Fez
--! small closed formulas are much simpler with fast recursion. Use FORMAL Fock on labels; works even for nonskew d.
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.Emu.Postulator
open Fock MeasureTheory Function LinearMap Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff BigOperators
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I] [Fintype I]
variable (d:I→I→ℂ)

abbrev fakeA (i:I) : FC I:= ∑ j, d i j • takeF j
abbrev fakeC (i:I) : FC I := put i + fakeA d i
local notation "p"=> Fock.vacuum I

lemma lose (i:I): acts (fakeA d i) (Fock.vacuum I)=0:=by
  rw [fakeA,act_sum]; apply sum_eq_zero; intro j _; rw [act_smul,←remove_take,vacuum_take,smul_zero]
lemma oblige (i:I)(x: Wave I): inner ℂ p (acts (put i) x)=0:=by
  rw [←act_inner]; change inner ℂ (acts (takeF i) p) x=_; rw [←remove_take,vacuum_take,inner_zero_left]
lemma ret (i j:I): antiB (fakeA d i) (put j)=d i j • 1:=by
 rw [fakeA,antiB_sum]; simp_rw [antiB_smul,antiB,mixed]; simp
lemma retrace (i j:I) : antiB (fakeA d i) (fakeC d j)=d i j •1:=by
  rw [fakeC, show ∀ a b c:FC I, antiB a (b+c)=antiB a b+antiB a c from (fun a b c=> by unfold antiB; rw [mul_add,add_mul]; abel), ret]
  unfold fakeA; simp_rw [antiB_sum,antiB_sum',antiB_smul,antiB_smul',antiB,take_take]; simp
lemma earns (l:List I): inner ℂ p (chime (fakeC d) p l)= Emu.runes d l:=by
  have hm (c:Cl I): inner ℂ p (invest put p d c)= spinC d c:=by
    rw [invest,inner_smul_right]; cases h:c.term with
    | nil=> rw [emptyChime]; simp [spinC,h,vacuum]; -- `basis_apply` simp
    | cons i l=>rw [charm,oblige]; simp [spinC,h]
  rw [shadeW (fakeC d) put (fakeA d) p d (lose d) (ret d) (fun i=>rfl)]; unfold runes; generalize claps l=L; induction L with|nil=> simp|cons a l ih=> simp only [List.map_cons,List.sum_cons,inner_add_right]; rw [ih,hm]

-- initial linear order instance may hamper Stamp. provide using locally chosen LinearOrder with Classical.
lemma readOrdered (i:I)(l:List I): runes d (i::l)= ((picks l).map (fun g=> cval g.neg*d i g.front*runes d g.back)).sum:=by
  rw [←earns,charm,fakeC,act_add,inner_add_right,oblige,zero_add, plume (fakeC d) (fakeA d) p d (lose d) (retrace d)]; generalize picks l=t
  induction t with
  | nil=> simp
  | cons x l ih=> simp only [List.map_cons,List.sum_cons,inner_add_right,ih]; rw [seatsC,inner_smul_right,earns]
omit [LinearOrder I] in
lemma readHead (i:I)(l:List I): runes d (i::l)= ((picks l).map (fun g=> cval g.neg*d i g.front*runes d g.back)).sum:=by
  classical
  letI := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective; exact readOrdered d i l
omit [LinearOrder I] [Fintype I] in
lemma empt : runes d []=1:=by simp [runes,claps,spinC,offer,cval]
#print axioms readHead
end YM.CF.Emu.Postulator

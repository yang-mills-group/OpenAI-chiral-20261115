import YM.CF.DPress.FD.Law.Muse
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Finset Cash
open scoped Topology BigOperators ENNReal NNReal Classical
variable {n:Side} {r k:ℕ}
-- independent random finite bells indexed by sites or pieces. use any one chosen anchor; need reads on *all* piece sites whenever an item is consulted. rotation need not respect arbitrary-choice anchors in setoids of implementation.
namespace Sat
open Deck
variable {I J K: Type*}[Fintype I][DecidableEq I][Fintype J][Nonempty J]
abbrev Bell(I J:Type*):= I→J
abbrev pool(r:ℕ)(Q:I→Site n)(J:Type*)[Fintype J][Nonempty J] :Vision n r (I→ J) := Vision.bunch (fun i=> Vision.harsh (Q i) be_J)
lemma single_p {V:I→Site n}(X:Support n)(p q: I→J)(y:I)(t:V y∈X) (h:(pool r V J).looks X p q) :p y=q y:=by
 have he: (if V y∈ X then ruleFx (fun j:J=>j) else Keep J).r _ _:=(h y); rw [if_pos t] at he; exact he
lemma flat (r:ℕ)(Q:I→Site n)(x:I→J) : (pool r Q J).c.μ x = ((Fintype.card J:ℝ)⁻¹)^(Fintype.card I):=by change ∏ i:I, ((Fintype.card J:ℝ)⁻¹)=_; simp
lemma chooseB (r:ℕ)(Q:I→Site n)(P:Equiv.Perm (I→J)) : Chooses (pool r Q J).c P:=fun i=>by rw [flat,flat] -- permits read
abbrev key(S:Support n):Site n:= if p:S.Nonempty then p.choose else 0
lemma tithe (S:Support n)(h:S.Nonempty): key S ∈ S:=by rw [key,dif_pos h]; exact h.choose_spec
-- general draw for each support.G. To augment with pad.
def bonus (f:Equiv.Perm I)(g:∀ i:I,Equiv.Perm J):Equiv.Perm (I→J) :=⟨fun x i=> g i (x (f i)),fun y i=> (g (f.symm i)).symm (y (f.symm i)),fun i=> by ext; simp, fun i=> by ext; simp⟩ -- tune g notation `unused i`
def hull (s:Equiv.Perm (Site n)): Equiv.Perm (Support n):= Equiv.finsetCongr s
-- want image def formula.
lemma eqV(s:Equiv.Perm (Site n))(A:Support n) : hull s A=A.image s:=by unfold hull; rw [Equiv.finsetCongr_apply]; exact map_eq_image ..
end Sat
end YM.CF.DPress.FD

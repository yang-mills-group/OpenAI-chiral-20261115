import YM.CF.Cadre.Lope
import Mathlib.RingTheory.PowerSeries.Derivative
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
-- P supports meeting kernel leaf Y
-- exact chain rule on disjoint poly family including marks
variable {B:Type*}
section
variable [CommSemiring B]
abbrev sandX (X G:Type*):= Σ (_:X), G
local notation "W1"=> @Sigma ΣA (fun _=>ΣG)
local notation "Q2"=> @Sigma ΣG (fun _=>W1)
def mint(Y:ΣA)(O:Finset A): Finset Q2:=Finset.sigma (stream O) fun F=> F.sigma fun X=> drum X Y (O∩X.val)
lemma caddy(Y:ΣA)(P:ΣG): Disjoint (grab Y P) (farR Y P):=disjoint_sdiff
lemma yin (Z: W1) (H:ΣG)(p:(⟨H,Z⟩:Q2)∈mint Y O):H∈stream O∧Z.1∈H∧Z.2∈drum Z.1 Y (O∩Z.1.val):=let h:=mem_sigma.mp p; ⟨h.1,mem_sigma.mp h.2⟩
lemma yul (U:ΣA→ΣG→B)(K:ΣG→ B):
 (∑ F∈stream O,∑ X∈F, (∑ T∈ drum X Y (O∩X.val), U X T)*K (F.erase X))=
 ∑ G∈ stream O,U (glueV Y (grab Y G)) (grab Y G)*K (farR Y G):=by
 let V(F:ΣG)(w:W1):=U w.1 w.2*K (F.erase w.1); let M:=mint Y O
 rw [show (∑ F∈stream O, ∑ X∈F,_)=∑ w∈M,V w.1 w.2 from ?_]; swap; · unfold M; rw [mint,sum_sigma]; apply sum_congr rfl; intro i _; rw [sum_sigma]; apply sum_congr rfl; intro j _; rw [sum_mul]; -- tune
 let N:=stream O; let η(G:ΣG):Q2:= ⟨insert (glueV Y (grab Y G)) (farR Y G), ⟨glueV Y (grab Y G), grab Y G⟩⟩; let f(w:Q2):=w.2.2∪w.1.erase w.2.1
 have ht(G:ΣG)(h:G∈N):η G∈M∧f (η G)=G:=by
    obtain ⟨v,k,u⟩:= drive Y O G h; refine ⟨mem_sigma.mpr ⟨k,mem_sigma.mpr ⟨mem_insert_self .., v⟩⟩,?_⟩
    change grab Y G ∪ (insert _ _ : Finset _).erase _= G; rw [erase_insert u,race]
 have he(w:Q2)(h:w∈M): f w∈N∧η (f w)=w:=by
    rcases w with ⟨j,a,q⟩; obtain ⟨p,g,v⟩:=yin Y O ⟨a,q⟩ j h; obtain ⟨u,t,hx,l⟩:=sideR Y O j p a g q v
    refine ⟨u,?_⟩; unfold η f; dsimp only; rw [t,hx,l,insert_erase g]
 symm; refine sum_bij (fun a _=>η a) (fun a h=> (ht a h).1) (fun a h j v g=> ((ht a h).2.symm.trans ((congrArg f g).trans (ht j v).2))) (fun a i=> ⟨_,(he a i).1,(he a i).2⟩) ?_
 intro G p; unfold η V; dsimp only; rw [erase_insert (drive Y O G p).2.2]
end
section
variable [CommRing B]
open PowerSeries
abbrev silo (B:Type*):= PowerSeries B
abbrev sailZ (A B:Type*):=Palot.leaf A→ PowerSeries B
lemma ladZ {ι:Type*}[DecidableEq ι] (I:Finset ι)(P:ι→PowerSeries B):derivative B (∏ i∈I,P i)=∑ i∈I, derivative B (P i)*∏ j∈I.erase i,P j:=by
 induction I using Finset.induction_on with
 |empty=>simp
 |insert i T g ih=>
    rw [prod_insert g, Derivation.leibniz, ih,sum_insert g,erase_insert g]; change P i*(∑ i∈T,_)+_ * _=_; rw [add_comm,mul_comm _ (derivative B (P i)),mul_sum]; -- tune
    congr 1; apply sum_congr rfl; intro j h; rw [erase_insert_of_ne (show i ≠ j from fun u=>g (u.symm ▸ h)), prod_insert (notMem_mono (erase_subset ..) g)]; ring
lemma hymn(Z:sailZ A B)(U:ΣA→ΣA→Finset ΣA→ PowerSeries B)(h:∀ X:ΣA,derivative B (Z X)=∑ Y:ΣA, ∑ F∈ drum X Y (O∩X.val), U X Y F):
 derivative B (hGas O Z)=∑ Y:ΣA, ∑ G∈ stream O,U (glueV Y (grab Y G)) Y (grab Y G)*∏ j∈farR Y G,Z j:=by
 let u (F:ΣG)(X Y:ΣA):=(∑ T∈drum X Y (O∩X.val), U X Y T)*∏ j∈F.erase X,Z j
 have ht(F:ΣG):derivative B (∏ j∈F,Z j)=∑ Y:ΣA,∑ X∈F,u F X Y:=by rw [ladZ,sum_comm]; exact sum_congr rfl (fun i _=> by rw [h,sum_mul])
 unfold hGas; rw [map_sum]; change ∑ G∈stream O, _= _; simp_rw [ht]; rw [sum_comm]; apply sum_congr rfl; intro y _; exact yul y O (fun X P=>U X y P) (fun F=>∏ j∈F,Z j)
end
end YM.CF.Cadre

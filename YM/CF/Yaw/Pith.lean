import YM.CF.Scion.Vice
import YM.CF.Scion.Xeno
import YM.CF.Hake.Sea
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Yaw
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E]{z:E}{k:ℕ}
structure PetalP (ι:Type) where
 slots: Type
 bindP: Fintype slots
 roll : slots→ List ι
 led : slots→ℝ
attribute [instance] PetalP.bindP
namespace PetalP
variable {ι I n:Type}[LinearOrder n][Fintype n]{X Y:E→FC n}(U:PetalP ι)(F:ι→FC n)
abbrev Cane (X: PetalP ι)(i:X.slots):FC n:= rollC F (X.roll i)
structure Meant(z:E)(k:ℕ)(U:PetalP ι)(F:ι→ FC n)(X:E→ FC n):Prop where
 post:∃ c:U.slots→ E→ℂ,(∀ i,Pence k (c i) z (U.led i)) ∧ ∀ᶠ i in 𝓝 z, X i=∑ j:U.slots,c j i • Cane F U j -- order?
variable {U F} {V:PetalP ι}
lemma Meant.germ(h:Meant z k U F X)(p:X=ᶠ[𝓝 z] Y):Meant z k U F Y:=by obtain ⟨c,v,p'⟩:=h.post; exact ⟨_,v,p.symm.trans p'⟩ -- missing bracket
variable (ι)
abbrev bud : PetalP ι := ⟨Unit,inferInstance,fun _=>[],fun _=>1⟩
lemma singletonK (F:ι→FC n)(z:E): Meant z k (bud ι) F 1:=by refine ⟨fun _ (_:E)=>1,fun i=>?_, Eventually.of_forall fun i=> ?_⟩; simpa using Pence.const (k:=k) z (1:ℂ); simp [bud,Cane,rollC]
variable {ι} (U V)
abbrev tw : PetalP ι:= ⟨U.slots × V.slots,inferInstance,fun i=> U.roll i.1 ++ V.roll i.2,fun i=> U.led i.1* V.led i.2⟩
variable{U V}
lemma Meant.join_k (h: Meant z k U F X)(p:Meant z k V F Y): Meant z k (U.tw V) F (X*Y):=by
 obtain ⟨c,u,w⟩:=h.post; obtain ⟨d,v,l⟩:=p.post; refine ⟨fun (i:U.slots× V.slots)=> c i.1*d i.2,fun i=> (u i.1).twice (v i.2),?_⟩; filter_upwards [w,l] with a w l; rw [Pi.mul_apply,w,l,sum_mul]; change _= ∑ i:U.slots × V.slots,_; rw [Fintype.sum_prod_type]; refine sum_congr rfl fun i _=>?_ ; rw [mul_sum]; refine sum_congr rfl fun j _=>?_ ; simp [tw,Cane,rollC,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,mul_comm] -- tune
variable [Fintype I]
abbrev bouquet (X:I→ PetalP ι):PetalP ι:= ⟨Σ i:I,(X i).slots,inferInstance,fun i=> (X i.fst).roll i.snd,fun i=> (X i.fst).led i.snd⟩
lemma Meant.rose_l (K:I→PetalP ι)(X:I→E→FC n)(f:∀ i,Meant z k (K i) F (X i)):Meant z k (bouquet K) F (∑ i:I,X i):=by
 choose c p t using fun i=> (f i).post; refine ⟨fun i=> c i.fst i.snd, fun i=>p i.fst i.snd, ?_⟩; filter_upwards [eventually_all.mpr t] with y j; rw [Finset.sum_apply]; change _=∑ i:(Σ i:I,(K i).slots),_; rw [Fintype.sum_sigma]; exact sum_congr rfl fun i _=> j i
abbrev Ribbon (U:List I)(K:I→ PetalP ι):PetalP ι:= U.foldr (fun i u=>tw (K i) u) (bud _)
lemma parallel(U:List I)(K:I→ PetalP ι)(X:I→ E→FC n)(h:∀ i∈ U,Meant z k (K i) F (X i)):Meant z k (Ribbon U K) F (U.map X).prod := by induction U with| nil=> exact singletonK ..| cons i l ih=> exact Meant.join_k (h _ (List.mem_cons_self ..)) (ih (fun j p=>h j (List.mem_cons_of_mem _ p))) -- tune
variable {A:Type*}[SemilatticeSup A][Fintype A][DecidableEq A][OrderBot A]
lemma ray_p (W X:Track A ℝ)(z:ℝ) : crank (z • W) X=z • crank W X:=by
 funext i; apply proves; intro j v; have he(q:Track A ℝ):view j (z • q)= z*view j q:=by simp only [view,mul_sum,Pi.smul_apply,smul_eq_mul]
 rw [view_crank,he,he,view_crank,mul_assoc] -- indentation
lemma tiny_p (U: List ι)(F:ι→ Track A ℝ)(Y:List ι):payH F (U++Y)= crank (payH F U) (payH F Y):=by induction U with| nil=> exact (crank_L _).symm| cons i l ih=> rw [List.cons_append]; change crank (F i) (payH F (l++Y))=crank (crank _ _) _; rw [ih, crank_A]
lemma ray_s (X:I→ Track A ℝ)(Y:Track A ℝ):crank (∑ i,X i) Y= ∑ i,crank (X i) Y:=by funext j; apply proves; intro i v; have he (X:I→Track A ℝ):view i (∑ j,X j)=∑ j,view i (X j):=map_sum (vAdd i) X _; rw [view_crank,he,sum_mul,he]; simp_rw [view_crank]
def share (X: PetalP ι)(V:ι→ Track A ℝ):Track A ℝ:=∑ i:X.slots,X.led i • payH V (X.roll i)
lemma branch_r (W V:PetalP ι)(X:ι→Track A ℝ): (tw W V).share X=crank (W.share X) (V.share X):=by unfold share; change ∑ i:W.slots × V.slots,_=_; rw [ray_s, Fintype.sum_prod_type]; refine sum_congr rfl fun i _=>?_ ; rw [crank_C,ray_s]; refine sum_congr rfl fun j _=> ?_ ; unfold tw; dsimp only; rw [tiny_p, ray_p,crank_C (W.led i • payH X (W.roll i)) (payH X (V.roll j)),ray_p,smul_smul,mul_comm] -- tune ray_p
lemma flower_l (W:I→PetalP ι)(X:ι→Track A ℝ):share (bouquet W) X=∑ i, share (W i) X:=Fintype.sum_sigma ..
lemma rib_l (W:I→ PetalP ι)(U:List I)(F:ι→ Track A ℝ):share (Ribbon U W) F=payH (fun i=>share (W i) F) U:=by induction U with| nil=> unfold share; simp [bud,Ribbon]| cons i l ih=> exact (branch_r (W i) (Ribbon l W) F).trans (congrArg (crank (share _ _)) ih)
end PetalP
end YM.CF.Yaw

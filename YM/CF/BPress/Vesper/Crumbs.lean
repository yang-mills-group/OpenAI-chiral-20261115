import YM.CF.BPress.Vesper.Porch
import YM.CF.Pastry.Bliss
/-! Crumb and common scalar transforms. Use words in FiniteGaugeData order even within-type. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Vesper
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Push.AbsoluteSums Gas Palmer Fock Pastry Pine Pf Leaves EdgeD
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]
variable {J B : Type}[LinearOrder J][Fintype J][Nonempty J][Fintype B][DecidableEq B]
namespace DoughBag
abbrev weft (z:ℂ)(A:Dough I): Dough I:= hollow z*A
lemma weft_u (z:ℂ)(A:Dough I): (weft z A).val=z • A.val:=by change ((z • _) * A.val)=_; rw [Algebra.smul_mul_assoc,one_mul]
lemma weft_κ: Continuous (fun v: ℂ × Dough I=> weft v.1 v.2):=by refine Continuous.subtype_mk (f:=fun v: ℂ×Dough I=> ((hollow v.1):Dough I).val * v.2.val) ((Continuous.smul continuous_fst continuous_const).mul (continuous_subtype_val.comp continuous_snd)) _ -- tune x drop
lemma wee_one : hollow (n:=I) 1=1:=Subtype.ext (one_smul ℂ (1:FC I))
lemma wee_void(z:Dough I): weft 1 z=z:=by rw [weft,wee_one,one_mul]
lemma wee_zero : hollow (n:=I) 0=0:=Subtype.ext (zero_smul ℂ (1:FC I))
lemma wee_mul (x y:ℂ): hollow (n:=I) (x*y)=hollow x*hollow y:=by
 apply Subtype.ext; change (x*y) • (1:FC I)=(x • 1)*(y • 1); rw [Algebra.smul_mul_assoc,one_mul,mul_smul]
def hollowHom (I:Type)[LinearOrder I][Fintype I][Nonempty I] : ℂ→+* Dough I where
 toFun:=hollow
 map_one':=wee_one
 map_mul':=wee_mul
 map_zero':=wee_zero
 map_add' x y:=Subtype.ext (add_smul x y (1:FC I))
lemma hollow_prod (g:B→ℂ)(p:Finset B): hollow (n:=I) (∏ i∈p,g i) = ∏ i∈p,hollow (g i):= map_prod (hollowHom I) ..
lemma hollow_sum (g:B→ℂ)(p:Finset B): hollow (n:=I) (∑ i∈p,g i)= ∑ i∈p,hollow (g i):= map_sum (hollowHom I) ..
lemma hollow_exp(z:ℂ): hollow (n:=I) (Complex.exp z)= exp (hollow z):=by
 letI : NormedAlgebra ℚ (Dough I):= NormedAlgebra.restrictScalars ℚ ℝ (Dough I); rw [Complex.exp_eq_exp_ℂ]; apply map_exp (hollowHom I) (Continuous.subtype_mk (continuous_id.smul continuous_const) _)
lemma weft_r(A:Dough I)(x:ℝ): weft (x:ℂ) A=x • A:=by apply Subtype.ext; rw [weft_u]; exact Complex.coe_smul ..
lemma cTask(L:Poly I J)(z:ℂ)(A:Dough I): L.cook (weft z A)=z • L.cook A:=by rw [weft,map_mul,cookH,Algebra.smul_mul_assoc,one_mul]
abbrev Leaf (X:Finset I):= ↥(Wheat X)
abbrev Dry (X:Finset I):= ↥((Wheat X).erase ∅)
lemma nilBit(X:Finset I): ∅∈ Wheat X:=by simp [Wheat]
abbrev letter (x:Finset I):=x.sort (·≤·) -- FiniteGaugeData coefficient recurrence
lemma le_leaf{X S:Finset I}(c:S∈ Wheat X): Even (letter S).length:= by simpa only [letter,length_sort] using (mem_filter.mp c|>.2)
lemma nodupB (s:Finset I):(letter s).Nodup:= sort_nodup _ _ -- tune binder
abbrev Kink(X:Finset I)(A:Dough I)(i:Leaf X):= batch (crumb A.val i.val) (letter i.val) (le_leaf i.property)
lemma timber {Z:Finset I} (A:Dough I) (p:Flour Z A.val): A=∑ i:Leaf Z, Kink Z A i:=by
 apply Subtype.ext; rw [← Subalgebra.val_apply (x:=(∑ i:Leaf Z,_)), sumS]; -- tune
 exact p.pin.trans (sum_attach ..).symm
abbrev nook{X:Finset I} (i:Dry X):Leaf X:=⟨i.val,mem_of_mem_erase i.property⟩
abbrev C₀(X:Finset I):Leaf X:=⟨∅,nilBit X⟩
lemma wind {X:Finset I}(q:Dough I)(p:Flour X q.val): q=hollow (crumb q.val ∅) + ∑ i: Dry X,Kink X q (nook i) := by
 have e:C₀ X∈ (univ:Finset (Leaf X)):=mem_univ _; let f:= Kink X q; let t:= C₀ X; nth_rw 1 [timber q p, ← Finset.add_sum_erase _ _ e]; change _= _
 apply congrArg₂ (·+·); · apply Subtype.ext; have hr:letter t.val=[]:=sort_empty _; change (crumb q.val t.val) • raw (letter t.val)=crumb q.val t.val • 1; rw [hr]; rfl
 symm; apply sum_bij (fun i _=> nook i) (fun i _=> mem_erase.mpr ⟨fun g=> ne_of_mem_erase i.property (congrArg Subtype.val g), mem_univ _⟩) (fun i _ j _ g=>Subtype.ext (show _ from (show (nook i).val=(nook j).val from congrArg Subtype.val g))); swap; · intros; rfl
 intro i v; refine ⟨⟨i.val, mem_erase.mpr ⟨fun p=> ne_of_mem_erase v (Subtype.ext p), i.property⟩⟩, mem_univ _,rfl⟩ -- tune eta
lemma tone {X: Finset I}(A:Dough I)(s:Dry X): Kink X A (nook s)*Kink X A (nook s)=0:=by
 apply Subtype.ext; change (_ • poke s.val)*(_ • poke s.val)=0; rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, Poly.tag_mul]; rw [if_neg (fun u=> ?_), smul_zero,smul_zero]; exact ne_of_mem_erase s.property (disjoint_self.mp u) -- tune
lemma pulse(T:Dough I)(p:T*T=0): exp T=1+T:=by
 letI : NormedAlgebra ℚ (FC I):=NormedAlgebra.restrictScalars ℚ ℂ _; letI : NormedAlgebra ℚ (Dough I):=NormedAlgebra.restrictScalars ℚ ℝ _; apply Subtype.ext; change Subalgebra.val (Dough I) (exp T)=1+T.val; exact (map_exp (Subalgebra.val (Dough I)) continuous_subtype_val T).trans (tideExp _ (congrArg Subtype.val p))
end DoughBag
end YM.CF.BPress.Vesper

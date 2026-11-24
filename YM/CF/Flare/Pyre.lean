import YM.CF.Flare.Coda
set_option autoImplicit false
noncomputable section
namespace YM.CF.Flare
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
section
variable {E F:Type*}[NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℂ E][NormedSpace ℂ F]{f g:ℝ→E}{v u:ℕ}
def Flo (v:ℕ)(f:ℝ→E):Prop:= ∃ F:ℕ→E,∀ t:ℝ,f t=∑ i∈range (v+1),(t:ℂ)^i • F i
lemma Flo.up (h:Flo v f)(p:v≤u):Flo u f:=by
 obtain ⟨F,h⟩:=h; let G(i:ℕ):= if i∈range (v+1) then F i else 0; refine ⟨G,fun t=>?_⟩; rw [h,← Finset.sum_subset (show range (v+1) ⊆ range (u+1) from range_mono (by omega)) (f:=fun i => (t:ℂ)^i • G i)]; exact sum_congr rfl fun i h=>by unfold G; rw [if_pos h]
 intro i _ h; simp only [G,if_neg h,smul_zero]
lemma Flo.grain (x:E): Flo v (fun _=> x) :=by apply Flo.up (v:=0) _ (Nat.zero_le _); exact ⟨fun _=>x,by simp⟩
lemma Flo.lin (h:Flo v f)(A:E →L[ℂ] F):Flo v fun x=> A (f x):=by obtain ⟨F,h⟩:=h; exact ⟨fun i=> A (F i),fun t=>by change A (f t)=_; rw [h,map_sum]; simp_rw [map_smul]⟩
lemma Flo.act (h:Flo v f)(a:ℂ):Flo v fun x=> a • f x:= h.lin (a • ContinuousLinearMap.id ℂ E)
lemma Flo.add (h:Flo v f)(p:Flo v g):Flo v fun x=> f x+g x:=by obtain ⟨A,h⟩:=h; obtain ⟨B,p⟩:=p; exact ⟨A+B,fun i=>by simp only [Pi.add_apply,smul_add,sum_add_distrib,h,p]⟩
lemma Flo.inch (h:Flo v f):Flo (v+1) fun x=> (x:ℂ) • f x:=by
 obtain ⟨G,g⟩:=h; let A(n:ℕ):= if n=0 then (0:E) else G (n-1); refine ⟨A,fun x=>?_⟩
 change (x:ℂ) • f x=_; rw [g,Finset.smul_sum, sum_range_succ' (fun i => (x:ℂ)^i • A i),pow_zero,one_smul, show A 0=0 from if_pos rfl,add_zero]; apply sum_congr rfl; intro i h; rw [pow_succ', smul_smul]; simp [A]
lemma Flo.view[CompleteSpace E](h:Flo v f)(p:v<u)(x:ℝ):f x= ∑ i∈range u,(bead u x i:ℂ) • f i:=by
 obtain ⟨A,H⟩:=h; simp_rw [H,Finset.smul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i h; have he:= line_g u i (Nat.lt_of_lt_of_le (mem_range.mp h) p) x (u:=1) (A i); simpa using he.symm
end
section
variable {n:Type*}[LinearOrder n][Fintype n]
lemma stands (S T:Finset n)(A B:Op n)(p:∀ i∉T,acts B (basisKet i)=0): Flo (S∩T).card fun x=> Fock.wedge (A+(x:ℂ) • B) S:=by
 induction S using Finset.induction_on with
 | empty=> simp_rw [wedge_empty]; exact Flo.grain _
 | @insert i S e ih=>
    let L(x:ℝ):=Fock.wedge (A+(x:ℂ) • B) S; have ht(k):acts (A+(k:ℂ) • B) (basisKet i)=acts A (basisKet i)+ (k:ℂ) • acts B (basisKet i):=by rw [act_add,act_smul]; -- tune
    simp_rw [wedge_any _ _ _ e, ht]; by_cases h:i∈T
    · simp only [map_add,map_smul,act_add,act_smul]; rw [show insert i S∩T=insert i (S∩T) from (by ext; simp; grind),card_insert_of_notMem (by intro l; exact e (mem_inter.mp l).1)]
      exact ((Flo.add ((ih.lin _).up (Nat.le_add_right _ _)) ((ih.lin _).inch)).act _)
    simp_rw [p i h,smul_zero,add_zero]; rw [show insert i S∩T=S∩T from (by ext; simp; grind)]; exact (ih.lin _).act _ -- inspect p
lemma frost(A B:Op n)(S: Finset n)(u:ℕ)(p: S.card<u)(h:∀ i∉S,acts B (basisKet i)=0)(x:ℝ) (V: UNI n): quant (twist V (A+(x:ℂ) • B))=∑ i∈range u, (bead u x i:ℂ) • quant (twist V (A+(i:ℂ) • B)):=by
 have he: quant (A+(x:ℂ) • B)=∑ i∈range u,(bead u x i:ℂ) • quant (A+(i:ℂ) • B):=by
    apply op_columns; intro j; rw [quant_column]; simp only [acts,map_sum,map_smul,ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]; -- tune
    have hx:= (stands j S A B h).view (show (j∩S).card<u from Nat.lt_of_le_of_lt (card_le_card inter_subset_right) p) x; convert hx using 1; apply sum_congr rfl; intro i h; push_cast; rw [show Matrix.toEuclideanCLM (n:=Finset n) (𝕜:=ℂ) _ (_) = _ from quant_column ..]
 simp only [quant_twist,he,map_sum]; apply sum_congr rfl; intro i _; rw [twist_formula,twist_formula,Matrix.mul_smul,Matrix.smul_mul]
end
variable {N:Side}{b:Candle}
def visitQ (T:Finset (Stag N)):= ((T ×ˢ (univ:Finset SpinIdx)).map (budE N).symm.toEmbedding : Finset (Single N))
lemma emply(T:Finset (Stag N)){i:Single N}(p:i∉visitQ T): acts (arch (shake T)) (basisKet i)=0:=by
 apply PiLp.ext; intro j; change (acts _ _).ofLp j= _; rw [basis_act, arch_at]; split_ifs with h; swap; · rfl
 rw [shake,if_neg]; rfl; intro v; apply p; apply Finset.mem_map.mpr; exact ⟨budE N i,mem_product.mpr ⟨show (i.1.1,i.2)∈T from (congrArg₂ Prod.mk h.1 h.2) ▸ v,mem_univ _⟩,(budE N).symm_apply_apply _⟩
lemma redeem(T:Finset (Stag N))(w:ℕ)(g:T.card*4<w)(s:ℝ): ∑ i∈range w,(bead w (-1) i:ℂ) • quant (Dofu N (openW T ((i+1:ℝ)*s)))=1:=by
 let B:=s • arch (shake T); let F:ℝ→Op (Single N):=fun i=>1+B+(i:ℂ) • B; have hv x: F x=arch (openW T ((x+1)*s)):=by unfold F B openW; rw [arch_a,arch_one,on_a,show (x:ℂ) • (s • arch (shake T))=x • (s • arch (shake T)) from (by ext; simp [Complex.real_smul]),smul_smul]; rw [add_mul,one_mul,add_smul]; abel
 have he:(visitQ T).card<w:=by simpa [visitQ,SpinIdx] using g
 have ht:= frost (1+B) B (visitQ T) w he (fun i p=> by unfold B; rw [ show s • arch (shake T)=(s:ℂ) • arch (shake T) from (by ext; simp [Complex.real_smul]),act_smul,emply T p,smul_zero]) (-1) (colU N)
 rw [← show quant (twist (colU N) (F (-1)))=1 from ?_]; swap; · rw [hv]; simp [openW,arch_one,quant_one]
 rw [show F (-1)=_ from rfl]; change _=quant (twist _ (1+B+((-1:ℝ):ℂ) • B)); rw [ht]; exact sum_congr rfl fun i _=>by rw [← Complex.ofReal_natCast i,show (1+B+((i:ℝ):ℂ) • B)= _ from hv i]; rfl
end YM.CF.Flare

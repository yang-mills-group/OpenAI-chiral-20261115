import YM.CF.BProof.Prox.Route

/-! Matrix currency with a Lip option. Supports implicit comparing visits on a prescribed
Domain X, including comparing parameters only at common values when indicated. Radius-zero
implies equal value on comparable points; this handles also ordinary local pricing (flags use
discrete distances). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Prox
open Function Filter Finset MeasureTheory
open scoped Topology BigOperators Classical
variable {A I K L X E 𝕜:Type*}
structure Atmos (A X: Type*) where
 compare : X→X→Prop
 read : Finset A → X→X→ℝ
 nonneg (x:Finset A)(u v:X): 0≤ read x u v
 mono {x y:Finset A}{u v:X}: x⊆ y→ read x u v≤read y u v
namespace Atmos
variable (A) (X)
/-- ordinary version. (At the same site/tags, enough to use agreement.) -/
def discrete (S:Scope X A): Atmos A X where
 compare _ _:= True
 read x a b:= if S.upon x a b then 0 else 1
 nonneg x u v:=by split<;>norm_num
 mono h:=by split<;>rename_i e<;>split<;>rename_i v <;> first | exact False.elim (e (S.mono h v))| norm_num
end Atmos
section
variable [MeasurableSpace X]
section Rent
variable (O:Atmos A X)[NormedAddCommGroup E] [MeasurableSpace E]
/-- sup-plus-seminorm payment. Use a fixed dist parameter in O. -/
def Rent (S:Finset A)(u:X→E)(p:ℝ) := Measurable u ∧ ∃ a b:ℝ,0≤a∧0≤ b ∧ a+b≤p ∧ (∀ i,‖u i‖≤a)∧∀ i j,O.compare i j→ ‖u i-u j‖≤b*O.read S i j
end Rent
variable {O:Atmos A X}
namespace Rent
variable {p q:ℝ} {S T:Finset A}
section
variable [NormedAddCommGroup E][MeasurableSpace E]{u v:X→E}
lemma meas (H:Rent O S u p): Measurable u:=H.1
lemma price (H: Rent O S u p) : 0≤ p:= by obtain ⟨a,b,h,v,k,-⟩:=H.2; exact le_trans (by positivity) k
lemma exact_bound (H: Rent O S u p)(i:X): ‖u i‖ ≤ p:=by obtain ⟨a,b,h,v,k,e,-⟩:=H.2; exact (e i).trans ((le_add_of_nonneg_right v).trans k)
lemma bound_diff (H:Rent O S u p){i j:X}(h:O.compare i j): ‖u i-u j‖≤p*O.read S i j:=by obtain ⟨a,b,v,k,u,-,p⟩:= H.2; exact (p i j h).trans (mul_le_mul_of_nonneg_right ((le_add_of_nonneg_left v).trans u) (O.nonneg ..))
lemma le (H:Rent O S u p)(h:p≤q): Rent O S u q:= by obtain ⟨a,b,h',v,k,r,d⟩:=H.2; exact ⟨H.1,a,b,h',v,k.trans h,r,d⟩
lemma go (H:Rent O S u p)(h:S⊆T): Rent O T u p:= by obtain ⟨a,b,h',v,k,r,d⟩:=H.2; exact ⟨H.1,a,b,h',v,k,r,fun i j p=> (d i j p).trans (mul_le_mul_of_nonneg_left (O.mono h) v)⟩
lemma unit (x:E): Rent O S (fun _=>x) ‖x‖:=⟨measurable_const,‖x‖,0,norm_nonneg _,le_rfl,by simp,fun _=> le_rfl,fun i j _=>by simp⟩
lemma zero : Rent O S (0:X→E) 0:=by change Rent _ _ (fun _: X=>(0:E)) _; simpa using (unit (X:=X) (S:=S) (O:=O) (0:E))
end
section
variable [NormedAddCommGroup E][MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]{u v:X→E}
lemma add (H:Rent O S u p)(G:Rent O S v q): Rent O S (u+v) (p+q):=by
 obtain ⟨a,b,h,k,e,r,d⟩:=H.2; obtain ⟨x,y,l,m,j,w,s⟩:=G.2; refine ⟨H.meas.add G.meas,a+x,b+y,by positivity,by positivity,by linarith,fun i=> (norm_add_le ..).trans (add_le_add (r i) (w i)),fun i t q=>?_⟩; rw [Pi.add_apply,Pi.add_apply,add_sub_add_comm]; exact (norm_add_le ..).trans ((add_le_add (d i t q) (s i t q)).trans_eq (add_mul ..).symm)
lemma sum {ι:Type*}(D:Finset ι){u:ι→ X→E}{p:ι→ℝ} (H:∀ i∈D,Rent O S (u i) (p i)): Rent O S (∑ i∈D,u i) (∑ i∈D,p i):=by
 induction D using Finset.induction_on with | empty=> rw [sum_empty,sum_empty]; exact zero| @insert i d h ih=> rw [sum_insert h,sum_insert h]; exact (H i (mem_insert_self ..)).add (ih (fun i h=>H _ (mem_insert_of_mem h)))
lemma neg (H:Rent O S u p): Rent O S (-u) p:=by obtain ⟨a,b,h,k,e,r,d⟩:=H.2; exact ⟨H.meas.neg,a,b,h,k,e,(by simpa using r),fun i j p=> by change ‖-u i-(-u j)‖≤_; rw [show -u i-(-u j)= -(u i-u j) from by abel,norm_neg]; exact d i j p⟩ -- tune
lemma sub (H:Rent O S u p)(G:Rent O S v q): Rent O S (u-v) (p+q):= by rw [sub_eq_add_neg]; exact H.add G.neg
lemma series [CompleteSpace E]{f:ℕ→ X→E}{P:ℕ→ℝ}(H:∀ i,Rent O S (f i) (P i))(g:Summable P) : Rent O S (fun x=>∑' i, f i x) (∑' i,P i):=by
 choose a b h v k r p using fun i=>(H i).2; have he:Summable a:= g.of_nonneg_of_le h (fun i=> (le_add_of_nonneg_right (v i)).trans (k i)); have hz:Summable b:= g.of_nonneg_of_le v (fun i=> (le_add_of_nonneg_left (h i)).trans (k i)); have hu(x:X):Summable (fun i=>‖f i x‖):= he.of_nonneg_of_le (fun i=> norm_nonneg _) (fun i=> r i x); refine ⟨Measurable.tsum (fun i=> (H i).meas),∑' i,a i,∑' i,b i, tsum_nonneg h,tsum_nonneg v,(?_),fun x=>(norm_tsum_le_tsum_norm (hu x)).trans ((hu x).tsum_le_tsum (fun i=> r i x) he),fun i j e=>?_⟩
 · rw [← Summable.tsum_add he hz]; exact (he.add hz).tsum_le_tsum k g
 have hh(t:ℕ): ‖f t i-f t j‖≤ b t*O.read S i j:=p t i j e; have g1:=hz.mul_right (O.read S i j); have hb:=g1.of_nonneg_of_le (fun t=> norm_nonneg _) hh; rw [←Summable.tsum_sub (hu i).of_norm (hu j).of_norm]; exact (norm_tsum_le_tsum_norm hb).trans ((hb.tsum_le_tsum hh g1).trans_eq (tsum_mul_right)) -- tune
lemma smul [NormedSpace ℝ E](H:Rent O S u p)(a:ℝ): Rent O S (a • u) (‖a‖*p):=by
 obtain ⟨x,y,l,m,j,w,h⟩:= H.2; refine ⟨measurable_const.smul H.meas,‖a‖*x,‖a‖*y,by positivity,by positivity,?_,fun i=> (norm_smul ..).trans_le (by gcongr; exact w i),fun i t u=>?_⟩; rw [← mul_add]; gcongr; simp only [Pi.smul_apply,← smul_sub,norm_smul, mul_assoc]; gcongr; exact h i t u -- tune
end
section
variable [NormedRing E][MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]{u v:X→E}
lemma mul (H:Rent O S u p)(G:Rent O S v q): Rent O S (u*v) (p*q):=by
 obtain ⟨a,b,h,k,e,r,d⟩:=H.2; obtain ⟨x,y,l,m,j,w,s⟩:=G.2; refine ⟨H.meas.mul G.meas,a*x,b*x+a*y,by positivity,by positivity,?_,fun i=> (norm_mul_le ..).trans (mul_le_mul (r i) (w i) (norm_nonneg _) h),fun i t q=>?_⟩
 · apply le_trans (b:=(a+b)*(x+y)) (by nlinarith); gcongr; linarith
 simp only [Pi.mul_apply]; rw [show u i*v i-u t*v t=(u i-u t)*v i+u t*(v i-v t) by noncomm_ring]; apply (norm_add_le ..).trans; apply (add_le_add (norm_mul_le ..) (norm_mul_le ..)).trans; exact (add_le_add (mul_le_mul (d _ _ q) (w i) (norm_nonneg _) (by have := O.nonneg S i t; positivity)) (mul_le_mul (r t) (s _ _ q) (norm_nonneg _) h)).trans_eq (by ring)
end
end Rent
end
end YM.CF.BProof.Prox

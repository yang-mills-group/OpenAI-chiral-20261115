import Gingham.Ruff.Placket
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Branch Drapes Filter
attribute [local instance] opCStarAlgebra

variable {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]
variable {b : Stage Y I D G} {s t u : Tag b} {A B C : Raw D I} {L : License D}

def primaries (p:ℕ)(a:ℝ) :ℝ:=∑' i:ℕ, ((i:ℝ)+1)^p* Real.exp (-a*i)
lemma primaries_P (p:ℕ)(a:ℝ) :0 ≤ primaries p a:= tsum_nonneg fun _=>by positivity
lemma primaries_b (p:ℕ){a:ℝ}(h:0<a) (S:Finset ℕ): ∑ i∈S, ((i:ℝ)+1)^p* Real.exp (-a*i) ≤ primaries p a :=by
 have hp:Summable (fun i:ℕ=> ((i:ℝ)+1)^p* Real.exp (-a*i)):=by
   have z: Summable (fun i:ℕ=> (i:ℝ)^p* Real.exp (-a*i)):=
     Real.summable_pow_mul_exp_neg_nat_mul p h
   apply (((summable_nat_add_iff 1).mpr z).mul_right (Real.exp a)).congr
   intro i; rw [mul_assoc,←Real.exp_add]; push_cast; ring_nf
 exact hp.sum_le_tsum _ (fun i _=>by positivity)

/-- Any finite map to ℕ with frequencies bounded by the capacity polynomial. -/
lemma fly {ι:Type*}[Fintype ι](l:ι→ℕ){a r:ℝ}(ha:0<a)(v:0≤r)(p e:ℕ)
 (f:∀ k:ℕ, ((univ.filter fun i=>l i=k).card:ℝ)≤ r*((k:ℝ)+1)^p):
 ∑ i, ((l i:ℝ)+1)^e* Real.exp (-a*(l i:ℝ)) ≤ r*primaries (p+e) a:=by
 classical

 apply le_trans _ (mul_le_mul_of_nonneg_left (primaries_b (p+e) ha (univ.image l)) v)
 rw [←sum_fiberwise_of_maps_to (t:=univ.image l) (g:=l) (fun _ h=>mem_image_of_mem l h),mul_sum]
 apply sum_le_sum; intro k _
 let t := univ.filter (fun i=>l i=k)
 calc
   _ = ∑ i∈t, ((k:ℝ)+1)^e* Real.exp (-a*k):=by apply sum_congr rfl; intro j h; rw [(mem_filter.mp h).2]
   _ = (t.card:ℝ)*_:=by rw [sum_const,nsmul_eq_mul]
   _ ≤ (r*((k:ℝ)+1)^p)*(((k:ℝ)+1)^e*Real.exp (-a*k)):=mul_le_mul_of_nonneg_right (f k) (by positivity)
   _ = _:=by rw [pow_add]; ring

def savings (a:ℝ)(c:Seal Y→Toll I):ℝ:= ∑ i:I, ∑ j:I, saleM a c i j
def faerie (F:Branch.Field Y)(x:Y)(A B:ℕ) (S:Seal Y): Prop:= ∀ y∈S,F.span x y ≤ A+B*S.card



variable {c :Seal Y→Toll I}
lemma float {x:Y}{M P:ℕ}{a n k q d:ℝ}(hn:Capacity b n)(v:0≤n)(L:Ledger a c q)
 (h:∀ S i j,0≤c S i j)
 (R:∀ S i j,c S i j≠0→b.home i∈S ∧ faerie b.F x M P S)
 (y:0<d)(z:k+d*P≤a):
 savings k c ≤ q * (Real.exp (d*M)) * (n*primaries 4 d) := by
 let l(i:I):=b.F.span x (b.home i)
 have F:∀ j:ℕ, ((univ.filter fun i=>l i=j).card:ℝ)≤ n*((j:ℝ)+1)^4:=by
   intro j; apply le_trans _ (hn.place x j)
   gcongr; exact fun i t=> mem_filter.mpr ⟨mem_univ _,(bay_mem _).mpr (mem_filter.mp t).2.le⟩
 have Ψ:= fly l y v 4 0 F; simp only [add_zero,pow_zero,one_mul] at Ψ
 apply le_trans _ (mul_le_mul_of_nonneg_left Ψ (mul_nonneg L.posP (Real.exp_pos _).le))
 rw [mul_sum]; apply sum_le_sum; intro i _
 rw [mul_assoc,←Real.exp_add]
 apply le_trans _ (mul_le_mul_of_nonneg_right (L.rows i) (Real.exp_pos _).le)
 rw [sum_mul]; apply sum_le_sum; intro j _
 unfold saleM; rw [sum_mul]; apply sum_le_sum; intro S _
 by_cases u:c S i j=0
 · simp [u]
 rw [mul_right_comm (rent a S)]
 apply mul_le_mul_of_nonneg_right _ (h S i j)
 rw [rent,rent, ←Real.exp_add]
 apply Real.exp_monotone
 obtain ⟨p,r⟩:=R S i j u
 have hv:(l i:ℝ)≤ (M:ℝ)+(P:ℝ)*(S.card:ℝ):=by exact_mod_cast r _ p
 nlinarith only [mul_le_mul_of_nonneg_left hv y.le,mul_le_mul_of_nonneg_right z (Nat.cast_nonneg S.card)]


structure Shells (R:Seal Y→Prop)(L:License D)(s t:Tag b)(a r:ℝ)(A:Raw D I) where
 mark : Seal Y→Raw D I
 cost : Seal Y→Toll I
 pass(S): Suite L s t S (cost S) (mark S)
 sum (x): A x = ∑ S,mark S x
 good(S i j): cost S i j≠0→R S
 paid: savings a cost ≤ r

lemma Brooch.cashed {x:Y}{M P:ℕ}{a n k q d:ℝ}
 (hn:Capacity b n)(v:0≤n)(p:Brooch (faerie b.F x M P) L s t a q A)
 (y:0<d)(z:k+d*P≤a):
 Nonempty (Shells (faerie b.F x M P) L s t k (q * (Real.exp (d*M)) * (n*primaries 4 d)) A) :=by
 obtain ⟨w,c,p,f,g,h⟩:=p
 exact ⟨w,c,p,g,h,float hn v f (fun S=>(p S).nonn)
    (fun S i j v=>⟨((p S).expo i j).triggered v|>.2.1,h S i j v⟩) y z⟩

namespace Shells
variable {R:Seal Y→Prop} {a r:ℝ}(X:Shells R L s t a r A)
-- arbitrary truncation predicate, on full domain.
open scoped Classical
def clipped (gate:Seal Y→Prop):Raw D I:=
  fun z=>∑ S,if gate S then X.mark S z else 0

lemma savings_nonneg (c:Seal Y→Toll I)(h:∀ S i j,0≤c S i j) (a:ℝ):0≤savings a c:=
 Finset.sum_nonneg fun i _=>Finset.sum_nonneg fun j _=>sale_nn h a i j
lemma split_t(gate:Seal Y→Prop)(z:D):
 A z=X.clipped gate z+X.clipped (fun S=>¬gate S) z:=by
 rw [X.sum,clipped,clipped,←Finset.sum_add_distrib]
 refine Finset.sum_congr rfl fun S _=>?_
 by_cases h:gate S<;>simp [h]
def discount {u v:ℝ}(gate:Seal Y→Prop)
    (h:∀ S,R S→ gate S→ rent u S≤ v*rent a S)(hn:0≤v):
 Shells (fun S=>R S ∧ gate S) L s t u (v*r) (X.clipped gate) :=by
  let N(S:Seal Y):=if gate S then X.mark S else (fun _=>0)
  let c(S:Seal Y):=if gate S then X.cost S else 0
  refine ⟨N,c,fun S=>?_,fun z=>?_, fun S i j=>?_,?_⟩
  · by_cases g:gate S
    · simpa only [N,c,if_pos g] using X.pass S
    simpa only [N,c,if_neg g] using (Suite.free S (L:=L) (s:=s) (t:=t))
  · unfold clipped; simp [N,ite_apply]
  · intro w; by_cases p:gate S
    · exact ⟨X.good S i j (by simpa only [c,p,if_true] using w), p⟩
    simp [c,p] at w

  apply le_trans _ (mul_le_mul_of_nonneg_left X.paid hn)
  simp_rw [savings,saleM,mul_sum]
  refine sum_le_sum fun i _=>sum_le_sum fun j _=>sum_le_sum fun S _=>?_
  have hx:= (X.pass S).nonn i j
  rw [←mul_assoc]
  by_cases e:gate S
  · simp only [c,if_pos e]
    by_cases t:X.cost S i j=0
    · rw [t];simp
    exact mul_le_mul_of_nonneg_right (h S (X.good S i j t) e) hx
  simpa only [c,if_neg e,Pi.zero_apply,mul_zero] using (mul_nonneg (mul_nonneg hn (rent_pos a S).le) hx)

def light (m:ℕ): Raw D I:= X.clipped (fun S=>S.card≤m)
def flight(m:ℕ): Raw D I:= X.clipped (fun S=>m<S.card)

lemma split_m (m:ℕ)(z:D): A z=X.light m z+X.flight m z:=by
 rw [X.split_t (fun S=>S.card≤m) z]
 simp only [light,flight,not_le]

def lightP (m:ℕ):
 Shells (fun S=>R S ∧ S.card≤m) L s t a (1*r) (X.light m) :=
 X.discount (fun S=>_) (fun S _ _=>by simp) zero_le_one

def flightP (m:ℕ){u:ℝ}(h:u≤a):
 Shells (fun S=>R S ∧ m<S.card) L s t u (Real.exp (-(a-u)*(m:ℝ))*r) (X.flight m) :=
 X.discount _ (fun S _ e=>by
   unfold rent;rw [←Real.exp_add]
   apply Real.exp_monotone
   have ht:(m:ℝ)≤S.card:=by exact_mod_cast e.le
   nlinarith only [mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr h)]) (Real.exp_pos _).le
#print axioms flightP


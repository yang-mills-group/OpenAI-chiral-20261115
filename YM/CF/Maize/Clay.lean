import YM.CF.Maize.Peak
set_option synthInstance.maxSize 30000
set_option autoImplicit false
noncomputable section
namespace YM.CF.Maize
open Function Fock Filter Metric NormedSpace Finset Pastry Petal Branch Jet Gas
open scoped Topology Classical BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n E:Type}[LinearOrder n][Fintype n][NormedAddCommGroup E][NormedSpace ℝ E]{k:ℕ}{b H C r:ℝ}(p:0≤H){F A S:E→Op n}{V D W:n→n→ℝ}{x:E}
def needle(u v:LeanV n):ℂ→ₗ[ℝ] ribbon n where
 toFun A:=⟨A • (put u*put v),(Flour.putPut univ (mem_univ _) (mem_univ _)).smul _⟩
 map_add' x y:=Subtype.ext (add_smul ..)
 map_smul' x y:=Subtype.ext (smul_assoc ..)
def spool (u v:LeanV n)(H:ℝ):ℂ→L[ℝ] ribbon n:= LinearMap.toContinuousLinearMap ((Gas.dilF H).toLinearMap.comp (needle u v))
include p
lemma spool_n(u v:LeanV n):∀ w,‖spool u v H w‖ ≤ H^2*‖w‖:=by
 intro w
 apply (price_d _ p (needle u v w)).trans; change tier H (_ • _ : FC (LeanV n))≤ H^2*‖w‖; rw [whiteℂ,mul_comm (H^2),pow_two]; exact mul_le_mul_of_nonneg_left (white_two H p) (norm_nonneg _)
omit p
abbrev loamP(b a:Bool)(F:Op n): ribbon n := ⟨faceD b a F,face_flour ..⟩
lemma sweep(x:E)(U:E→Op n)(b a:Bool): dilF H (loamP b a (U x))=∑ i,∑ j, spool (b,i) (a,j) H (U x i j):=by
 have hp: loamP b a (U x)= ∑ i,∑ j,needle (n:=n) (b,i) (a,j) (U x i j):=by
    apply Subtype.ext; change faceD b a (U x)=(ribbon n).val (∑ i,∑ j, needle (n:=n) _ _ _); rw [map_sum]; simp_rw [map_sum]; rfl
 rw [hp,map_sum]; simp_rw [map_sum]; rfl
include p
omit p in
lemma Tlin {T:Type}[NormedAddCommGroup T][NormedSpace ℝ T]{v:E→ℂ}{c a:ℝ}(h:Allows k v x a)(L:ℂ→L[ℝ] T)(p:0 ≤ c)(t:∀ i,‖L i‖≤c*‖i‖): Allows k (fun x=>L (v x)) x (c*a):= Allows.linear L h (ContinuousLinearMap.opNorm_le_bound _ p t)
lemma stance(a b:Bool)(i j:n)(h:Allows k (fun x=> F x i j) x C): Allows k (fun z=> spool (a,i) (b,j) H (F z i j)) x (H^2*C) := Tlin h _ (sq_nonneg H) (spool_n p (a,i) (b,j))
lemma primeK(b a:Bool){F:E→Op n}{V:n→n→ℝ}(h:∀ i j,Allows k (fun x=>F x i j) x (C*V i j)): Allows k (fun x=>dilF H (loamP b a (F x))) x (H^2*C*ledgerV V):=by
 simp_rw [sweep]; unfold ledgerV; simp_rw [Finset.mul_sum,mul_assoc (H^2)]; refine allows_sum (f:=fun i x=>∑ j,spool (n:=n) (b,i) (a,j) H (F x i j)) (fun i _=> ?_); exact allows_sum (f:=fun j x=> spool (b,i) (a,j) H (F x i j)) (fun j (_:j∈(univ:Finset n))=> stance p b a i j (h i j)) -- tune
lemma perk_a (h:∀ i j, Allows k (fun x=> F x i j) x (C*V i j))(t:∀ i j, Allows k (fun x=>A x i j) x (C*D i j))(v:∀ i j, Allows k (fun x=>S x i j) x (C*W i j)): Allows k (fun x=>dilF H (hang (F x) (A x) (S x))) x (C*(Linen.coins V D W*H^2)):=by
 have he(z:E): hang (F z) (A z) (S z)=(1/2:ℝ) • (loamP false false (F z)+loamP false true (A z)+(-1:ℝ) • loamP true false (A z)ᵀ +loamP true true (S z)):=by
    apply Subtype.ext; simp only [neg_one_smul]; change quilt _ _ _=(1/2:ℝ) • (faceD false false _+faceD false true _ + -faceD true false _+faceD true true _); unfold quilt; rw [sub_eq_add_neg]; ext; simp [Complex.real_smul]; ring
 simp_rw [he,map_smul,map_add,map_smul]; have ht:= primeK p true false (F:=fun x=> (A x)ᵀ) (V:=Function.swap D) (fun i j=>t j i); rw [show ledgerV (Function.swap D)=ledgerV D from sum_comm] at ht
 have hp:= ((((primeK p false false h).add (primeK p false true t)).add (ht.smul (-1))).add (primeK p true true v)); apply (hp.smul (1/2:ℝ)).mono
 apply le_trans (mul_le_of_le_one_left hp.nonneg (by norm_num)) (le_of_eq ?_); norm_num [Linen.coins]; ring
-- Hollow for scalar
noncomputable def bark(n:Type)[LinearOrder n][Fintype n](H:ℝ):ℂ→L[ℝ]Dough n:= by
 let V:ℂ→ₗ[ℝ] Dough n:={ toFun:=fun i=> hollow i,map_add':=fun i j=>Subtype.ext (add_smul ..),map_smul':=fun i j=>Subtype.ext (smul_assoc ..) }
 exact LinearMap.toContinuousLinearMap ((dilF H).toLinearMap.comp V)
lemma mintB(n:Type)[LinearOrder n][Fintype n]:∀ x,‖bark n H x‖≤1*‖x‖:=by
 intro x; rw [one_mul]; change ‖dilF H _‖ ≤ _; exact (price_d H p (hollow (n:=n) x)).trans_eq (hollow_cost ..)
end YM.CF.Maize

import YM.CF.Vault.Brag
import YM.CF.Dial.Beet
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vault
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip Scroll
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]
variable {S W V M:Op n}[Nonempty n]
open Branch
lemma wind_invA(b:Bool)(X:Op n)(p:IsUnit X):windX b X⁻¹=(windX b X)⁻¹:=by symm; apply Matrix.inv_eq_right_inv; rw [←win_m,(live p).1,win_i]
lemma wingUnit (b:Bool)(X:Op n)(p:IsUnit X): IsUnit (windX b X):=live_of (show windX b X*windX b X⁻¹=1 by rw [←win_m,(live p).1,win_i])
lemma wbody(b:Bool)(A B:Op n):windX b (body A B)=body (windX b A) (windX b B):=by cases b; rfl; simp [windX,body]
lemma wstag(b:Bool)(A B:Op n):windX b (stage A B)=stage (windX b A) (windX b B):=by unfold stage; simp only [win_a,wbody,win_l,win_i]
lemma wrel (b:Bool)(P A B:Op n)(p:IsUnit (stage P A)):windX b (relay P A B)= relay (windX b P) (windX b A) (windX b B):=by unfold relay; simp only [win_a,win_l,win_m,wbody,win_i,wind_invA b _ p, wstag]
lemma wspark (b:Bool)(P A B:Op n)(g:IsUnit (stage P A))(t:‖relay P A B-1‖<1)(U:UNI n): spark (sings b U P) (congrC U (windX b A)) (congrC U (windX b B))= cSignX b (spark P A B):=by
 let X:=relay P A B-1; have ht:‖windX b X‖= ‖X‖:=by cases b; rfl; exact norm_cc _
 have he: relay (windX b P) (windX b A) (windX b B)-1=windX b X:=by rw [←wrel b _ _ B g]; unfold X; rw [win_l,win_i]
 have hg: ‖windX b X‖<1:=ht.trans_lt t
 rw [singT,spark_turn (by rw [←wstag]; exact wingUnit b _ g) (he.symm ▸ hg)]
 unfold spark; rw [he,tally_log hg,tally_log (A:=X) t]
 have hx:sings b (1:UNI n) (pencil X)=pencil (windX b X):=by
    have hi(k): windX b (X^k)=(windX b X)^k:=by induction k with | zero=> simp [win_i] | succ i ih=> rw [pow_succ,pow_succ, win_m,ih]
    let A:ℝ:=‖X‖; have hm:Summable (fun i:ℕ=> bcoef i • X^(i+1)):=by
       apply Summable.of_norm; apply ((summable_geometric_of_lt_one (norm_nonneg _) (show A<1 from t)).mul_right A).of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=>?_)
       rw [norm_smul]; apply le_trans (mul_le_mul (bc_norm i) (norm_pow_le ..) (norm_nonneg _) zero_le_one); rw [one_mul,pow_succ]
    unfold pencil; rw [sings_sumts _ _ _ hm]; apply tsum_congr; intro i; rw [singT,one_des,win_r,hi]
 rw [←hx,singT,trace_twist,win_trace]; cases b<;> simp [cSignX]
lemma priceCC(b:Bool)(P:Op n)(U:UNI n)(F:ℝ→ Op n)(k:ℕ)(h:Stay P F k): rockZ (fun i=> congrC U (windX b (F i))) (sings b U P) k k=cSignX b (rockZ F P k k):=by
 simp only [rockZ]; rw [show ∀ f:ℕ→ℂ,cSignX b (∑ i∈range k,f i)=∑ i∈ range k,cSignX b (f i) from (by intro f; cases b<;>simp [cSignX,star_sum])]; refine sum_congr rfl fun i w=>?_ ; let V:= mem_range.mp w; apply wspark
 · exact (h i V (berth k i) ⟨le_rfl,ber_m k (by omega : i ≤ i+1)⟩).2.1
 exact (h i V _ ⟨ber_m k (by omega : i ≤ i+1),le_rfl⟩).2.2
lemma wtrans(b:Bool)(A:Op n): windX b Aᵀ=(windX b A)ᵀ:=by cases b<;>rfl
lemma victor_iso(b:Bool)(P A C D:Op n)(U Y:UNI n): let S:=sings b U P; let B:=U.val*windX b A*star Y.val;
 victory S (congrC Y (windX b C)) (congrC U (windX b D)) B=congrC U (windX b (victory P C D A)):=by
 intro S B; rw [victory,victory,win_a,wbody]; rw [show 1-S= twist U (windX b (1-P)) by unfold S; rw [win_l,win_i,map_sub,map_one,singT],board_twist,win_m,win_m,wtrans]; unfold congrC; rw [mul_add,add_mul]; congr 1
 let W:=windX b A; let Z:=windX b C; unfold B; rw [Matrix.transpose_mul,Matrix.transpose_mul]; change (U.val*W*star Y.val)*(Y.val*Z*Y.valᵀ)*((star Y.val)ᵀ * _)=_ -- tune assoc
 simp only [←mul_assoc]; rw [mul_assoc _ (star Y.val), Y.property.1,mul_one, mul_assoc _ Y.valᵀ,←Matrix.transpose_mul,Y.property.1,Matrix.transpose_one,mul_one]
lemma path_iso (b:Bool)(P A C D:Op n)(U Y:UNI n): let S:= sings b U P; let B:=U.val*windX b A*star Y.val;
 straightC S (congrC Y (windX b C)) (congrC U (windX b D)) B= fun i=>congrC U (windX b (straightC P C D A i)):=by
 intro S B; funext i; rw [straightC,straightC,show victory S _ _ B=_ from victor_iso b P A C D U Y]
 unfold congrC; simp only [win_a,win_c,mul_add,add_mul,Matrix.smul_mul,Matrix.mul_smul]; have hx(b:Bool)(i:ℝ): cSignX b i=i∧cSignX b (1-i)=1-(i:ℂ):=by cases b <;>simp [cSignX] -- casting issue
 rw [(hx b i).1,(hx b i).2]
lemma relayC (b:Bool)(P A C D:Op n)(U Y:UNI n)(k:ℕ)(h:Stay P (straightC P C D A) k): let S:=sings b U P; let B:=U.val*windX b A*star Y.val;
 rockZ (straightC S (congrC Y (windX b C)) (congrC U (windX b D)) B) S k k=cSignX b (rockZ (straightC P C D A) P k k):=by intro S B; rw [show straightC _ _ _ _=_ from path_iso b P A C D U Y]; exact priceCC b P U _ _ h
end YM.CF.Vault

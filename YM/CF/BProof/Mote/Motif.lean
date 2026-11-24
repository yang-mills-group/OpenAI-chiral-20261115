import YM.CF.BProof.Mote.Sun
set_option linter.unusedSimpArgs false
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir.BasisRim
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame Rush Scroll
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
namespace Sheet
variable {f g:noteD}(L:Side)(j:ℕ)
lemma birth (x y:Site L)(a b:SpinIdx) : Sheet (fun p=>(trident L p * sprig j L p) (x,a) (y,b)):=by
 by_cases q:y=0∧a=b
 · let c:= (((L.val:ℂ)^2)⁻¹)*((Real.sqrt L.val)⁻¹:ℝ); let r:= (modeT (lift x)*muff j L); obtain ⟨rfl,rfl⟩:= q
   convert (sings_h L ((Sheet.mode (lift x)).times (main L j))).scale c using 1; ext1 p; unfold harmony trident sprig; rw [Matrix.mul_apply]; simp only [St,Fintype.sum_prod_type,Matrix.smul_apply,c_app,ite_true,aliasBlock]; change ∑ i:Site L,∑ k:SpinIdx,_=c * ∑ i:Site L, _; rw [mul_sum]; refine sum_congr rfl fun i _=>?_; rw [Finset.sum_eq_single a]; simp only [Fintype.sum_prod_type,St,Matrix.smul_apply,c_app,ite_true,aliasBlock,Matrix.of_apply,smul_eq_mul, Matrix.one_apply_eq,money,mul_one,Pi.mul_apply,modeT]; unfold c; ring
   intro k _ h; simp [Matrix.one_apply, Ne.symm h]
   simp
 rw [show (fun p=>(trident L p*sprig j L p) (x,a) (y,b))=0 from ?_]; exact Sheet.zero
 funext p; rw [Matrix.mul_apply]; refine sum_eq_zero fun ⟨i,k⟩ _=>?_ ; unfold trident sprig; simp only [c_app, Matrix.smul_apply, Matrix.one_apply,aliasBlock,Matrix.of_apply]; split_ifs <;> first | grind | simp -- tune
lemma bri(x y:St L):∃ f:noteD, Sheet f∧∀ p,p∈baseCube→(brix j L p x y)=f p:=by
 obtain ⟨a,b⟩:=x; obtain ⟨c,d⟩:=y; exact ⟨_, (birth L j a c b d).plus (cash (((1-peb L):Stk L) (a,b) (c,d))), fun p t=> (congrArg (fun i:Stk L=>i (a,b) (c,d)) (brix_scale j L t.1))⟩
lemma harmon (k:Cover→₀ℂ)(p:Momentum):Summable (fun i=> Laurent.mode p i *k i):= summable_of_hasFiniteSupport ((k.hasFiniteSupport).subset (support_mul_subset_right ..))
lemma coeff (p:Sheet f):∃ g:Cover→₀ℂ,f=Laurent.read g:=by
 induction p with
 | mode x=> refine ⟨Finsupp.single x 1,?_⟩; funext p; unfold Laurent.read; simp [Finsupp.single_apply,eq_comm]
 | zero=> exact ⟨0, funext fun p=> (by simp only [Laurent.read,Finsupp.coe_zero,Pi.zero_apply,smul_zero,tsum_zero])⟩
 | @plus f g a b i j=> obtain ⟨k,rfl⟩:=i; obtain ⟨l,rfl⟩:=j; refine ⟨k+l,funext fun z=>?_⟩; simp only [Laurent.read,Pi.add_apply,Finsupp.coe_add,Pi.add_apply,mul_add,smul_eq_mul];  rw [(harmon k z).tsum_add (harmon l z)]
 | @scale f _ c i=> obtain ⟨l,rfl⟩:=i; refine ⟨c • l, funext fun z=>?_⟩; simp only [Laurent.read,Pi.smul_apply, Finsupp.coe_smul,smul_eq_mul]; simp_rw [mul_left_comm _ c]; rw [tsum_mul_left] -- tune
lemma sound (h:Odd L.val):∃ S:Finset Cover, ∀ x∉S, tub (brix j L) x=0:=by
 let f:=brix j L; have he(x y:St L):∃ g:Cover→₀ℂ,∀ p∈baseCube, Laurent.read g p= f p x y:=by obtain ⟨v,h,t⟩:=bri L j x y; obtain ⟨g,rfl⟩:= coeff h; exact ⟨g,fun p v=>(t p v).symm⟩
 choose V t using he; let K(x:Cover):Stk L:=Matrix.of fun i j=> V i j x
 have hp: Reads K f:= ⟨fun i j=> (show Summable (fun x:Cover=> ‖V i j x‖) from summable_of_hasFiniteSupport ?_),fun p h i j=>t i j p h⟩; case refine_1=> exact ((V i j).hasFiniteSupport).subset (fun x p q=> p (by dsimp only; rw [q]; exact norm_zero)) -- implicit support details
 let Q:= univ.biUnion (fun i: St L=> univ.biUnion (fun j:St L=> (V i j).support)); refine ⟨Q,fun x g=>?_⟩
 rw [Reads_u _ _ _ (cBrix j L h) hp]; ext i j -- function rewrite
 by_contra p; exact g (Finset.mem_biUnion.mpr ⟨i, mem_univ _,Finset.mem_biUnion.mpr ⟨j,mem_univ _,Finsupp.mem_support_iff.mpr p⟩⟩)
end Sheet
end YM.CF.Fir.BasisRim

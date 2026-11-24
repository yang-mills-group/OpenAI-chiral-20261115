import YM.CF.BPress.Weave.Stretch
/-! Purchases uniform in every S argument and period. row spine R powers. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Weave
open Function Filter Lattice Wilson RG Precision Grid Cube Bands Tunnel Pressure Wealth Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s: Side}{B:BandWidth}(X : Bands s B)
abbrev Fare := Finset X.Hcols→ BEnd X
lemma basis_row (A : BEnd X) : rowM X A= LinearMap.toMatrix (EuclideanSpace.basisFun (Axon X) ℝ).toBasis (EuclideanSpace.basisFun (Axon X) ℝ).toBasis A.toLinearMap:=by
 ext i j; simp [rowM,LinearMap.toMatrix_apply,q_ray, EuclideanSpace.inner_single_left, OrthonormalBasis.coe_toBasis_repr_apply]
lemma entry1 (A: BEnd X)(v:RaySpace X)(i: Axon X): (A v) i=∑ j,rowM X A i j*v j:=by
 let b:= EuclideanSpace.basisFun (Axon X) ℝ; conv_lhs=> rw [← b.sum_repr v]
 rw [map_sum]; change _ = _; rw [← EuclideanSpace.basisFun_inner _ _ _ i, inner_sum]; unfold b; apply sum_congr rfl; intro j _; simp [map_smul, rowM,q_ray,EuclideanSpace.inner_single_left,mul_comm]
lemma entry_cap (A:BEnd X)(i j : Axon X): |rowM X A i j| ≤ ‖A‖:= by
 calc
  _ ≤ ‖q_ray X i‖* (‖A‖*‖q_ray X j‖):= (abs_real_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _))
  _ = _ := by simp [q_ray]
lemma row_sm (A: BEnd X)(c:ℝ): rowM X (c • A)=c • rowM X A:=by rw [basis_row,basis_row]; exact map_smul ..
lemma row_a (A C:BEnd X): rowM X (A+C)=rowM X A+rowM X C:=by rw [basis_row,basis_row,basis_row]; exact map_add ..
lemma row_z : rowM X 0=0:=by rw [basis_row]; exact map_zero ..
lemma row_1 : rowM X 1=1:=by rw [basis_row,ContinuousLinearMap.toLinearMap_one]; exact LinearMap.toMatrix_one ..
lemma row_P (A C:BEnd X): rowM X (A*C)=rowM X A*rowM X C:=by rw [basis_row,basis_row,basis_row]; apply LinearMap.toMatrix_mul -- tune
lemma column_mono (x:X.Hcols){r t:ℕ}(p:r≤t) : columnBall X x r ⊆ columnBall X x t:=fun _ h=>column_eq.mpr ⟨(column_eq.mp h).1, (column_eq.mp h).2.trans p⟩
structure Connect (F:Fare X)(r:ℕ) : Prop where
 reaches (S): Wealth.reaches X (F S) r
 sees : houseRead X F r
namespace Connect
variable {X}{F G: Fare X}{r t:ℕ}
lemma mono (h:Connect X F r)(v:r≤t): Connect X F t:=⟨fun S i j p=> h.reaches S i j fun e=> p (column_mono X _ v e),fun S T i e=> h.sees S T i fun y p=>e y (column_mono X _ v p)⟩
lemma one : Connect X (fun _=>1) r:=⟨fun _ i j p=>by have h:i≠j:=fun h=> p (h ▸ column_self ..); rw [row_1]; simp [h], fun _ _ _ _ _=>rfl⟩
lemma zero : Connect X (fun _=>0) r:=⟨fun _ i _ _=>by rw [row_z]; rfl,fun _ _ _ _ _=>rfl⟩
lemma keep : Connect X (keeper X) r:=by
 have he (S:Finset X.Hcols) (i j:Axon X) : rowM X (keeper X S) i j= if i=j ∧ zSite X i ∈ S then 1 else 0:=by
   change inner ℝ _ (keepOnly X S _) =_; rw [q_at]; by_cases h:i=j
   · subst j; split <;> simp_all [q_ray]
   simp only [h,false_and,if_false]; split <;> simp [h,q_ray,EuclideanSpace.inner_single_left] -- tune
 refine ⟨fun S i j p=> ?_,fun S T i p j=>?_⟩; rw [he]; exact if_neg (fun (y:i=j∧zSite X i∈ S)=> p (y.1 ▸ column_self ..)); simp only [he,p _ (column_self ..)]
lemma plus (h:Connect X F r)(k:Connect X G r): Connect X (fun S=>F S+G S) r:=⟨fun S i j u=>by rw [row_a, Matrix.add_apply,h.reaches S i j u,k.reaches S i j u,add_zero],fun S T i h' j=>by rw [row_a,row_a, Matrix.add_apply,Matrix.add_apply, h.sees S T i h' j,k.sees S T i h' j]⟩
lemma scale (h: Connect X F r)(c:ℝ): Connect X (fun S=> c • F S) r:=⟨fun S i j u=>by rw [row_sm,Matrix.smul_apply,h.reaches S i j u,smul_zero],fun S T i h' j=>by rw [row_sm,row_sm, Matrix.smul_apply,Matrix.smul_apply,h.sees S T i h' j]⟩
lemma sub (h:Connect X F r)(k:Connect X G r): Connect X (fun S=>F S-G S) r:=by simpa [sub_eq_add_neg,show ∀ x:BEnd X, (-1:ℝ) • x= -x from fun x=> neg_one_smul ℝ x] using h.plus (k.scale (-1))
lemma walk (h:Connect X F r)(g:Connect X G t): Connect X (fun S=>F S * G S) (r+t):=by
 refine ⟨fun S i j u=>?_,fun S T i e j=>?_ ⟩
 · rw [row_P, Matrix.mul_apply]; apply sum_eq_zero; intro k _; by_cases h': zSite X k∈ columnBall X (zSite X i) r; exact mul_eq_zero_of_right _ (g.reaches S k j fun p=> u (reach_add X h' p)); rw [h.reaches S i k h',zero_mul]
 rw [row_P,row_P, Matrix.mul_apply,Matrix.mul_apply]; apply sum_congr rfl; intro k _; rw [(h.mono (Nat.le_add_right r t)).sees S T i e]; by_cases p:zSite X k∈ columnBall X (zSite X i) r; rw [g.sees S T k (fun y u=>e y (reach_add X p u))]; rw [h.reaches T i k p,zero_mul,zero_mul]
lemma pow (h:Connect X F r)(i:ℕ): Connect X (fun S=> F S^i) (i*r):=by induction i with|zero=>simpa only [pow_zero] using (one (r:=0*r))| succ i ih=> simp_rw [pow_succ,Nat.add_mul,one_mul]; exact ih.walk h
lemma sumT {I:Type*}(T:Finset I)(F:I→ Fare X)(h:∀ i∈T,Connect X (F i) r): Connect X (fun S=>∑ i∈T,F i S) r:=by
 induction T using Finset.induction_on with| empty=> simpa only [sum_empty] using (zero (X:=X) (r:=r))| @insert i T t ih=> simp_rw [sum_insert t]; exact (h i (mem_insert_self i T)).plus (ih (fun j g=>h j (mem_insert_of_mem g)))
lemma stretch_at (h:Connect X F r)(p:ℝ)(n:ℕ): Connect X (fun S=>stretch X S (F S) p n) (n*r):= (Connect.scale (sumT (range (n+1)) _ (fun i e=>(Connect.scale (((Connect.pow (Connect.sub one (h.scale p⁻¹)) i)).mono (Nat.mul_le_mul_right r (Nat.lt_succ_iff.mp (mem_range.mp e)))) (SignScalar.c i)))) _).plus (keep.scale _)
end Connect
-- parcel spectral wrappers: B.D = fixed. d.direct actual funds maybe VARIABLE! audit. parameter use gap b fixed version or assumptions for d direct. check Work.Raw wrappers.
section angular
variable (p:ℝ)(n:ℕ)(M:ℕ)(R:PathData group)(d:Clip)(β y:ℝ){σ C Λ:ℝ}(H:R.Bounds d σ C Λ)
abbrev wave (S:Finset X.Hcols) : BEnd X:= hessian X M R d β y H S
def flying (S:Finset X.Hcols) : BEnd X:= stretch X S (wave X M R d β y H S) p n
lemma purchased (v:High B M) : Connect X (flying X p n M R d β y H) (n*(6*M)):= (show Connect X (wave X M R d β y H) (6*M) from ⟨fun i=>hessian_reach X M R d β y H i v,hessian_plan X M R d β y H v⟩).stretch_at p n
lemma flight (t:0<y)(u:High B M)(G:β∈ Set.Icc (y/2) (2*y))(r:ℝ)(v:r≤massL B d)(e:payUpper d M B.D C ≤ p)(f:1≤p)(g:0<r)(h:p*(2*peak r)*brink p r n≤y⁻¹^2)(S: Finset X.Hcols) : Poly X S (wave X M R d β y H S) (flying X p n M R d β y H S) (peak p) (peak r) (y⁻¹^2):= stretch_bound X S _ p r n ⟨ section_sym ..,fun w=>by unfold Flare; rw [one_smul]; exact hess_sev X M R d β y H S w u⟩ ((show Margins (wave X M R d β y H S) (massL B d) (payUpper d M B.D C) from fun w=> ⟨ mass_lower X M R d β y H S w t G u,pay_upper X M R d β y H S u t G w⟩).broad v e) f g (v.trans (min_le_left ..)) h -- tune
end angular
end YM.CF.BPress.Weave

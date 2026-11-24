import YM.CF.BProof.Extension.Frame
import YM.CF.BProof.Taylor
import YM.Gauge.Colors

/-! Uniform Lipschitz extension for SU(n). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Extension
open Function Metric Filter Set Module NormedSpace
open scoped Matrix Matrix.Norms.Frobenius Topology InnerProductSpace ContDiff ComplexConjugate NNReal ENNReal
variable {N : ℕ}
abbrev rowI (N:ℕ) := EuclideanSpace ℂ (Fin (N+1))
abbrev GM (N:ℕ) := Matrix (Fin (N+1)) (Fin (N+1)) ℂ
abbrev inSU (A : GM N) := A∈ unitary (GM N) ∧ Matrix.det A=1
noncomputable def rowC (A : GM N) (i : Fin (N+1)) : rowI N := WithLp.toLp 2 (A i)
private def rows (F : Fin (N+1)→ rowI N) : GM N:= Matrix.of fun i j=> F i j
@[simp] lemma row_rows (F : Fin (N+1)→ rowI N) : rowC (rows F)=F:=rfl
private lemma row_inject : Injective (@rowC N) := by intro u v h; exact congrArg rows h
private lemma unitsR {A : GM N} : A∈ unitary (GM N) ↔ Orthonormal ℂ (rowC A):=by
 have he (i j) : (A*star A) i j = ⟪rowC A j,rowC A i⟫_ℂ:=by rw [Matrix.mul_apply]; rfl
 rw [Matrix.mem_unitaryGroup_iff,orthonormal_iff_ite]; constructor
 · intro h i j; simp only [← he,h,Matrix.one_apply]; simp [eq_comm]
 intro h; ext i j : 1; rw [he,h j i]; simp [Matrix.one_apply,eq_comm]

def fromRows (F : Fin (N+1)→ rowI N) : GM N := rows F -- Linear
private abbrev DomainR (N:ℕ):= Fin N → rowI N
def cutRows (A: GM N) : DomainR N:= fun i=> rowC A i.succ
def cofactor (F : DomainR N) : rowI N := WithLp.toLp 2 fun i=> conj ((rows (Fin.cons 0 F)).adjugate i 0)
def finish (F : DomainR N) : GM N := fromRows (Fin.cons (cofactor F) F)

lemma finish_spec (A:GM N) (h:inSU A) : finish (cutRows A)=A := by
 have ha: A.adjugate=star A:= by
    rw [← Matrix.one_mul A.adjugate,← show star A*A=1 from h.1.1,Matrix.mul_assoc,Matrix.mul_adjugate,h.2,one_smul,Matrix.mul_one]
 unfold finish; apply row_inject
 funext i; change Fin.cons (α:=fun _ => rowI N) _ _ i=rowC A i
 refine Fin.cases ?_ (fun i=>by simp only [Fin.cons_succ,cutRows]) i
 refine PiLp.ext fun j=>?_
 change conj _ = A 0 j
 have hv(z:Fin (N+1)→ℂ) : (rows (Fin.cons 0 (cutRows A))).updateRow 0 z=A.updateRow 0 z := by
   ext k l : 1; exact Fin.cases (by simp) (fun k=>by rw [Matrix.updateRow_ne (Fin.succ_ne_zero _),Matrix.updateRow_ne (Fin.succ_ne_zero _)]; rfl) k -- tune
 rw [show (rows (Fin.cons 0 (cutRows A))).adjugate j 0=A.adjugate j 0 from by rw [Matrix.adjugate_apply,Matrix.adjugate_apply, hv],ha]; simp

private lemma completeR (F : DomainR N) (h : Orthonormal ℂ F) : inSU (finish F) := by
 let S := {x : Fin (N+1)| x≠0}; let f:Fin (N+1)→ rowI N:=Fin.cons 0 F
 have hh : Orthonormal ℂ (S.restrict f) := by
    have hX : ∀ x∈S,∃ y,x=Fin.succ y:= fun x hx=> by induction x using Fin.cases with|zero => exact (hx rfl).elim|succ y=> exact ⟨y,rfl⟩
    rw [orthonormal_iff_ite] at *; rintro ⟨x,hx⟩ ⟨y,hy⟩; obtain ⟨i,rfl⟩:= hX x hx; obtain ⟨j,rfl⟩:=hX y hy; simpa [Set.restrict,f] using h i j
 obtain ⟨b,hb⟩:= hh.exists_orthonormalBasis_extension_of_card_eq (by simp [rowI])
 let T:=rows b; have hT:T∈ unitary (GM N):= unitsR.mpr b.orthonormal
 let x(i:Fin (N+1)):= if i=0 then star T.det else 1
 let K:=Matrix.diagonal x; have he : T.det*star T.det=1:= (Matrix.det_of_mem_unitary hT).2
 have hk: K∈ unitary (GM N):= by
    apply Matrix.mem_unitaryGroup_iff.mpr; ext i j : 1; unfold K; rw [Matrix.diagonal_mul]; by_cases H:i=j
    · subst j; by_cases h:i=0 <;> simp [x,h]; exact mul_eq_one_comm.mp he
    simp [Matrix.diagonal_apply,H,Ne.symm H,Matrix.one_apply]
 let A:=K*T; have hA : inSU A := by refine ⟨(unitary _).mul_mem hk hT,?_⟩; unfold A K; simp [Matrix.det_mul,Matrix.det_diagonal,Fin.prod_univ_succ,x]; exact mul_eq_one_comm.mp he
 have hg : cutRows A=F:= by
    funext i; refine PiLp.ext fun j=>?_
    change (Matrix.diagonal x*rows b) i.succ j=F i j; rw [Matrix.diagonal_mul]; simp [rows,x,hb _ (show i.succ∈S from Fin.succ_ne_zero i),f]
 rw [← hg,finish_spec _ hA]; exact hA

private noncomputable def stampR : (Fin (N+1) → rowI N) →ₗ[ℝ] GM N where
 toFun := fromRows
 map_smul' := fun _ _=>rfl
 map_add' := fun _ _=>rfl
private noncomputable def cutR : GM N →ₗ[ℝ] DomainR N where
 toFun := cutRows
 map_smul' := fun _ _=>rfl
 map_add' := fun _ _=>rfl

lemma finish_s : ContDiff ℝ ω (@finish N) := by
 have hh : ContDiff ℝ ω (@cofactor N):= by
    apply (contDiff_piLp 2).mpr; intro i
    let x (F:DomainR N):=(rows (Fin.cons 0 F)).updateRow 0 (Pi.single i 1)
    have he(j k:Fin (N+1)):ContDiff ℝ ω (fun F:DomainR N=>x F j k):=by
       refine Fin.cases ?_ (fun j=>?_) j
       · exact contDiff_const
       change ContDiff ℝ ω fun F:DomainR N=> x F j.succ k
       simp only [x,Matrix.updateRow_ne (Fin.succ_ne_zero _),rows,Matrix.of_apply,Fin.cons_succ]; exact (contDiff_piLp_apply 2).comp (contDiff_apply ℝ _ _)
    change ContDiff ℝ ω (fun F=>conj ((rows (Fin.cons 0 F)).adjugate i 0))
    simp_rw [Matrix.adjugate_apply,Matrix.det_apply]
    apply (starL ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp -- tune
    exact ContDiff.sum fun σ _=> ContDiff.const_smul σ.sign (contDiff_prod fun j _ => he _ _)
 let P(F:DomainR N) : Fin (N+1) → rowI N := Fin.cons (cofactor F) F; change ContDiff ℝ ω (stampR.toContinuousLinearMap ∘ P)
 exact stampR.toContinuousLinearMap.contDiff.comp (contDiff_pi.mpr (fun i=>Fin.cases hh (fun i=> contDiff_apply ℝ _ _) i))

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
lemma costLinear (L:E→L[ℝ] F) : ∃ C:ℝ,0<C ∧ ∀ x, ‖L x‖ ≤ C*‖x‖:= ⟨‖L‖+1,by positivity,fun x=> (L.le_opNorm x).trans (by gcongr; simp)⟩
lemma costBall [ProperSpace E](f:E→F)(h:ContDiff ℝ ω f)(r:ℝ) : ∃ C:ℝ,0<C ∧ Lip (closedBall 0 r) C f := by
 let S:=closedBall (0:E) r; have he: IsCompact S:=isCompact_closedBall ..
 obtain ⟨C,H⟩:= he.bddAbove_image (f:=fun x:E=> ‖fderiv ℝ f x‖) ((h.continuous_fderiv (by simp)).norm.continuousOn)
 refine ⟨max C 1, one_pos.trans_le (le_max_right ..),fun x hx y hy=>?_⟩
 rw [dist_eq_norm]; exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f':= fderiv ℝ f) (fun x hx=> (h.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt) (fun x hx=> (H ⟨x,hx,rfl⟩).trans (le_max_left ..)) (convex_closedBall ..) hy hx
lemma finish_price (N:ℕ) : ∃ C:ℝ, 0<C ∧ Lip (closedBall (0:DomainR N) 1) C finish := costBall _ finish_s _

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
lemma frame_extend (N:ℕ) (B K : ℝ) (hb : 0<B)(hk:0<K) (d : Module.finrank ℝ X ≤ 3) :
    ∃ C > (0:ℝ), ∀ (S T : Set X)(F : X → GM N), S ⊆ closedBall 0 B → T ⊆ S → T.Nonempty →
    (∀ x∈T,inSU (F x)) → Lip T K F → ∃ G : X→GM N, Lip S C G ∧ (∀ x∈S,inSU (G x)) ∧ EqOn F G T := by
 let L:=cutR (N:=N) |>.toContinuousLinearMap
 obtain ⟨u,h,J⟩:= costLinear (show GM N →L[ℝ] DomainR N from L) -- defeq
 obtain ⟨C,hc,H⟩:= columns (Y:=rowI N) N B (u*K) hb (mul_pos h hk) d (by simp [rowI]); obtain ⟨v,hv,V⟩:= finish_price N
 refine ⟨v*C,mul_pos hv hc,fun S T F vS vT hT hF HF=>?_⟩
 let f:=fun x=>cutRows (F x); have ht(x:X)(hx:x∈T):Orthonormal ℂ (f x):= (unitsR.mp (hF x hx).1).comp _ (fun _ _ => Fin.succ_inj.mp)
 have hm(i:Fin N):Lip T (u*K) (fun x=> f x i):=by
    intro x hx y hy; change ‖L (F x) i-L (F y) i‖ ≤ _; apply le_trans (norm_le_pi_norm (L (F x)-L (F y)) i); rw [←map_sub,mul_assoc]; exact (J _).trans (mul_le_mul_of_nonneg_left (HF x hx y hy) h.le)
 obtain ⟨Y,he,hs,hu⟩:= H S T f vS vT hT ht hm
 have hw(x:X)(hx:x∈S):Y x∈closedBall (0:DomainR N) 1:=by rw [mem_closedBall,dist_zero_right]; exact (pi_norm_le_iff_of_nonneg one_pos.le).mpr (fun i=> (hs x hx).1 i |>.le)
 refine ⟨finish ∘ Y, fun x hx y hy=>?_,fun x hx=> completeR _ (hs x hx),fun x hx => ?_⟩
 · refine (V _ (hw x hx) _ (hw y hy)).trans ?_; rw [mul_assoc,dist_eq_norm (Y x)]; exact mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i=>hu i x hx y hy)) hv.le
 rw [Function.comp_apply,← he hx]; exact (finish_spec (F x) (hF x hx)).symm
end YM.CF.BProof.Extension

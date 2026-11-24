import YM.CF.BProof.Extension.Rail
import YM.CF.Matter.Pair

/-! Smooth extension of SU(n) or SO(n) assignments. Unitaries over **one** RCLike field. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Extension.Mar
open Function Metric Filter Set Module NormedSpace RCLike
open scoped Matrix Topology InnerProductSpace ContDiff ComplexConjugate NNReal ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] {N:ℕ}
abbrev Wing (𝕂:Type*) [RCLike 𝕂](N:ℕ) := EuclideanSpace 𝕂 (Fin (N+1))
abbrev CellK (𝕂:Type*)(N:ℕ) := Matrix (Fin (N+1)) (Fin (N+1)) 𝕂
section
variable {n:Type*}[Fintype n][DecidableEq n]
abbrev inK (A : Matrix n n 𝕂) := A ∈ unitary (Matrix n n 𝕂) ∧ A.det=1
end
noncomputable def rowC (A : CellK 𝕂 N) (i : Fin (N+1)) : Wing 𝕂 N := WithLp.toLp 2 (A i)
private def rows (F : Fin (N+1)→ Wing 𝕂 N) : CellK 𝕂 N:= Matrix.of fun i j=> F i j
@[simp] lemma row_rows (F : Fin (N+1)→ Wing 𝕂 N) : rowC (rows F)=F:=rfl
private lemma row_inject : Injective (rowC (𝕂:=𝕂) (N:=N)) := by intro u v h; exact congrArg rows h
private lemma unitsR {A : CellK 𝕂 N} : A∈ unitary (CellK 𝕂 N) ↔ Orthonormal 𝕂 (rowC A):=by
 have he (i j) : (A*star A) i j = ⟪rowC A j,rowC A i⟫_𝕂:=by rw [Matrix.mul_apply]; rfl
 rw [Matrix.mem_unitaryGroup_iff,orthonormal_iff_ite]; constructor
 · intro h i j; simp only [← he,h,Matrix.one_apply]; simp [eq_comm]
 intro h; ext i j : 1; rw [he,h j i]; simp [Matrix.one_apply,eq_comm]

def fromRows (F : Fin (N+1)→ Wing 𝕂 N) : CellK 𝕂 N := rows F -- Linear
private abbrev DomainR (𝕂:Type*)[RCLike 𝕂](N:ℕ):= Fin N → Wing 𝕂 N
def cutRows (A: CellK 𝕂 N) : DomainR 𝕂 N:= fun i=> rowC A i.succ
def cofactor (F : DomainR 𝕂 N) : Wing 𝕂 N := WithLp.toLp 2 fun i=> conj ((rows (Fin.cons 0 F)).adjugate i 0)
def finish (F : DomainR 𝕂 N) : CellK 𝕂 N := fromRows (Fin.cons (cofactor F) F)

lemma finish_spec (A:CellK 𝕂 N) (h:inK A) : finish (cutRows A)=A := by
 have ha: A.adjugate=star A:= by
    rw [← Matrix.one_mul A.adjugate,← show star A*A=1 from h.1.1,Matrix.mul_assoc,Matrix.mul_adjugate,h.2,one_smul,Matrix.mul_one]
 unfold finish; apply row_inject
 funext i; change Fin.cons (α:=fun _ => Wing 𝕂 N) _ _ i=rowC A i
 refine Fin.cases ?_ (fun i=>by simp only [Fin.cons_succ,cutRows]) i
 refine PiLp.ext fun j=>?_
 change conj _ = A 0 j
 have hv(z:Fin (N+1)→𝕂) : (rows (Fin.cons 0 (cutRows A))).updateRow 0 z=A.updateRow 0 z := by
   ext k l : 1; exact Fin.cases (by simp) (fun k=>by rw [Matrix.updateRow_ne (Fin.succ_ne_zero _),Matrix.updateRow_ne (Fin.succ_ne_zero _)]; rfl) k -- tune
 rw [show (rows (Fin.cons 0 (cutRows A))).adjugate j 0=A.adjugate j 0 from by rw [Matrix.adjugate_apply,Matrix.adjugate_apply, hv],ha]; simp

private lemma completeR (F : DomainR 𝕂 N) (h : Orthonormal 𝕂 F) : inK (finish F) := by
 let S := {x : Fin (N+1)| x≠0}; let f:Fin (N+1)→ Wing 𝕂 N:=Fin.cons 0 F
 have hh : Orthonormal 𝕂 (S.restrict f) := by
    have hX : ∀ x∈S,∃ y,x=Fin.succ y:= fun x hx=> by induction x using Fin.cases with|zero => exact (hx rfl).elim|succ y=> exact ⟨y,rfl⟩
    rw [orthonormal_iff_ite] at *; rintro ⟨x,hx⟩ ⟨y,hy⟩; obtain ⟨i,rfl⟩:= hX x hx; obtain ⟨j,rfl⟩:=hX y hy; simpa [Set.restrict,f] using h i j
 obtain ⟨b,hb⟩:= hh.exists_orthonormalBasis_extension_of_card_eq (by simp [Wing])
 let T:=rows b; have hT:T∈ unitary (CellK 𝕂 N):= unitsR.mpr b.orthonormal
 let x(i:Fin (N+1)):= if i=0 then star T.det else 1
 let K:=Matrix.diagonal x; have he : T.det*star T.det=1:= (Matrix.det_of_mem_unitary hT).2
 have hk: K∈ unitary (CellK 𝕂 N):= by
    apply Matrix.mem_unitaryGroup_iff.mpr; ext i j : 1; unfold K; rw [Matrix.diagonal_mul]; by_cases H:i=j
    · subst j; by_cases h:i=0 <;> simp [x,h]; exact mul_eq_one_comm.mp he
    simp [Matrix.diagonal_apply,H,Ne.symm H,Matrix.one_apply]
 let A:=K*T; have hA : inK A := by refine ⟨(unitary _).mul_mem hk hT,?_⟩; unfold A K; simp [Matrix.det_mul,Matrix.det_diagonal,Fin.prod_univ_succ,x]; exact mul_eq_one_comm.mp he
 have hg : cutRows A=F:= by
    funext i; refine PiLp.ext fun j=>?_
    change (Matrix.diagonal x*rows b) i.succ j=F i j; rw [Matrix.diagonal_mul]; simp [rows,x,hb _ (show i.succ∈S from Fin.succ_ne_zero i),f]
 rw [← hg,finish_spec _ hA]; exact hA

private lemma cofactorS : ContDiff ℝ ∞ (@cofactor 𝕂 _ N):= by
    apply (contDiff_piLp 2).mpr; intro i
    let x (F:DomainR 𝕂 N):=(rows (Fin.cons 0 F)).updateRow 0 (Pi.single i 1)
    have he(j k:Fin (N+1)):ContDiff ℝ ∞ (fun F:DomainR 𝕂 N=>x F j k):=by
       refine Fin.cases ?_ (fun j=>?_) j
       · exact contDiff_const
       change ContDiff ℝ ∞ fun F:DomainR 𝕂 N=> x F j.succ k
       simp only [x,Matrix.updateRow_ne (Fin.succ_ne_zero _),rows,Matrix.of_apply,Fin.cons_succ]; exact (contDiff_piLp_apply 2).comp (contDiff_apply ℝ _ _)
    change ContDiff ℝ ∞ (fun F=>conj ((rows (Fin.cons 0 F)).adjugate i 0))
    simp_rw [Matrix.adjugate_apply,Matrix.det_apply]
    apply (starL ℝ : 𝕂 ≃L[ℝ] 𝕂).contDiff.comp -- tune
    exact ContDiff.sum fun σ _=> ContDiff.const_smul σ.sign (contDiff_prod fun j _ => he _ _)
lemma realizeWing : Realize 𝕂 (Wing 𝕂 N):= fun x y=> by simp_rw [PiLp.inner_apply,map_sum]; exact Finset.sum_congr rfl fun i _=>rfl
lemma finishSmooth (i j : Fin (N+1)): ContDiff ℝ ∞ (fun F: DomainR 𝕂 N=> finish F i j):=by
 refine Fin.cases ?_ (fun k=>?_) i
 exact (contDiff_piLp_apply 2).comp cofactorS
 exact (contDiff_piLp_apply 2).comp (contDiff_apply ℝ _ _)
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
-- entrywise to allow L2/Frobenius coexistence.
abbrev SuitM {n:Type*}(S:Set X)(F:X→Matrix n n 𝕂) := ∀ i j,Suit S (fun x=>F x i j)
lemma smooth_extend (d:Module.finrank ℝ X< 2*Module.finrank ℝ 𝕂) (S T:Set X)(s:IsCompact S)(p:Convex ℝ S)(t:T⊆S) (F:X→ CellK 𝕂 N)(h:SuitM S F)(W:∀ x∈T,inK (F x)) : ∃ G:X→CellK 𝕂 N, SuitM S G ∧ EqOn F G T ∧ ∀ x∈S,inK (G x):=by
 let f(x:X):=cutRows (F x); have he :∀ i,Suit S (fun x=> f x i):=fun i x hx=> (contDiffAt_piLp 2).mpr (fun j=>h i.succ j x hx)
 obtain ⟨b,g,H,hb⟩:= ascent (𝕂:=𝕂) realizeWing S T s p t N (by simp [Wing]) d f he (fun x hx=> (unitsR.mp (W x hx).1).comp _ (fun _ _=> Fin.succ_inj.mp))
 refine ⟨finish ∘ b,fun i j x hx=> (finishSmooth i j).contDiffAt.comp x (contDiffAt_pi.mpr fun i=> g i x hx),fun x hx=>?_,fun x hx=> completeR _ (hb x hx)⟩
 rw [Function.comp_apply,←H hx]; exact (finish_spec (F x) (W x hx)).symm
end YM.CF.BProof.Extension.Mar

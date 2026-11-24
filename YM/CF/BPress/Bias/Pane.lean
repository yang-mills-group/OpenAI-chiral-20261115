import YM.CF.BPress.Bias.Ferry
/-! Y = fixed spatial momentum. Stays time-slice-local in position, all support only mode constraint. Can use full op-norm on these sectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Bias
open Function Filter NormedSpace Finset Lattice Laurent Bloch Next.Free Metric Fir Lat Spin Rush Blank Tulip Nacre SU Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {N: Side} (k:Site N)
def originM (a: Op (Site N)): Op (Single N) := scalarP (a⊗ₖ(1:Op SpinIdx))
def inflate {A:Op (Site N)}(h:A∈ unitary (Op (Site N))): UNI (Single N):= ⟨originM A, Matrix.kronecker_mem_unitary (Matrix.kronecker_mem_unitary h (unitary _).one_mem) (unitary _).one_mem⟩
variable (N)
def Full: UNI (Single N):= inflate (fourier_mem N)
def Temp: UNI (Single N):= inflate (tempUni N)
def Tang: UNI (Single N):= Full N * star (Temp N)
variable {N}
lemma tang_exp : (Tang N).val=originM (Fourier N* star (temporal N)):=by
 change originM (Fourier N)*star (originM _)=_; unfold originM scalarP; simp [op_star_kron,op_kron_mul]
lemma l_spectral(f:Momentum→ Op SpinIdx): lens f N = twist (Full N) (scalarP (mark N f)):=by unfold Blank.lens plates; rw [twist_formula,twist_formula]; unfold scalarP; simp only [Full,inflate,originM, overU,scalarP,op_star_kron,op_kron_mul,mul_one, star_one]
lemma tang_spectral (f:Momentum→ Op SpinIdx): twist (star (Tang N)) (lens f N)= twist (Temp N) (scalarP (mark N f)):=by
 rw [l_spectral,twist_formula, twist_formula,twist_formula]; let U:=Full N; let W:=Temp N; let A:=scalarP (mark N f); change star (U.val*star W.val)*(U.val*A*star U.val)* star (star (U.val*star W.val))=W.val*A*star W.val; rw [star_mul,star_star]; simp only [star_mul,star_star,mul_assoc]; rw [←mul_assoc (star U.val), U.property.1,one_mul, ←mul_assoc (star U.val), U.property.1,one_mul]

-- mask toolkit
variable {I:Type*}[Fintype I][DecidableEq I]
lemma slabL (S:Finset I)(A:Op I)(i j:I) : (cutM S*A) i j=if i∈S then A i j else 0:=by rw [cutM, Matrix.diagonal_mul]; split_ifs <;> simp
lemma slabR (S:Finset I)(A:Op I)(i j:I) : (A*cutM S) i j=if j∈S then A i j else 0:=by rw [cutM, Matrix.mul_diagonal]; split_ifs <;> simp
lemma neComm (S: Finset I)(A:Op I)(h:∀ i j,A i j≠0 → (i∈S ↔ j∈S)):Commute (cutM S) A:=by
 unfold Commute SemiconjBy; ext i j; rw [slabL,slabR]; by_cases g:A i j=0; · simp [g]
 simp [h i j g]
lemma cut_inside (S T: Finset I)(h:S⊆ T) : cutM T*cutM S=cutM S:=by ext i j; rw [slabL]; by_cases t:i ∈ T ; simp [t]; rw [if_neg t]; by_cases e:i=j; subst j; simp [cutM,mt (@h _) t]; simp [cutM,e]
lemma twist_C {A:Op I} (U:UNI I): twist U A=A ↔ Commute A U.val:=by
 rw [twist_formula]; constructor
 · intro h; unfold Commute SemiconjBy; nth_rw 1 [← h]; rw [mul_assoc _ (star U.val),U.property.1,mul_one]
 intro h; rw [←h.eq,mul_assoc,U.property.2,mul_one]

abbrev penX (i:Single N):Site N:= i.1.1
abbrev fog (o:Single N):=penX o 0
def regions:=univ.filter fun o:Single N=> mer (penX o)=mer k
def region:=cutM (regions k)
def sectorY:=twist (Full N) (region k)
def shutters (t:Finset (Per N)):Finset (Single N):=univ.filter fun i=>fog i∈ t
def shutter (t:Finset (Per N)):= cutM (shutters t)
lemma commY : twist (Temp N) (region k)=region k:=by
 rw [twist_C]; refine neComm (regions k) _ ?_; rintro ⟨⟨i,b⟩,r⟩ ⟨⟨j,d⟩,t⟩ v; have he:mer i=mer j:=by contrapose! v; simp [Temp,inflate,originM,scalarP,temporal,v]
 simp only [regions,penX,mem_filter,mem_univ,true_and,he]
lemma tangY : twist (Tang N) (region k)=sectorY k:=by
 unfold sectorY; nth_rw 1 [←commY k]; rw [twist_formula,twist_formula,twist_formula]; let U:=Full N; let W:=Temp N; change (U.val*star W.val)*(W.val*_*star W.val)*star (U.val*star W.val)=_; simp only [star_mul,star_star,mul_assoc]; rw [←mul_assoc (star W.val),W.property.1,one_mul,←mul_assoc (star W.val),W.property.1,one_mul]
lemma stays(t:Finset (Per N)): twist (Tang N) (shutter t)=shutter t:=by
 rw [twist_C]; refine neComm (shutters t) _ ?_; rintro ⟨⟨i,b⟩,r⟩ ⟨⟨j,d⟩,v⟩ u; have he:i 0=j 0:=by contrapose! u; rw [tang_exp]; simp [originM,scalarP,horiz N i j u]
 simp only [shutters,penX,fog,mem_filter,mem_univ,true_and,he]
lemma cutS {S T: Finset I}:Commute (cutM S) (cutM T):= neComm S _ fun i j h=>by rw [show i=j by contrapose! h; simp [cutM,h]]
lemma going (t:Finset (Per N)): Commute (shutter t) (sectorY k):=by nth_rw 1 [← stays t]; rw [← tangY]; exact cutS.map (twist (Tang N))
lemma comm_full(f :Site N→Op SpinIdx): Commute (region k) (scalarP (jump (Equiv.refl _) f)):=by
 refine neComm (regions k) _ ?_; rintro ⟨⟨i,b⟩,r⟩ ⟨⟨j,d⟩,t⟩ u; have he:i=j:=by contrapose! u; simp [jump_apply,scalarP,u]
 simp only [regions,penX,mem_filter,mem_univ,true_and,he]
lemma goingLens (f:Momentum → Op SpinIdx) : Commute (sectorY k) (lens f N):=by rw [l_spectral]; exact (comm_full k (f∘mel)).map (twist (Full N))
lemma sector_star : IsStarProjection (sectorY k):= (cutM_idp (regions k)).map (twist (Full N))

-- offdiagonal block between two times `u'=u+n` etc
private lemma φ_diag (n:ℕ)(b u:Per N) :φ (u+(n: Per N)) b * star (φ u b)=pinω u n* markFreq b (n:ℝ):=by
 have hp: pinω u n *pinω u n=1:= fee_one _; let a:=φ (u+(n: Per N)) b; let y:=markFreq b (n:ℝ); apply mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hp); rw [←mul_assoc,φ_step,←mul_assoc (pinω u n),hp,one_mul,mul_comm (φ u b), mul_assoc,φ_one,mul_one]
variable (f:Momentum→Op SpinIdx)
private lemma twist_site (x y:Site N)(i j:SpinIdx) : let F:=temporal N⊗ₖ(1:Op SpinIdx); (F*mark N f*star F) (x,i) (y,j)=∑ k:Site N,temporal N x k*f (mel k) i j * star (temporal N y k):=by
 intro F; have he(k:Site N)(i j): (F*mark N f) (x,i) (k,j)=temporal N x k*f (mel k) i j:=by
    simp only [Matrix.mul_apply,mark,jump_apply, Equiv.refl_apply,Fintype.sum_prod_type,F,Matrix.kroneckerMap_apply]; simp [Matrix.one_apply, ite_mul,mul_ite]
 rw [Matrix.mul_apply]; simp only [Matrix.star_apply,Fintype.sum_prod_type]; simp_rw [he]; simp [F,Matrix.one_apply,apply_ite]
lemma block (a b:SpinIdx) (i: Slot)(u:Per N)(n:ℕ): let v:=u+(n:Per N); twist (star (Tang N)) (lens f N) ((needle k v,a),i) ((needle k u,b),i) = pinω u n * Turn f k n a b:=by
 intro v; rw [tang_spectral, twist_formula]; change (scalarP (temporal N⊗ₖ(1:Op SpinIdx))*scalarP (mark N f)*star (scalarP (temporal N⊗ₖ(1:Op SpinIdx)))) _ _ = _; unfold scalarP; rw [op_kron_mul,op_star_kron,op_kron_mul, star_one,mul_one,mul_one]; simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq,mul_one]; rw [twist_site]; unfold temporal evoke; simp only [Matrix.of_apply,mer_tick,apply_ite,star_zero, ite_mul,mul_zero]; simp +contextual only [ite_true,eq_comm (a:=mer k),zero_mul]; rw [tick_sum]; unfold Turn; simp only [needle,update_self,Matrix.smul_apply, smul_eq_mul,Matrix.sum_apply, mul_sum]; apply sum_congr rfl; intro t _; set P:=φ v t; set Y:=star (φ u t); set W:=f (mel (update k 0 t)) a b; have hp:P*Y=pinω u n*markFreq t n:=φ_diag n t u; rw [star_div₀,sq_star]; change _*W*(Y/_)=_; rw [show pinω u n*((N.val:ℂ)⁻¹*(markFreq t n * W))= (pinω u n*markFreq t n)/(N.val:ℂ)*W by ring, ←hp, ← sqMore]; ring
end YM.CF.BPress.Bias

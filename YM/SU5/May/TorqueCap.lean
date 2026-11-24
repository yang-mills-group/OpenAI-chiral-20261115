import YM.SU5.May.FloeCore
/-! # true capital after funding: vector price-cap per-leg, not c² single pixels. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Advance.Whorl
open Function Fock NormedSpace SU Lat Lattice Spire Cube Finset MeasureTheory Branch Reflect Window Wilson Rush Peaks Scroll
open Phase Skye Pastry Tulip Dial Paige Push.SectorMeasure Scree Vault Fir Peaks Drapes Tap Precision Tree Next.SectorChange Stencil
open Reed (Fine think)
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical ENNReal
attribute [local instance] opCStarAlgebra
open Hygrometry Flare
variable {I:Type*}[LinearOrder I][Fintype I]
structure Worth (A S:Finset I)(P:ℝ)(x:Reader0 I) : Prop where
 limb : withinM (if x.1 then Aᶜ else A) x.2
 touches : withinM S x.2
 budget : ‖x.2‖≤P
structure Headboard (A S:Finset I)(b:Bool)(κ:ℕ)(ρ:ℝ)(C:List (Reader0 I)) : Prop where
 allKeys:∀ x∈ C,Worth A S ρ x
 size:C.length ≤ κ
 poll:wheat C=b
-- finitely priced, **ell1 of reps**, a BASIS FREE bound scales all location vectors. Then closure. pay even Favoured.
noncomputable def Capital (A S:Finset I)(b:Bool)(κ:ℕ)(ρ c:ℝ) : Set (FC I):= {u| ∃ (J: Type)(_ :Fintype J)(C:J→List (Reader0 I))(w:J→ℂ), (∀ j,Headboard A S b κ ρ (C j)) ∧ (∑ j, ‖w j‖)≤c ∧ u=∑ j,w j • rollC ton (C j)}
variable {A S T: Finset I}{b d:Bool}{κ κ':ℕ} {c c' ρ ρ':ℝ} {x:Reader0 I}{u v:FC I}
abbrev Fort (A S:Finset I)(b:Bool)(κ:ℕ)(ρ c:ℝ) : Set (FC I):= closure (Capital A S b κ ρ c)
lemma Worth.increase (h:Worth A S ρ x)(v:S ⊆ T)(w:ρ≤ρ'):Worth A T ρ' x:=by
 refine ⟨h.limb,?_,h.budget.trans w⟩; exact (within_test ..).2 fun i p=> (within_test ..).1 h.touches i (fun w'=> p (v w'))
lemma Worth.fine (h:Worth A S ρ x) : Fine A S true (ton x):=by
 rcases x with ⟨b,x⟩; cases b; exact (fine_create _ h.limb h.touches); exact (fine_remove _ h.limb h.touches)
lemma capital_le (v:S⊆T)(w:ρ≤ρ')(q:c≤c')(t:κ≤κ'): Capital A S b κ ρ c ⊆ Capital A T b κ' ρ' c' :=by rintro x ⟨J,N,C,f,g,u,rfl⟩; exact ⟨J,N,C,f,fun x=> ⟨fun i v'=> ((g x).allKeys i v').increase v w, (g x).size.trans t,(g x).poll⟩,u.trans q,rfl⟩
lemma capital_zero (p:0 ≤ c) : 0∈Capital A S b κ ρ c:= ⟨Fin 0,inferInstance, fun i=> [],fun _=>0, fun i=> i.elim0,by simpa,by simp⟩
lemma Capital.oneWord {C:List (Reader0 I)} {w:ℂ}(p:Headboard A S b κ ρ C) (h:‖w‖≤c): w • rollC ton C∈ Capital A S b κ ρ c:= ⟨Unit,inferInstance,fun _=> C,fun _=>w,fun _=>p,by simpa,by simp⟩
lemma capital_add (x:u∈ Capital A S b κ ρ c)(y:v∈Capital A S b κ ρ c') : u+v∈ Capital A S b κ ρ (c+c'):=by
 obtain ⟨J,f,W,l,L,p,rfl⟩:= x; obtain ⟨K,j,X,t,T,q,rfl⟩:=y
 refine ⟨J⊕K,inferInstance,Sum.elim W X,Sum.elim l t,Sum.rec L T,by simpa [Fintype.sum_sum_type] using add_le_add p q,by simp [Fintype.sum_sum_type]⟩
lemma capital_smul (h:u∈ Capital A S b κ ρ c)(x:ℂ): x • u∈ Capital A S b κ ρ (‖x‖*c):=by obtain ⟨J,t,C,w,H,p,rfl⟩:=h; refine ⟨J,t,C,x • w,H,by simpa [Finset.mul_sum] using mul_le_mul_of_nonneg_left p (norm_nonneg x), by simp only [Finset.smul_sum,smul_smul,Pi.smul_apply,smul_eq_mul]⟩
lemma capital_convex:Convex ℝ (Capital A S b κ ρ c):=by
 intro x hx y hy r t u v w; rw [← Complex.coe_smul,←Complex.coe_smul t]; set R:= ‖(r:ℂ)‖; set T:=‖(t:ℂ)‖
 have p:R*c+T*c=c:=by unfold R T; rw [Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg u,Real.norm_of_nonneg v,←add_mul,w,one_mul]
 exact p ▸ capital_add (capital_smul hx (↑r:ℂ)) (capital_smul hy (↑t:ℂ))
private lemma wheat_append {α:Type*}(C D:List α): wheat (C++D)=(wheat C).xor (wheat D):= by induction C with
 | nil=> exact (Bool.false_xor _).symm
 | cons x C ih=> rw [List.cons_append,wheat,ih,wheat,Bool.xor_assoc]
lemma capital_mul (x:u∈ Capital A S b κ ρ c) (y:v∈Capital A S d κ' ρ c'): u*v∈ Capital A S (b.xor d) (κ+κ') ρ (c*c'):=by
 obtain ⟨J,f,W,l,L,p,rfl⟩:= x; obtain ⟨K,j,X,t,T,q,rfl⟩:=y
 refine ⟨J×K,inferInstance,fun i=> W i.1++X i.2,fun i=> l i.1*t i.2,fun i=> ⟨?_,?_,?_⟩,?_,?_⟩
 · exact fun k u=> (List.mem_append.mp u).elim ((L i.1).allKeys k) ((T i.2).allKeys k)
 · simpa using add_le_add (L i.1).size (T i.2).size
 · rw [wheat_append,(L i.1).poll,(T i.2).poll]
 · simp_rw [Fintype.sum_prod_type,norm_mul,←Finset.mul_sum,←Finset.sum_mul]; exact mul_le_mul p q (sum_nonneg fun i _=> norm_nonneg _) ((sum_nonneg fun i _=> norm_nonneg _).trans p)
 rw [Finset.sum_mul]; simp_rw [Finset.mul_sum,Matrix.smul_mul,Matrix.mul_smul, Fintype.sum_prod_type]; simp_rw [rollC,List.map_append, List.prod_append,smul_smul]
lemma passFort {Y:Type*}[TopologicalSpace Y]{M:Set Y}(p:IsClosed M)(Z:FC I→Y)(f:Continuous Z)(v:∀ x∈Capital A S b κ ρ c,Z x∈M){x:FC I}(h:x∈Fort A S b κ ρ c): Z x∈M:= closure_minimal v (p.preimage f) h
lemma increasedF (v:S⊆T)(w:ρ≤ρ')(q:c≤c')(t:κ≤κ'): Fort A S b κ ρ c⊆ Fort A T b κ' ρ' c':= closure_mono (capital_le v w q t)
-- mul/scale/sum for forts. root needs only capital (closure inherited).
example (x:u∈ Fort A S b κ ρ c)(y:v∈ Fort A S d κ' ρ c'): u*v∈ Fort A S (b.xor d) (κ+κ') ρ (c*c'):=passFort isClosed_closure _ (continuous_id.mul (continuous_const (y:=v))) (fun a h=>passFort isClosed_closure _ ((continuous_const (y:=a)).mul continuous_id) (fun k q=>subset_closure (capital_mul h q)) y) x
#print axioms capital_convex
end YM.CF.Buffered.Advance.Whorl

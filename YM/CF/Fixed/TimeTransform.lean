import YM.CF.Fixed.SliceBands
import YM.CF.Reed.Point

/-! Heat energy decision on partial Fourier with still-varying temporal
profile. The relevant seam powers here are not switched to `Grace.C`. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Fixed.Rift
open Function NormedSpace Matrix Lattice Finset Filter Fock BZ Mir Lat Scroll SU Bulk
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}
abbrev AxisA (N:Side):= Slot → Per N → Three
def BlankN (f:AxisA N)(U:Bkg N):Prop:= (∀ i:Site N,U (i,0)=1)∧ ∀ (i:Site N)(j:Fin 3), (matter (U (i,j.succ))).val=diagonal (fun k=>phase (f k (i 0) j))
abbrev motionZ (N:Side)(i: Fin 3): Equiv.Perm (Ion N):=Equiv.prodCongr (view N i) (Equiv.refl Slot)
variable (f:AxisA N)(U:Bkg N)(g:BlankN f U)

include g
def timeZ (N:Side): Op (Stage N):=jump (plusTime N) (fun x=> trunkZ x • (1:Spin))
lemma initialT: ingot (relate N) (frame matter U (anticut N)|>.T 0)=frameZ N (fun _=> timeZ N):=by
  rw [←staticZ]; ext ⟨⟨x,c⟩,t,i⟩ ⟨⟨y,d⟩,u,j⟩; change shift matter U _ 0 (paste t x,i,c) (paste u y,j,d) = _
  unfold shift tableS timeZ; simp only [jump_apply,advance_time,paste_eq]
  unfold hop color; rw [g.1,map_one]; unfold seam trunkZ; by_cases k:x=y <;> by_cases h:c=d <;> by_cases p:t+1=u <;> simp [paste, k,p,h,Matrix.one_apply,anticut]

omit g in
lemma spin_ion(A:Spin): ingot (relate N) (spin N Slot A) = frameZ N (fun _=> diagonalS fun _=>A):=by
  rw [←staticZ]; ext ⟨⟨x,i⟩,y,s⟩ ⟨⟨z,j⟩,w,t⟩; change spin N Slot A (paste y x,s,i) (paste w z,t,j)=_; rw [Lat.spin, tableS]; simp only [jump_apply,Equiv.refl_apply,paste_eq]; by_cases e:i=j<;> by_cases h:y=w <;> by_cases f:x=z <;> simp [e,h,f,diagonalS,jump_apply]

lemma blockL(i:Fin 3): ingot (relate N) ((frame matter U (anticut N)).T i.succ)=jump (motionZ N i) (fun (x:Ion N)=> diagonalS fun y => (trunkZ (x.1 i)*phase (f x.2 y i)) • (1:Spin)):=by
  ext ⟨⟨x,a⟩,t,m⟩ ⟨⟨z,b⟩,p,n⟩; change shift matter U _ _ (paste t x,m,a) (paste p z,n,b)=_
  simp only [shift,jump_apply,advance_tri,paste_eq,Equiv.prodCongr_apply,motionZ]; unfold hop color; rw [g.2]; unfold seam trunkZ diagonalS; by_cases h:t=p <;> by_cases e:view N i x=z <;> by_cases d:a=b<;> simp [h,e,d,jump_apply,paste,anticut, mul_comm]; split_ifs<;>rfl

def freqZ (f:AxisA N)(x:Ion N)(t:Per N):Three:=zmom x.1 + f x.2 t
def snare (i:Fin 3)(x:Ion N) : Op (Stage N):= diagonalS (fun y=>phase (freqZ f x y i) • 1)
lemma tinted (i:Fin 3): ingot (relate N) ((frame matter U (anticut N)).T i.succ)=frameZ N (snare f i):=by
  rw [blockL f U g]; apply Eq.symm; apply twist_comm; apply blockEq
  rintro ⟨x,a⟩ ⟨y,b⟩; simp_rw [block_mul,tableS,block_jump];
  let S:= motionZ N i; have he(x: Tri N): (f a : _)=f a:=rfl;
  rw [sum_eq_single (y,b),sum_eq_single (S (x,a))]; -- tune order
  · simp only [Equiv.refl_apply,ite_true, S, motionZ, Equiv.prodCongr_apply, Prod.map_apply, horizontal]
    by_cases k:a=b; · subst b; rw [if_pos rfl,if_pos rfl,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,mul_one,one_mul]; unfold snare diagonalS freqZ; rw [←jump_smul,←jump_smul]; congr 1; funext t; simp only [Pi.smul_apply, Pi.add_apply, Reed.Bare.phase_ext,smul_smul]; congr 1; unfold spaceF; rw [div_mul_eq_mul_div, div_mul_eq_mul_div]; congr 1; rw [mul_comm (f_tri _ _), ← mul_assoc, mul_comm _ (trunkZ _), fh_op]; ring
    simp [k]
  all_goals first | exact fun a _ h=> by rw [if_neg (Ne.symm h),zero_mul] | exact fun p _ h=> by simp only [Equiv.refl_apply,if_neg h,mul_zero] | simp

omit g
def archT (A B:Op (Stage N)):Op (Stage N):= -(1/2:ℝ) • (B+star B)+ A*((1/2:ℝ) • (B-star B))
def headerT(N:Side): Op (Stage N):=diagonalS fun _=>grading
def headK(N:Side) (i : Axis): Op (Stage N):=diagonalS fun _=>gammaOp i
lemma realJump {i k : Type*}[DecidableEq i](f:Equiv.Perm i)(A:i→ Op k)(r:ℝ): jump f (r • A) = r • jump f A:=by ext ⟨x,p⟩ ⟨y,q⟩; by_cases h:f x=y<;>simp [jump_apply,h]
-- minus mass. spin. table maps
lemma timeLap (N:Side): headerT N * archT (headK N 0) (timeZ N) = timely N:=by
  let T:= headK N 0; let Z:= timeZ N; let F:= headerT N
  have h1: (1/2:ℝ) • ((F*T-F)*Z)=shotF N:=by
    have he:(F*T-F)=diagonalS fun _=> grading*gammaOp 0-grading:=by unfold F T headK headerT diagonalS; rw [jump_mul,Equiv.refl_trans,←jump_sub]; rfl
    rw [he]; unfold Z timeZ shotF diagonalS; rw [jump_mul,Equiv.refl_trans]; rw [← realJump]; congr 1; funext i; simp only [Pi.smul_apply,Equiv.refl_apply,Algebra.mul_smul_comm, mul_one]; rw [smul_comm]; unfold incoming; rw [opp_s, Algebra.mul_smul_comm]; simp only [mul_sub,mul_one]; congr 1; module
  have h2: (-(1/2:ℝ)) • ((F+F*T)*star Z)=star (shotF N):=by
    have he:F+F*T=diagonalS fun _=> grading+grading*gammaOp 0:=by unfold F T headK headerT diagonalS; rw [jump_mul,Equiv.refl_trans,←jump_add]; rfl
    rw [he]; unfold Z timeZ shotF diagonalS; rw [jump_star,jump_star, jump_mul,Equiv.refl_trans,← realJump]; congr 1; funext i; simp only [Pi.smul_apply, Equiv.refl_apply,star_smul,star_one,Algebra.mul_smul_comm,mul_one]; rw [smul_comm]; congr 1; rw [exit_star,plusS]; simp only [Algebra.mul_smul_comm,mul_add,mul_one]; module
  rw [timely, ←h2,←h1]; unfold archT; simp only [F,T,Z,Algebra.mul_smul_comm,mul_add,add_mul,mul_sub,sub_mul,mul_assoc]; module

lemma phaseLap (x:Ion N)(i:Fin 3): headerT N * (1 + archT (headK N i.succ) (snare f i x)) = diagonalS fun y=> varS i (freqZ f x y i):=by
  unfold headK headerT snare diagonalS archT; rw [←(jump_id (X:=Per N) (n:=SpinIdx)),jump_star,Equiv.refl_symm,←jump_sub, ←jump_add,←realJump,←realJump,jump_mul,Equiv.refl_trans,←jump_add,←jump_add,jump_mul,Equiv.refl_trans]; congr 1; funext j
  dsimp only [Pi.smul_apply, Pi.add_apply,Pi.sub_apply, Equiv.refl_apply]; let p:Mom:=Fin.cons 0 (freqZ f x j); let B:= BZ.atom p; let a:= i.succ
  have he:(B.lap a)= (1-Real.cos (freqZ f x j i)) • (1:Spin):= by rw [show freqZ f x j i=p a from (by unfold a p; simp)]; exact BZ.atom_l ..
  have hh:B.diff a=(Real.sin (freqZ f x j i)) • (Complex.I • (1:Spin)):= by rw [show freqZ f x j i=p a from (by unfold a p; simp)]; exact BZ.atom_s ..
  rw [show phase (freqZ f x j i) • (1:Spin)=B.T a from (by change _=phase (p a) • _; unfold p a; simp),neg_smul]; change grading * (1 + (- ((1/2:ℝ) • (B.T a+star (B.T a)))+gammaOp a* B.diff a))=_; rw [show (1+(- ((1/2:ℝ) • (B.T a+star (B.T a))) + gammaOp _ * B.diff a))=B.lap a+gammaOp a*B.diff a from (by change _=(1- ((1/2:ℝ) • _))+_; abel),he,hh]; unfold varS angleM; simp only [mul_add,Algebra.mul_smul_comm, mul_one]; rfl

include g
lemma income_root :ingot (relate N) (frame matter U (anticut N)|>.H)= frameZ N (fun x=>timed (freqZ f x)):=by
  let Y:= fun i:Axis=> (frame matter U (anticut N)).inc i
  let Z:=frame matter U (anticut N); let F:=frameZ N
  let A:Vega N:= fun _=>headerT N
  let K:=(ingot (relate N)); -- tune
  let V: Axis→ Vega N:=Fin.cons (fun _=> timeZ N) (snare f); let B(i:Axis):Vega N:=fun _=> headK N i
  have he (i:Axis): K (Z.T i)=F (V i) := by induction i using Fin.cases with| zero=> exact initialT f _ g| succ i=> simpa only [V, Fin.cons_succ] using tinted f U g i
  have hx:K Z.chir=F A:= spin_ion ..; have h(i:Axis): K (Z.gamma i)=F (B i):=spin_ion ..
  let L(i:Axis):Vega N:= fun k=> archT (B i k) (V i k)
  have hp(i:Axis):K (Y i)= F (1+ L i):=by
    rw [show L i= -(1/2:ℝ) • (V i+star (V i))+ B i * ((1/2:ℝ) • (V i-star (V i))) from rfl]
    simp only [map_add F,map_smul F,map_mul F,map_sub F, map_one F,show ∀ B, F (star B)=star (F B) from fun _=>frameZ_star _];
    change K (1-((1/2:ℝ) • (Z.T i + star (Z.T i))) + Z.gamma i * ((1/2:ℝ) • (Z.T i-star (Z.T i))))=_
    rw [map_add K,map_sub K,map_one K,map_mul K,map_smul K,map_smul K, map_add K, map_sub K, ingot_star, he,h,neg_smul]; abel
  change K (Z.chir*(-1+∑ i,Y i))=_; rw [map_mul K,map_add K, map_neg K, map_one K,map_sum K,hx]; simp_rw [hp]; rw [← map_sum, ← show F (-1)= -1 by rw [map_neg,map_one], ←map_add,←map_mul]; congr 1; funext x
  rw [Fin.sum_univ_succ]; simp only [Pi.mul_apply,Finset.sum_apply,Pi.add_apply,Pi.one_apply,Pi.neg_apply, A, L,V, Fin.cons_succ,Fin.cons_zero,B]; rw [←add_assoc,←add_assoc,neg_add_cancel,zero_add,mul_add,timeLap, Matrix.mul_sum]; simp_rw [phaseLap]; unfold timed phaseS; congr 1; induction (univ:Finset (Fin 3)) using Finset.induction_on with -- induction?
  | empty=> simp; ext; simp [diagonalS,jump_apply]
  | insert i T h ih=> rw [sum_insert h]; simp_rw [sum_insert h]; rw [ih]; exact (table_add (fun y=>_) _).symm

lemma energy_arrange (h:Safe (frame matter U (anticut N)).H): let A(x):= timed (freqZ f x)
    (∀ x,Safe (A x)) ∧ energy (frame matter U (anticut N)).H = ∑ x,energy (A x):=by
  intro A; have he:= income_root f U g; let F:= frame matter U (anticut N); let T:= ingot (relate N) F.H; let U':= mainF N; have ht : twist U' (tableS A) = T:=he.symm
  have hx:Safe T:=safe_reindex _ _ h; have hv:=hx.twisted (star U'); rw [←ht,twist_inv] at hv; exact ⟨fun _=>table_safe _ hv,(energy_ingot _ _ h).symm.trans (by change energy T=_; rw [←ht,energy_turn _ _ hv]; exact energy_table A hv)⟩
end YM.CF.Fixed.Rift

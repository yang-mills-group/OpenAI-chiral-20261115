import YM.CF.Jill.Pool
import YM.CF.Tulip.Metro
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kea
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}
abbrev TF:= {u:F→ℝ//∑ i,u i=0}
abbrev Candle:=Axis→TF
def pw (x:ℝ):= BZ.phase x
lemma phase_a(x y:ℝ):pw (x+y)=pw x * pw y:=by unfold pw BZ.phase; rw [Complex.ofReal_add,add_mul,Complex.exp_add]
lemma phase_z:pw 0=1:=by simp [pw,BZ.phase]
lemma phase_o(x:ℝ):pw (-x)=star (pw x):=by unfold pw BZ.phase; rw [Complex.star_def, ← Complex.exp_conj]; simp
lemma phase_c(x:Candle)(a:F): (∏ i:Axis,pw ((x i).val a))=pw (∑ i:Axis,(x i).val a):=by simp_rw [pw,BZ.phase, Complex.ofReal_sum,sum_mul,Complex.exp_sum] -- may require args
def waveG (x:TF): E :=
 let A:Op F:=Matrix.diagonal (pw ∘ x.val)
 let U:UNI F:=⟨A,by
       apply Matrix.mem_unitaryGroup_iff.mpr; have he:star A=Matrix.diagonal (fun i=>star (pw (x.val i))):=by ext i j; by_cases h:i=j <;> simp [h,Ne.symm,A]
       rw [he]; unfold A; rw [Matrix.diagonal_mul_diagonal, show (fun i=> (pw∘x.val) i * star (pw (x.val i)))=1 by funext i; exact BZ.phase_one _]; rfl⟩
 ⟨U,by change A.det=1; unfold A; rw [Matrix.det_diagonal]; simp only [Function.comp_apply,pw,BZ.phase,← Complex.exp_sum,← sum_mul, ← Complex.ofReal_sum,x.property,Complex.ofReal_zero,zero_mul,Complex.exp_zero]⟩
def tax (x:Candle) : Bkg N:= fun i=> waveG (x i.2)
lemma tax_mul(u v:TF): waveG u * waveG v=waveG ⟨u.val+v.val,(by simp [u.property,v.property,sum_add_distrib])⟩:=by
 apply Subtype.ext; apply Subtype.ext; change Matrix.diagonal _ * Matrix.diagonal _= Matrix.diagonal _; rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; exact (phase_a ..).symm
lemma tax_comm(u v:TF): waveG u*waveG v=waveG v*waveG u:=by rw [tax_mul,tax_mul]; congr 1; exact Subtype.ext (add_comm ..)
lemma tax_flat(x:Candle)(i:Site N)(a b:Axis):travel (tax x) i (square a b)=1:=by
 simp only [square,travel,Step.neg_read,Step.pos_read]; unfold tax; rw [← mul_assoc, tax_comm, mul_one]; group
lemma tax_guard (x:Candle)(N:Side)(e:ℝ)(h:0≤e):Guard (tax x:Bkg N) e:=by constructor <;> intro i j k _ <;> rw [tax_flat] <;> simpa using h
lemma wave_id(x:TF): fund (waveG x)=Matrix.diagonal (pw∘x.val):=rfl
def freqD (x:TF)(i:Slot):ℝ:= match i.2 with
|.inl v=>x.val v.val.1+x.val v.val.2
|.inr v=>-x.val v
lemma matD (x:TF):(matter (waveG x)).val=Matrix.diagonal (pw ∘ freqD x):=by
 let f:=pw ∘ x.val
 have he: cc (Matrix.diagonal f)=Matrix.diagonal (fun i=>star (f i)):=by ext i j; by_cases h:i=j <;> simp [h]
 change _ =_; rw [matter_matrix,wave_id,triple,each,ExTwo.wedge_diag,he]; ext ⟨u,i⟩ ⟨v,w⟩; by_cases h:u=v <;> cases i <;> cases w <;> simp [h, Matrix.diagonal_apply,Matrix.one_apply,Join.both,freqD,phase_a,phase_o,f]
def pulse (x:Candle)(i:Slot):Bin:=fun a=> freqD (x a) i
def rise (x:Candle)(i:Slot):Bin:= pulse x i + pulse x i
lemma modal(p:Bin)(a:Axis): mode (tmap p) (step a)=pw (p a):=by simp [mode,Lattice.step,tmap,pw,BZ.phase, Pi.single_apply,mul_ite,ite_mul,mul_comm] -- tune
lemma canon (x:Candle)(a:Step)(k:Site N):(matter (Step.read a (tax x) k)).val=Matrix.diagonal (fun i=> mode (tmap (pulse x i)) (a.vec:Cover)):=by
 obtain ⟨i,p|p⟩:=a
 · change (matter ((posDir i).read _ _)).val=_; rw [Step.pos_read]; change (matter (waveG (x i))).val=Matrix.diagonal _; rw [matD]; congr 1; funext j; exact (modal (pulse x j) i).symm
 change (matter ((negDir i).read _ _)).val= _; rw [Step.neg_read,map_inv,tax]; rw [show ↑((matter _)⁻¹)=star (matter (waveG (x i))).val from rfl,matD]; simp_rw [show (Step.mk i true).vec (R:=ℤ)= -(step i) from rfl]; ext j a; by_cases h:j=a
 · subst a; rw [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]; simp only [Matrix.diagonal_apply_eq,Function.comp_apply]; change star (pw (pulse x j i))=_; rw [← modal]; have he:=mode_adjoint (tmap (pulse x j)) (step i); rw [show star _=tmap (pulse x j) from tmap_physical _] at he; exact he
 simp [h,Ne.symm]
lemma travD(x:Candle)(w:Walk)(k:Site N): (matter (travel (tax x) k w)).val=Matrix.diagonal (fun i=> mode (tmap (pulse x i)) (stop (0:Cover) w)):=by
 induction w generalizing k with
 | nil=>simp [travel,mode,Lattice.stop]
 | cons d w ih=>
    rw [travel,map_mul]; rw [show ↑(_*_:UNI Slot)= (matter (d.read _ _)).val*(matter (travel (tax x) (k+d.vec) w)).val from rfl,canon,ih, Matrix.diagonal_mul_diagonal]; congr 1; funext i; rw [stop,zero_add,show stop (d.vec:Cover) w=d.vec+stop (0:Cover) w from ?_,mode_shift] -- tune
    nth_rw 1 [← add_zero (d.vec:Cover)]; exact stop_trans ..
end YM.CF.Kea

import YM.CF.Rush.Arch
/-! Spin position convolutions. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rush
open Fir Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {a:Type*}[DecidableEq a]
/-- Period masks for Laurent operators -/
def wagon (N:Side)(f: Cover→Op a)(z:Cover):Op (Site N×a):=jump (Equiv.addRight (wrap N z)) fun x=>wind x z • f z
def cart (N:Side)(f: Cover→Op a):Op (Site N×a):= Matrix.of fun x y=> ∑' z,wagon N f z x y
lemma wagon_app (N:Side)(f:Cover→Op a)(z: Cover)(x y i j): wagon N f z (x,i) (y,j)= if x+wrap N z=y then wind x z*f z i j else 0 := rfl
structure Reads (f: Cover→Op a)(A: Momentum→Op a) : Prop where
  sumK i j: Summable (fun z=>‖f z i j‖)
  readK (p:Momentum)(h:p∈baseCube)(i j : a) : Laurent.read (X:=ℂ) (fun z:Cover=> f z i j) p=A p i j
variable [Fintype a]
variable {f:Cover→Op a}{A:Momentum→Op a}(h:Reads f A){N:Side}
include h in
lemma wagon_sum (x y:Site N × a): Summable (fun z=> wagon N f z x y):=by
  obtain ⟨x,i⟩:=x; obtain ⟨y,j⟩:=y; apply Summable.of_norm; apply Summable.of_nonneg_of_le _ _ (h.sumK i j)
  · exact fun _=>norm_nonneg _
  intro z; rw [wagon_app]; split
  · simp [wind,fee_norm]
  simp
lemma single_load {p:Momentum}(hm:∀ w:Cover,mode p (N.val • w)=fee w)(b:a)(u: a→ℂ)(f:Cover→Op a) (z x): (wagon N f z *ᵥ fun y=> mode p (natural y.1)*u y.2) (x,b)=mode p (natural x)*mode p z*((f z)*ᵥ u) b:=by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,wagon_app]; rw [sum_eq_single (x+wrap N z)]
  · simp only [if_true]; rw [Finset.mul_sum]; apply sum_congr rfl; intro i _; rw [← wave_advance hm]; ring
  · intro y hy h; simp [Ne.symm h]
  simp
include h in
lemma earns {p:Momentum}(hp:p∈baseCube)(hm:∀ w:Cover,mode p (N.val • w)=fee w) (v : a→ℂ)(x b):
    (cart N f *ᵥ (fun y=> mode p (natural y.1)*v y.2)) (x,b)=mode p (natural x)*(A p *ᵥ v) b:=by
  let q:= fun y:Site N × a=>mode p (natural y.1)*v y.2
  calc
    (cart N f *ᵥ q) (x,b)=∑' z,(wagon N f z*ᵥ q) (x,b):= by
      simp only [cart, Matrix.mulVec,dotProduct,Matrix.of_apply]; simp_rw [← tsum_mul_right]; exact Summable.tsum_finsetSum (fun i _=> (wagon_sum h (x,b) i).mul_right (q i)) |>.symm
    _ = _:= by
      unfold q; simp_rw [single_load hm]; simp only [Matrix.mulVec,dotProduct]; simp_rw [Finset.mul_sum]
      have hx (i:a)(z:Cover): mode p (natural x)*mode p z*(f z b i*v i)=(mode p (natural x)*v i)*(mode p z • f z b i):=by rw [smul_eq_mul]; ring
      simp_rw [hx]; have he (i:a): Summable (fun z=>mode p z • f z b i):=by apply Summable.of_norm; simpa only [norm_smul,mode_real _ _ hp.1,one_mul] using h.sumK b i
      rw [Summable.tsum_finsetSum (fun i _=> (he i).mul_left _)]
      refine sum_congr rfl ?_; intro i _; rw [tsum_mul_left,← Laurent.read, h.readK p hp]; ring
lemma paid {ι:Type*}{w:ι→ℝ}{A:ι→Momentum→Op a}(h:Pay w A)(he:∀ i (p:Momentum), p∈realCube zone→∀ x,p+reciprocal x∈realCube zone→ A i (p+reciprocal x)=A i p) (i:ι): Reads (tub (A i)) (A i):=by
  obtain ⟨⟨η,C,hη,hC,H⟩,hg⟩:=tub_bill h he; exact ⟨fun a b=> ((H i a b).unweighted hη.le).2.1,hg i⟩
variable (N)
open scoped Kronecker
def overU (a: Type*) [Fintype a][DecidableEq a]: UNI (Site N×a):= ⟨Fourier N ⊗ₖ (1:Op a), Matrix.kronecker_mem_unitary (fourier_mem _) (unitary _).one_mem⟩
def mark (A:Momentum→Op a): Op (Site N×a):= jump (Equiv.refl _) fun i=> A (mel i)
def plates (A:Momentum→Op a):Op (Site N×a):=twist (overU N a) (mark N A)
lemma four_id (x k:Site N)(b i : a): (overU N a).val (x,b) (k,i)=mode (mel k) (natural x)*((1:Op a) b i/normF N):=by simp [freq_mode,overU, Fourier]; ring
include h in
lemma cart_traded: cart N f=plates N A:=by
  let U:=overU N a
  suffices he:cart N f*U.val=U.val*mark N A by rw [plates,twist_formula,← he,mul_assoc,show U.val*star U.val=1 from U.property.2,mul_one]
  ext ⟨x,b⟩ ⟨k,i⟩; calc
    _ = (cart N f *ᵥ (fun y=> mode (mel k) (natural y.1)*((1:Op a) y.2 i/normF N))) (x,b) := by simp only [Matrix.mul_apply,Matrix.mulVec,dotProduct]; congr! 2 with y; rw [four_id]
    _ = _:=by rw [earns h (mel_h k) (mode_fee k) (fun y=> (1:Op a) y i/normF N) x b]; simp only [Matrix.mul_apply, Matrix.mulVec,dotProduct,Fintype.sum_prod_type, U,four_id,mark,jump_apply,Equiv.refl_apply]; rw [Finset.mul_sum]; simp [Matrix.one_apply, ite_div, mul_ite, ite_mul]; ring
end YM.CF.Rush

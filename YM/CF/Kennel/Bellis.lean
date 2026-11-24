import YM.CF.Kennel.Terre
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kennel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
section alter
variable {n:Type*}[LinearOrder n][Fintype n]{W:PUnit}{P B X Y K Z C L C':Op n}
private lemma glazed (w:Clad P B X Y K)(t:Clad (1-P) (1-B) Y X L)(q:TagG P C)(e:TagG P C')(hp:IsUnit (1+bentT K B X C))(hx:IsUnit (1+bentT K B X (C+C'))): traitP B K X (C+C')-traitP B K X C= star L*C'*creep K B X (C+C') - star L*C*(1+bentT K B X C)⁻¹*(bentT K B X C')*creep K B X (C+C'):=by
 let D:=bentT K B X C; let R:=bentT K B X (C+C'); let T:=bentT K B X C'; let H:= (1+D)⁻¹; let S:=creep K B X (C+C'); let A:=creep K B X C; have hs:(1+D+T)*S=K:=by rw [show 1+D+T=1+R by unfold D T R bentT; rw [mul_add,add_assoc]]; unfold S creep; rw [←mul_assoc,(live hx).1,one_mul]
 have ha:S=A-H*T*S:=by
   unfold H A creep; have hz:H*K = S+H*T*S:=calc
     _ = H*((1+D+T)*S):=by rw [hs]
     _ = _:=by rw [←mul_assoc, mul_add,add_mul,show H*(1+D)=1 from (live hp).2,one_mul]
   rw [hz]; abel
 have hv:TagG P (C+C'):=⟨by rw [mul_add,q.1,e.1,zero_add],by rw [add_mul,q.2,e.2]⟩
 rw [wingPay w hv hx t,wingPay w q hp t,mul_add (star L),add_mul]; change laneP _ _ _ + (star L*C*S+star L*C'*S) - (laneP _ _ _ + star L*C*A)= _; nth_rw 1 [ha]; rw [mul_sub]; simp only [mul_assoc]; unfold S H D A T creep bentT; simp only [Matrix.mul_assoc]; abel -- unfold order
lemma glaze {ι:Type*}{f:Filter ι}(P B X Y K L C C':ι→ Op n)(A:ι→ℝ){p b x y k l c:Op n}(t:Tendsto P f (𝓝 p))(u:Tendsto B f (𝓝 b))(v:Tendsto X f (𝓝 x))(w:Tendsto K f (𝓝 k))(h:Tendsto L f (𝓝 l))(q:Tendsto C f (𝓝 0))(hp:Tendsto C' f (𝓝 0))(hx:Tendsto (fun i=>A i • C' i) f (𝓝 c))(D:∀ᶠ i in f,Clad (P i) (B i) (X i) (Y i) (K i)∧Clad (1-P i) (1-B i) (Y i) (X i) (L i)∧ TagG (P i) (C i)∧ TagG (P i) (C' i)):
 Tendsto (fun i=> A i • (traitP (B i) (K i) (X i) (C i+C' i)-traitP (B i) (K i) (X i) (C i))) f (𝓝 (star l*c*k)):=by
 let U(i):=1+bentT (K i) (B i) (X i) (C i); let V(i):=1+bentT (K i) (B i) (X i) (C i+C' i); let W(i):=bentT (K i) (B i) (X i) (A i • C' i); let F(i):=creep (K i) (B i) (X i) (C i+C' i)
 have he : Tendsto U f (𝓝 1):=by simpa [U] using (((w.mul (u.mul v)).mul q).const_add 1)
 have hy:Tendsto V f (𝓝 1):=by simpa [V] using (((w.mul (u.mul v)).mul (q.add hp)).const_add 1)
 let T :Op n→Op n:= fun y=>y⁻¹; have ht:Tendsto T (𝓝 1) (𝓝 1):=by
    have hp:Tendsto T (𝓝 1) (𝓝 (T 1)):= (inv_p (R:=(1:Op n)) isUnit_one).continuousAt.tendsto; simpa [T] using hp
 have hg:Tendsto F f (𝓝 k):=by rw [←one_mul k]; exact (ht.comp hy).mul w
 have hk:Tendsto W f (𝓝 (k*(b*x)*c)):= (w.mul (u.mul v)).mul hx
 have hm:= (h.star.mul hx|>.mul hg).sub (((((h.star.mul q).mul (ht.comp he)).mul hk).mul hg)); simp only [mul_zero,zero_mul,sub_zero] at hm; apply hm.congr'
 have hI:∀ᶠ i:Op n in 𝓝 1, IsUnit i:= Units.isOpen.mem_nhds (show (1:Op n) ∈ {x|IsUnit x} from isUnit_one)
 filter_upwards [he.eventually hI,hy.eventually hI,D] with i hl hy ⟨hg,hz,hx,hF⟩
 rw [glazed hg hz hx hF hl hy]; simp only [smul_sub, ← Matrix.smul_mul]; simp only [W,bentT,T,U, Function.comp_apply,F]; -- tune Matrix.smul_mul LHS occurrence wrong
 simp only [Matrix.mul_smul,Matrix.smul_mul]
end alter
variable {N Q:Side}(G:Ratio N Q)(P S:Op (Iota G))(F:Op (Single Q))
def pierM : Op (Single Q)→L[ℝ] Op (Single N):= (show Op (Single Q)→ₗ[ℝ] Op (Single N) from ⟨⟨fun X=>summit (patchQ G) (star P*foot G X*S),fun i j=>by rw [foot_add,mul_add,add_mul]; rfl⟩,fun c i=>by change summit (patchQ G) (star P*foot G (c • i)*S)= c • summit (patchQ G) (star P*foot G i*S); rw [show foot G (c • i)=c • foot G i from rfl, Matrix.mul_smul,Matrix.smul_mul]; rfl⟩).toContinuousLinearMap
lemma vested:pierM G P S F = Matrix.conjTranspose (arch G P)*F*(arch G S):=by
 change summit (patchQ G) (star P*foot G F*S)= _; ext x y; let U:=switchG G; let A:=patchQ G
 change ∑ i:Iota G,(∑ j:Iota G, star (P j (A x))*foot G F j i)*S i (A y)= ∑ i:Single Q,(∑ j:Single Q, star (arch G P j x)*F j i)*arch G S i y
 conv_rhs => rw [← Equiv.sum_comp U]
 apply sum_congr rfl; intro i _; congr 1
 conv_rhs => rw [← Equiv.sum_comp U]
 refine sum_congr rfl fun j _=>?_; unfold arch; simp only [U, Matrix.of_apply, Equiv.symm_apply_apply]; rfl
 unfold arch; simp [U,A]
end YM.CF.Kennel

import YM.CF.Aroma.Nest
import YM.CF.Thera.Lawn
set_option autoImplicit false
noncomputable section
namespace YM.CF.Aroma
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Rush Cube MeasureTheory NormedSpace
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][DecidableEq n]{N M:Side}
def ski(T:Op n)(x:Air N): Cab n N:= jump (Equiv.refl _) fun i=> (x (node i):ℂ) • thrust T
def Dir(x:Air N): Prop:=∀ z:Site (More N),∀ i:Axis,i≠1→x (z+step i)=x z
def lop(x:Air N):Air N:= fun z=> x z - x (z+step 1)
structure Foot(T:Op n)(j:ℕ)(M:Side)(J:InJ n N):Prop where
 oddM:Odd M.val
 realT:star T=T
 smooth:ContDiffAt ℝ ω J 0
 curve:CurveH J
 heft:∀ᶠ x in 𝓝 0,flatV n N * J x= J x
 around:J 0=subHub fun i=> fuel n j M (mel i)
 peak :∀ x:Air N,Dir x→∀ᶠ s:ℝ in 𝓝 0,J (s • lop x)= exp (s • ski T x)* J 0 *star (exp (s • ski T x))
lemma tiltQ (T: Op n)(e:star T=T)(x: Air N): star (ski T x)= -(ski T x):=by unfold ski; rw [jump_star, ←jump_neg]; congr 1; ext1 i; simp only [Equiv.refl_symm,Equiv.refl_apply,star_smul,thrust,op_star_kron,star_one, e,Complex.conj_I, show star Complex.I = -Complex.I from Complex.conj_I,op_kron_smul]; rw [show star ((x _:ℝ):ℂ)=(x _:ℝ) from Complex.conj_ofReal _]; simp
lemma trail8 (a:Axis)(o:ℕ)(ho:16≤N.val)(k: Site N)(r:ℝ)(h:|r|≤pinch N) : spoon (mel k) (spark a (r:ℂ))∈ realCube zone:=by
 let x:= spark a (r:ℂ); have hp:=mel_h k; refine ⟨?_,fun i=>?_⟩
 · unfold physical; rw [spoon,star_add,star_add,hp.1,spark_star]; simp
 have hh:0<zone:=zone_pos; have hx:= hp.2 i
 by_cases H:i=a
 · subst i; have ht: (16:ℝ) ≤ N.val := by exact_mod_cast ho
   have he : 2*pinch N< zone:=by
      unfold zone pinch; rw [← mul_div_assoc]; calc
        _ ≤ 2*Real.pi/(16:ℝ):=by gcongr
        _ < _:=by have:= Real.pi_pos; linarith
   simp only [spoon,spark,Pi.add_apply,Pi.smul_apply,smul_eq_mul, Lattice.step_apply,ite_true, mul_one,Complex.add_re, Complex.ofReal_re]; rw [abs_lt]; constructor <;> linarith [(abs_le.mp h).1,(abs_le.mp h).2,(abs_le.mp hx).1,(abs_le.mp hx).2]
 simpa [spoon,spark,H] using (hx.trans_lt (show Real.pi<Real.pi+zone by linarith))
lemma slid_f(q: Momentum)(F:Tide N q)(i:Site N)(v:spoon (mel i) q∈realCube zone)(j:ℕ)(M:Side): fuel n j M (mel (F.σ i))=fuel n j M (spoon (mel i) q) ∧ edgeH n j M (mel (F.σ i))=edgeH n j M (spoon (mel i) q):=by
 obtain ⟨w,hw⟩:=F.cost i; have hf:=base_subset_realCube zone_pos (mel_h (F.σ i)); unfold fuel edgeH; rw [hw, bar_overlap j M hf w (hw ▸ v),(shell_overlap j M) _ hf _ (hw ▸ v)] -- tune
 trivial
namespace Foot
variable {T:Op n}{j:ℕ}{J:InJ n N}(P:Foot T j M J)
include P
lemma ride (x:Air N)(h:Dir x):JD J (lop x)= ski T x* J 0 - J 0*ski T x:=by
 let F(s:ℝ):=exp (s • ski T x); let f(s:ℝ):= s • lop x
 have hf:f 0=0:=zero_smul ..; have he:F 0=1:=by simp [F]
 have hx:HasDerivAt (J ∘ f) (JD J (lop x)) 0:=by
   have hp: HasFDerivAt J (JD J) (f 0):=by rw [hf]; exact (P.smooth.differentiableAt (by simp)).hasFDerivAt
   apply hp.comp_hasDerivAt; exact hasDerivAt_id' (0:ℝ) |>.smul_const _ |>.congr_deriv (by simp)
 have hF:HasDerivAt F (ski T x) 0:=by have h:=hasDerivAt_exp_smul_const (ski T x) (0:ℝ); simpa only [zero_smul,exp_zero,one_mul] using h
 let L: Cab n N→L[ℝ] Cab n N:=(starL ℝ).toContinuousLinearMap; have hp:HasDerivAt (fun s=>star (F s)) (star (ski T x)) 0:=L.hasFDerivAt.comp_hasDerivAt 0 hF
 have hl:(fun s=>F s*J 0*star (F s))=ᶠ[𝓝 0] J ∘ f:= (show J ∘ f=ᶠ[𝓝 0] _ from P.peak x h).symm; have hu:= (hx.congr_of_eventuallyEq hl).unique ((hF.mul_const (J 0)).mul hp); rw [he,star_one,mul_one,one_mul,tiltQ T P.realT,mul_neg] at hu; rw [sub_eq_add_neg]; exact hu
end Foot
end YM.CF.Aroma

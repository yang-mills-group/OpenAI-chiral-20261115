import YM.SU5.Relativistic.Ukase
import YM.SU5.Relativistic.Millet
/-! # first variations. Disk squeeze instead of killing concatenated tokens. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Fock Lattice Finset Thera Pea
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators ComplexOrder InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I][Nonempty I]{P:Op I}(p:IsStarProjection P)(A:Pea I){H F:FC I}(T:A.GlowGap H)
def peak (μ R z:ℝ):= 1+μ*z+8*R^2*z^2
private lemma peak_v {μ C u a x b y h:ℝ} (hx:0≤μ)(hp:0≤C)(vg:0≤u)(ht:0≤a)(hg:0≤x)(hv:0≤b) (p:a^2+b^2≤ x^2 -3*b^2) (hh:h^2=a^2+b^2)
    (hT:y^2≤h^2+2*(u* (μ*x^2+3*b*C*x))+(u*C*x)^2 ) : y≤ peak μ C u*x:=by
 let r:=μ*u+8*C^2*u^2; have hK:0≤r:=by unfold r; positivity
 have he : peak μ C u=1+r:=by unfold r peak; ring
 rw [he]; apply le_of_sq_le_sq _ (by positivity)
 unfold r; nlinarith only [hh,p,hT, sq_nonneg (b-u*C*x), sq_nonneg (μ*u*x),mul_nonneg (sq_nonneg (C*u*x)) (mul_nonneg hx vg), sq_nonneg (C^2*u^2*x)] -- r unfold last
local notation "K"=> A.hat
include T
lemma gapFund (C μ:ℝ)(z:ℂ)(r:‖F‖≤C)(h:‖H*F*H‖ ≤ μ): ‖(1+z • F)*K‖ ≤ peak μ C ‖z‖:=by
 have hc:0≤C:=(norm_nonneg _).trans r; have hp:=T.head
 let d:=‖z‖; have he:0≤μ:= (norm_nonneg _).trans h; have hW : 0≤peak μ C d:=by unfold peak d; positivity
 rw [←Matrix.l2_opNorm_toEuclideanCLM]; refine ContinuousLinearMap.opNorm_le_bound _ hW fun x=>?_
 let V:= acts K x; let L:=acts H x; let X:=1-H; let B:=acts X x; let U:=acts K B
 have hK: H*K=H:=by simpa only [star_mul,T.head.isSelfAdjoint.star_eq,A.star_h.star_eq] using congrArg star T.shell
 have hm:X*K=K*X:=by unfold X; rw [sub_mul,mul_sub,one_mul,mul_one,hK,T.shell]
 have hh:V=L+U:=by
    unfold V L U B; rw [←act_mul]; rw [←act_add,show H+K*X=K from by unfold X; rw [mul_sub,mul_one,T.shell]; abel]
 have hl(X:FC I)(y:Wave I)(p:IsStarProjection X) : ‖acts X y‖≤‖y‖:=(Graph.spentS ..).trans (mul_le_of_le_one_left (norm_nonneg _) (p.norm_le _))
 have hf:‖U‖ ≤ 1/2*‖B‖:=by
    unfold U; rw [show acts K B=acts (K*X) B from by unfold B; rw [←act_mul,←act_mul, mul_assoc,T.head.one_sub.isIdempotentElem.eq]]; exact (Graph.spentS ..).trans (mul_le_mul_of_nonneg_right T.grade (norm_nonneg _))
 have hs:‖V‖^2=‖L‖^2+‖U‖^2:=by unfold U B; rw [show acts K (acts X x)=acts X V from by unfold V; rw [←act_mul, ←act_mul,hm], show L=acts H V from (by unfold V; rw [←act_mul,hK])]; exact (BProof.Align.splitOrth V T.head).symm -- polymorphism check
 have hx:= BProof.Align.splitOrth x T.head
 have hv:‖V‖ ≤ ‖x‖:= (Graph.spentS ..).trans (mul_le_of_le_one_left (norm_nonneg _) T.cap)
 have h0: inner ℂ L (acts F L)=inner ℂ x (acts (H*F*H) x):=by unfold L; nth_rw 1 [←(show star H=H from T.head.isSelfAdjoint)]; rw [act_inner,act_mul,act_mul]; -- parse rw act_mul
 have fX:= norm_nonneg x
 have hz:‖inner ℂ V (acts F V)‖ ≤ μ*‖x‖^2+ 3*‖U‖*C*‖x‖:=by
    have hu(T:Wave I):‖acts F T‖ ≤ C*‖T‖:=(Graph.spentS ..).trans (mul_le_mul_of_nonneg_right r (norm_nonneg _))
    have ht:‖inner ℂ L (acts F L)‖≤ μ*‖x‖^2:=by rw [h0]; exact (norm_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left ((Graph.spentS ..).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))) (norm_nonneg _)).trans_eq (by ring))
    nth_rw 1 [hh]; rw [inner_add_left, show inner ℂ L (acts F V)=inner ℂ L (acts F L)+inner ℂ L (acts F U) from (by rw [hh,map_add,inner_add_right])]
    refine (norm_add_le ..).trans (le_trans (add_le_add_left (norm_add_le ..) _) (le_trans (add_le_add (add_le_add ht (le_trans (norm_inner_le_norm ..) (mul_le_mul (hl _ _ T.head) (hu _) (norm_nonneg _) (norm_nonneg _)))) ((norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left ((hu _).trans (mul_le_mul_of_nonneg_left hv hc)) (norm_nonneg _)))) ?_))
    nlinarith only [mul_nonneg (mul_nonneg (norm_nonneg U) hc) fX]
 let C':=z • acts F V; change ‖acts ((1+z • F)*K) x‖≤ _; rw [act_mul,act_add,act_one,act_smul]; apply peak_v he hc (norm_nonneg _) (norm_nonneg L) (norm_nonneg x) (norm_nonneg U) ?_ hs
 swap
 · -- tune goals
   change ‖L‖^2+‖B‖^2=_ at hx; nlinarith only [pow_le_pow_left₀ (norm_nonneg _) hf 2, hx] -- reducible L B
 change ‖V+C'‖^2 ≤ _; rw [norm_add_sq (𝕜:=ℂ)]; have ht: (inner ℂ V C').re ≤ ‖z‖ * (μ*‖x‖^2+3*‖U‖*C*‖x‖):=by apply (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans _); unfold C'; rw [inner_smul_right,norm_mul]; exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)
 have h'g: ‖C'‖≤ ‖z‖*C*‖x‖:=by unfold C'; rw [norm_smul,mul_assoc ‖z‖]; exact mul_le_mul_of_nonneg_left ((Graph.spentS ..).trans (mul_le_mul r hv (norm_nonneg _) hc)) (norm_nonneg _)
 change ‖V‖^2+2*(inner ℂ V C').re+‖C'‖^2≤_; linarith only [ht,pow_le_pow_left₀ (norm_nonneg _) h'g 2]
-- world already after tilt. supplier compression with slim sector and close. Leak theorem footprint sufficient
include p
lemma nearCore {v:Wave I}{η:ℝ}(f:Sea P v)(q:Real.exp (4*A.leak P)^2≤1+3*η^2)(b:0≤η) : ‖acts H v-v‖ ≤ η:=by
 let W:= acts A.tagH v; let L:=1-H; let V:=acts L v
 have hv: ‖W‖^2 ≤1+3*η^2:=by
    have hx:‖W‖≤ Real.exp (4*A.leak P):=by unfold W tagH; rw [act_smul]; exact A.frosty p _ f
    exact (pow_le_pow_left₀ (norm_nonneg _) hx _).trans q
 have hy:acts K W=v:=by unfold W; rw [←act_mul, intake,act_one]
 have ht:H*K=H:= by simpa only [star_mul,T.head.isSelfAdjoint.star_eq,A.star_h.star_eq] using congrArg star T.shell
 have hp: acts H W=acts H v:=by nth_rw 1 [←hy]; rw [←act_mul H K,ht]
 have hL:L*K=K*L:=by unfold L; rw [sub_mul,mul_sub,one_mul,mul_one,ht,T.shell]
 have he:‖V‖≤1/2*‖acts L W‖:=by
    have he0:V=acts (K*L) (acts L W):=by rw [←act_mul, mul_assoc,T.head.one_sub.isIdempotentElem,←hL,act_mul,hy]
    rw [he0]; exact (Graph.spentS ..).trans (mul_le_mul_of_nonneg_right T.grade (norm_nonneg _))
 rw [norm_sub_rev, show v-acts H v=acts L v from (?_)]
 · apply le_of_sq_le_sq _ b; have hx:= BProof.Align.splitOrth v T.head; have hp':= BProof.Align.splitOrth W T.head; rw [hp] at hp'; rw [f.2] at hx; nlinarith only [pow_le_pow_left₀ (norm_nonneg _) he 2,hx,hp',hv]
 unfold L; rw [act_sub,act_one]
lemma aware {v:Wave I}{C η μ:ℝ}(a:‖A.tagH‖≥0)(q:Real.exp (4*A.leak P)^2≤1+3*η^2)(b:0≤η)(e:η≤1/2)(f:Sea P v)
    (h:∃ c:ℂ,H*F*H=c • H)(u:‖F‖≤C)(j:‖inner ℂ v (acts F v)‖ ≤ μ) : ‖H*F*H‖ ≤ 4*(μ+2*C*η):=by
 let W:= acts H v; have he:‖W‖ ≤1:= (Graph.spentS ..).trans ( (mul_le_mul_of_nonneg_right (T.head.norm_le _) (norm_nonneg _)).trans_eq (by rw [f.2,one_mul]))
 have g:= nearCore p A T f q b; have hf:(1:ℝ)/2 ≤ ‖W‖:=by
    have hp:= norm_le_norm_sub_add v W; have hx:‖v-W‖≤η:=(norm_sub_rev v W).trans_le g; linarith [f.2]
 obtain ⟨c,w⟩:=h
 have hh: inner ℂ W (acts F W)=c*(↑(‖W‖^2):ℂ):=by
    have hp: H*F*H=c • (H*H):= by rw [T.head.isIdempotentElem,w]
    unfold W; nth_rw 1 [←(show star H=H from T.head.isSelfAdjoint)]; rw [act_inner,←act_mul,←act_mul,hp,act_smul,inner_smul_right]; rw [act_mul,←act_inner,T.head.isSelfAdjoint,inner_self_eq_norm_sq_to_K]; push_cast; rfl -- tune rw x order RCLike
 have hv: ‖inner ℂ W (acts F W)-inner ℂ v (acts F v)‖ ≤ 2*C*η:=by
    have hX:‖acts F W‖ ≤ C:= (Graph.spentS ..).trans ((mul_le_of_le_one_right (norm_nonneg _) he).trans u)
    rw [show inner ℂ W (acts F W)-inner ℂ v (acts F v)=inner ℂ (W-v) (acts F W)+inner ℂ v (acts F (W-v)) from (by rw [map_sub,inner_sub_left,inner_sub_right]; ring)]
    exact (norm_add_le ..).trans ((add_le_add ((norm_inner_le_norm ..).trans (mul_le_mul g hX (norm_nonneg _) b)) ((norm_inner_le_norm ..).trans (mul_le_mul f.2.le ((Graph.spentS ..).trans (mul_le_mul u g (norm_nonneg _) ((norm_nonneg _).trans u))) (norm_nonneg _) zero_le_one))).trans_eq (by ring))
 have hz:= norm_le_norm_sub_add (inner ℂ W (acts F W)) (inner ℂ v (acts F v)); have hy: ‖c‖*‖W‖^2 ≤ 2*C*η+μ:=by
    rw [hh,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)] at hz; -- also updated RHS!
    rw [←hh] at hz -- wrong norm?
    exact hz.trans (add_le_add hv j)
 rw [w,norm_smul]; apply le_trans (mul_le_of_le_one_right (norm_nonneg c) (T.head.norm_le _)); nlinarith only [hy,mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hf 2) (norm_nonneg c)]
end YM.CF.Papyrus.Franc
#print axioms YM.CF.Papyrus.Franc.aware

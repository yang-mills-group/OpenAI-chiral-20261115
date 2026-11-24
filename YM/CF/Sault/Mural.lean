import YM.CF.Sault.Faro
import YM.CF.Proa.Wings
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sault
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Pastry
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Scree
variable {n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]
-- general dΓ form
abbrev urn(f g:n→FC m)(P:Op n):FC m:=∑ i,∑ j, P i j • (f i*g j)
abbrev crock(f:n→FC m)(P:Op n)(i:n):=∑ j, P j i • f j
lemma clove (f g:n→FC m)(S T P:Op n): urn (crock f S) (crock g T) P=urn f g (S*P*Tᵀ):=by
  unfold urn crock; simp_rw [sum_mul,mul_sum,Matrix.mul_apply,sum_mul,sum_smul,smul_sum,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul,Matrix.transpose_apply]
  let D (i j p q : n) := (P i j*(T q j*S p i)) • (f p*g q)
  change ∑ i,∑ j,∑ p,∑ q, D i j p q=_
  simp_rw [sum_comm (f:=fun i j=>∑ p,∑ q,D i j p q), sum_comm (f:=fun i p=>∑ q,D i _ p q),
    sum_comm (f:=fun j p=>∑ i,∑ q,D i j p q), sum_comm (f:=fun i q=>D i _ _ q), sum_comm (f:=fun j q=>∑ i,D i j _ q)]
  simp [D,mul_comm,mul_assoc, mul_left_comm]
lemma crock_one (f:n→FC m):crock f 1=f:=by funext i; unfold crock; simp [Matrix.one_apply,ite_smul]
lemma podA(b:Bool)(f:Op n): urn (trailM b) (wire b) f= Matrix.trace f • 1 - urn (wire b) (trailM b) fᵀ:=by
 unfold urn trailM wire
 have he (i j:n): takeF (n:=LeanV n) (b,i)*put (b,j)=(if i=j then 1 else 0)-put (b,j)*takeF (b,i):=by apply eq_sub_of_add_eq; rw [mixed]; simp
 simp_rw [he,smul_sub,sum_sub_distrib]; rw [sum_comm (f:=fun i j=> f i j • _)]; -- tune picks first sum not second
 congr 1; simp [Matrix.trace,apply_ite _ _,Finset.sum_smul]
 exact sum_comm
-- components. DRESS: anchor PK−PtB trace for physical frame scalar. parity derivative close.CAR
abbrev forge (L K W V R:Op n):FC (LeanV n):= faceD true false K+urn (wire true) (trailM true) W+ (Matrix.trace L • 1-urn (wire false) (trailM false) Vᵀ)+ urn (trailM false) (trailM true) R
variable {P:Op n}
lemma sand(p:IsStarProjection P)(K:Op n): urn (palm P) (hilt P) K=forge (P*K) K (K*(1-P)) (P*K) (P*K*(1-P)):=by
 let W:=1-P; let F:=trailM (n:=n) true; let G:=trailM (n:=n) false; let T:=wire (n:=n) true; let S:=wire (n:=n) false
 have hp(i:n):palm P i=T i+crock G P i:=by unfold palm; have ht:P=(cc P)ᵀ:=(ccT P|>.trans p.isSelfAdjoint).symm; congr 1; unfold crock; nth_rw 2 [ht]; rfl
 have hq(i:n):hilt P i= S i+crock F Wᵀ i:=rfl
 have hv:urn (palm P) (hilt P) K=urn T S K+urn T (crock F Wᵀ) K+ urn (crock G P) S K+urn (crock G P) (crock F Wᵀ) K:=by unfold urn; simp_rw [hp,hq,add_mul,mul_add,smul_add,sum_add_distrib]; abel
 rw [hv,show urn T (crock F Wᵀ) K=urn T F (K*W) from (by nth_rw 1 [←crock_one T]; rw [clove,one_mul,Matrix.transpose_transpose]),show urn (crock G P) S K=urn G S (P*K) from (by nth_rw 1 [←crock_one S]; rw [clove,Matrix.transpose_one,mul_one]),clove,Matrix.transpose_transpose,podA]
lemma loft(p:IsStarProjection P)(K:Op n)(x: Wave n)(g:Sea P x)(X:Wave (LeanV n)):let L:=ballL (nursery P p) x; let V:=P*K; let B:=1-P
 L (acts (forge V K (K*B) V (V*B)) X)=acts (dg K) (L X):=by
 intro L V B; rw [←sand p,urn,dg,dyad,act_sum,map_sum,act_sum]; apply sum_congr rfl; intro i hj; rw [act_sum,map_sum,act_sum]; apply sum_congr rfl; intro j hg; rw [act_smul,map_smul,act_smul,act_mul,act_mul]; congr 1; unfold L; rw [polar p x g,bore p x g] -- tune
lemma zeal (V U:Op n)(p:V*U=1)(K:Op n) : dg K*quant U=quant U* dg (V*K*U):=by
 have hv:dg (V*K*U)=dyad K (prong put V) (prong takeF (cc (star U))):=by rw [dyad_prong,ccT,star_star]; rfl
 rw [hv]; simp only [dg,dyad,sum_mul,mul_sum]
 apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; apply congrArg
 rw [prong_p,prong_t, ←mul_assoc (quant U),quant_create,←act_mul,mul_eq_one_comm.mp p,act_one,create_put,mul_assoc,mul_assoc,←quant_ann,remove_take] -- tune quant_ann direction
open Thera
lemma flank(p:IsStarProjection P)(A:Op n)(h:TagG P A)(F:FC (LeanV n)): Commute (exp (dg A)) ((nursery P p).eval F):=by
 change Commute _ (∑ i:Finset (LeanV n),crumb F i • (nursery P p).tag i); apply Commute.sum_right; intro i _; apply Commute.smul_right
 clear ‹i∈_›
 induction i using Finset.induction_on_min with
 | empty=> rw [Poly.tag_void]; exact Commute.one_right _
 | insert j s k ih=>rw [Poly.tag_min _ _ _ k]; rcases j with ⟨b,v⟩; apply Commute.mul_right _ ih; cases b; exact Proa.moves _ _ p h (true,v); exact Proa.moves _ _ p h (false,v)
lemma lumen (p:IsStarProjection P)(C:Op n)(h:TagG P C)(x:Wave n)(w:Wave (LeanV n)):let T:=nursery P p; acts (exp (dg C)) (ballL T x w)=ballL T (acts (exp (dg C)) x) w:=by
 intro T; change acts _ (∑ i:Finset (LeanV n), w.ofLp i • acts (T.tag i) x) = _; rw [map_sum]; change ∑ i:Finset (LeanV n),_=∑ i:Finset (LeanV n),_; apply sum_congr rfl; intro i _; rw [map_smul, ←act_mul, ←act_mul (T.tag i), ←Poly.eval_oneT, (flank p C h _).eq] -- tune
lemma plume (p:IsStarProjection P)(A C:Op n)(h:TagG P A)(x:Wave n)(s:Sea P x)(F:Wave (LeanV n))(Q:Op n):let K:=(1-A)*Q*(1+A); let T:=nursery P p; let y:= acts (exp (dg A)) x; let L:=ballL T y; let U:=C*Q
 L (acts (forge (P*K-U) K (K*(1-P)) (P*K) (P*K*(1-P))) F)=acts (dg Q-Matrix.trace U • 1) (L F):=by
 intro K T y L U
 have hp:(1-A)*(1+A)=1:=by simp only [mul_add,sub_mul,mul_one,one_mul,h.nil]; abel
 let B:=ballL T x; let D:=exp (dg A); have ht(q): L q=acts D (B q):=(lumen p A h x q).symm; let S':= forge (P*K) K (K*(1-P)) (P*K) (P*K*(1-P))
 rw [show forge _ K _ _ _=S'-Matrix.trace U • 1 from (by unfold S' forge; rw [Matrix.trace_sub,sub_smul]; abel), act_sub,act_smul,act_one,map_sub,map_smul,ht, show B _= _ from loft p _ x s F, act_sub,act_smul,act_one, ht,←act_mul]; congr 1; rw [←act_mul,show D=quant (1+A) from tallied _ h.nil, zeal (1-A) (1+A) hp]; -- tune rw direction expand L
end YM.CF.Sault

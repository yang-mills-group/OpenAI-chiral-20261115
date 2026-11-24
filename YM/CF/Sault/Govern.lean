import YM.CF.Sault.Crown
import YM.CF.Sault.Cider
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sault
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Pastry
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Scree
variable {n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]
-- general dΓ form
variable (b r:Bool)(V: UNI n)
local notation "S"=> sauce b r V
local notation "R"=> sings b V
-- normal packet class
abbrev dma(P A Q C:Op n) : FC (LeanV n):=let K:=(1-A)*Q*(1+A); forge (tally P C K Q) K (K*(1-P)) (P*K) (P*K*(1-P))
local notation "L"=> hitL b r V
local notation "X"=> doveL b r V
lemma rake (A Q:Op n):(1-L A)*L Q*(1+L A)= L ((1-A)*Q*(1+A)):=by
 unfold hitL Thera.jazz; cases r
 · simp [win_i]
 simp only [ite_true,singT,win_m,map_mul,star_mul,win_l,win_a,win_i,map_sub,map_add,map_one,star_add,star_sub,star_one]; simp only [mul_assoc,mul_neg,neg_mul]; rw [←sub_eq_add_neg]; simp
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000
lemma gild(P K: Op n)(t:star P=P): let A:= swapX r (R P); let Q:= L K; let W:=K*(1-P); let T:=P*K
 A*Q=L (if r then W else T)∧ Q*(1-A)= L (if r then T else W)∧A*Q*(1-A)= L (P*K*(1-P)) ∧ rise A Q=X (rise P K):=by
 intro A Q W T; have hv:cSignX b ((2:ℂ)⁻¹)=(2:ℂ)⁻¹:=by cases b; rfl; norm_num [cSignX]
 unfold rise A Q W T hitL doveL
 cases r
 · simp [swapX,Thera.jazz,win_i,hv,twist_scalar]
 simp only [ite_true,swapX,Thera.jazz,singT,win_i,win_l,win_m,map_sub,map_mul,map_add, map_one, star_add,star_sub,star_mul,star_one,win_c,win_a, twist_scalar, hv,star_smul]; push_cast
 have hu:star (twist V (windX b P))=_:= (show star (twist V (windX b P))=twist V (windX b P) from (by rw [←map_star, ←win_s,t])); simp only [hu,map_sub,map_add,map_one,map_mul,star_sub,star_add,star_one,star_mul,mul_neg,neg_mul,sub_sub_cancel]; refine ⟨True.intro,True.intro,?_,?_⟩; rw [mul_assoc]
 rw [show star ((2:ℂ)⁻¹)=(2:ℂ)⁻¹ by norm_num]; simp only [sub_mul,mul_sub,one_mul,mul_one]; congr 1; abel
lemma rollV (P A Q C:Op n) (k:star P=P)(p:star C=C):dma (swapX r (R P)) (L A) (L Q) (swapX r (R C))= S (dma P A Q C):=by
 have hv(J Y:Op n):doveL b r V (J-Y)=doveL b r V J-doveL b r V Y:=by cases r<;> simp [doveL]
 unfold dma; rw [quest]; dsimp only -- tune
 let B:=(1-A)*Q*(1+A); obtain ⟨ht,hz,hk,hl⟩:= gild b r V P B k
 rw [rake b r V A Q,hk,hz,ht]; unfold tally; rw [hl,(gild b r V C Q p).2.2.2,hv] -- tune
lemma wardD (P A Q C:Op n) (k:star P=P)(p:star C=C)(F:FC (LeanV n)): rind (dma (swapX r (R P)) (L A) (L Q) (swapX r (R C))* S F)= S (rind (dma P A Q C *F)):=by rw [plower,rollV b r V P A Q C k p, show S (_*_) = _ from singm ..]
-- combine transform frame.M uses ROOT correlation. CONVERGENCE at all β.W. Polynomials t. sign.
end YM.CF.Sault

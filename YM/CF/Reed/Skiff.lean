import YM.CF.Reed.Hawk
import YM.CF.Fock.Sphere
set_option linter.unusedSectionVars false

/-! Exterior substitution in ordered two-sector coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Reed
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock NormedSpace Function Finset Pastry Phase
attribute [local instance] opCStarAlgebra
variable {n m : Type*} [LinearOrder n] [Fintype n] [LinearOrder m] [Fintype m]
lemma plain_axis (S : Finset n): Plain (axis S) := Absorb.lot _ _ (fun i _=>by
  have ht : Plain (bar i * col i) := (Absorb.blade (mem_univ (false,i))).times (Absorb.blade (mem_univ (true,i))); simpa [ballad] using ht.scale (-1))
lemma eval_blade (f : Poly n m) (i:n) : f.eval (put i)= f.term i := by rw [show put i=poke {i} from (Poly.tag_once (cane _) _).symm, f.eval_oneT,f.tag_once]
-- use closed supported log eval series
lemma eval_expose {A : FC n} (h : Plain A) (v : Poly n m) : v.eval (exp A)=exp (v.eval A) := by
  let L : FC n →L[ℂ] FC m := ⟨v.eval,v.eval.continuous_of_finiteDimensional⟩
  have he : ∀ i:ℕ, Plain (A^i) ∧ L (A^i)=(v.eval A)^i := by
    intro i; induction i with
    | zero=> rw [pow_zero,pow_zero]; exact ⟨Absorb.one,v.eval_one⟩
    | succ i ih=> rw [pow_succ,pow_succ]; exact ⟨ih.1.times h, Eq.trans (ih.1.eval h v) (congrArg (·*v.eval A) ih.2)⟩
  change L _=_
  rw [exp_eq_tsum ℂ]; dsimp only; rw [L.map_tsum ( (norm_expSeries_summable' (𝕂:=ℂ) A).of_norm)] -- tune
  rw [exp_eq_tsum ℂ]; dsimp only; exact tsum_congr (fun i=> Eq.trans (L.map_smul _ _) (congrArg _ (he i).2))
def tote (s : Finset n) (U : Op n) (i : n) := ∑ j∈s,U i j • col j
def tube (s : Finset n) (U : Op n) : Poly (LeanV n) (LeanV n) where
  term i:= if i.1 then tote s U i.2 else bar i.2
  anti i j:= by
    rcases i with ⟨b,i⟩; rcases j with ⟨g,j⟩; cases b <;> cases g <;> simp only [Bool.false_eq_true,ite_false,ite_true]; exact put_put _ _
    all_goals simp only [tote,antiB_sum',antiB_sum, antiB_smul',antiB_smul,bar,col,wire,antiB, put_put, smul_zero,sum_const_zero]
lemma tube_bar (s : Finset n) (U : Op n) (i:n) : (tube s U).eval (bar i)=bar i := eval_blade ..
lemma tube_eta (s : Finset n) (U : Op n) (i:n): (tube s U).eval (col i)=tote s U i:= eval_blade ..
lemma thetaB (S : Finset n) : Plain ((θ n).tag S) := by
  induction S using Finset.induction_on with | empty=> rw [Poly.tag_void]; exact Absorb.one
                                             | insert i S p ih=> rw [Poly.tag_any _ _ _ p]; exact ((Absorb.blade (mem_univ (false,i))).times ih).scale _
lemma theta_inv (v : Finset n) (U : Op n) (T : Finset n) : (tube v U).eval ((θ n).tag T)=(θ n).tag T := by
  induction T using Finset.induction_on with
  | empty=> rw [Poly.tag_void,Poly.eval_one]
  | insert i t p ih=> let P := tube v U; rw [Poly.tag_any _ _ _ p, map_smul]; congr 1; change P.eval (bar i*_)=bar i*_ ; rw [Absorb.eval (s:=univ) (show Plain (bar i) from Absorb.blade (mem_univ _)) (thetaB _) P,show P.eval (bar i)=_ from tube_bar .., show P.eval ((θ n).tag _)=_ from ih]
-- creator frame map on occupied columns. quant transpose
lemma light_put (i:n): cc (put i)=put i := put_clear _ -- tune import
lemma quant_clear (A : Op n) : quant (cc A)=cc (quant A) := by
  symm; apply quant_unique
  · apply PiLp.ext; intro i; rw [vacuum,basis_act]; rw [cc_apply,show quant A i ∅=(vacuum n).ofLp i from (basis_act ..|>.symm).trans (by rw [show acts (quant A) (basisKet ∅)=vacuum n from quant_vac A]), basis_apply]; by_cases e:i=∅ <;> simp [vacuum,e]
  intro i; nth_rw 1 [← light_put i]; rw [←cc_mul,quant_put,cc_mul]; congr 1; unfold create; ext x y; change cc (∑ j,(acts _ _).ofLp j • put j) x y=(∑ j,(acts _ _).ofLp j • put j) x y; simp_rw [cc_apply,Matrix.sum_apply,basis_act, Matrix.smul_apply, smul_eq_mul,star_sum,star_mul']; exact sum_congr rfl (fun j _=> by rw [show star (put j x y)=put j x y from Matrix.ext_iff.mpr (light_put j) x y]; rfl)
lemma flip_at (A : Op n) (s t : Finset n) : quant Aᵀ s t=quant A t s := by
  have he : cc (star A)=Aᵀ := by rw [cc,star_star]
  rw [←he,quant_clear, quant_star,cc,star_star, Matrix.transpose_apply]
-- Ch Use embedded endocreator operates column only
lemma yellow (S : Finset n) : Plain ((η n).tag S) := by
  induction S using Finset.induction_on with
  | empty=> rw [Poly.tag_void]; exact Absorb.one
  | insert i S p ih=> rw [Poly.tag_any _ _ _ p]; exact ((Absorb.blade (mem_univ (true,i))).times ih).scale _
def loom (A : Op n) : Poly n n := ⟨fun i=>create (acts A (basisKet i)), fun _ _=> car_create ..⟩
lemma loom_piece (A : Op n) (S : Finset n) : Plain ((loom A).tag S) := by
  induction S using Finset.induction_on with
  | empty=> rw [Poly.tag_void]; exact Absorb.one
  | insert i S p ih=>
    rw [Poly.tag_any _ _ _ p]; have he : Plain ((loom A).term i) := Absorb.lot (univ:Finset n) _ (fun i _=> (Absorb.blade (mem_univ i)).scale _); exact (he.times ih).scale _
lemma padQ (A : Op n) (s t:Finset n) : crumb ((loom A).tag s) t= quant A t s := (basis_act _ t ∅).symm
lemma transcribe (s : Finset n) (A : Op n) (t : Finset n) : (tube s A).eval ((η n).tag t)=(η n).eval ((loom (cutM s*Aᵀ)).tag t) := by
  let T:=cutM s*Aᵀ; let F:=η n; let H:=tube s A; let Q:=loom T
  have he i : H.eval (col i)=F.eval (Q.term i) := by
    rw [show H.eval (col i)=tote s A i from tube_eta ..]; change _=F.eval (create (acts T (basisKet i))); rw [create_def,map_sum]; simp_rw [map_smul,basis_act,eval_blade]
    unfold tote; rw [←sum_subset (subset_univ s)]; swap; exact fun j h k=> by simp [T,cutM,k,Matrix.diagonal_mul]
    apply sum_congr rfl; intro j k; rw [show T j i=A i j from by simp [T,cutM,Matrix.diagonal_mul,k]]
  change H.eval _=F.eval (Q.tag t); induction t using Finset.induction_on with
  | empty=> rw [Poly.tag_void,Poly.tag_void,H.eval_one,F.eval_one]
  | insert i t p ih=>
    rw [Poly.tag_any _ _ _ p,Poly.tag_any Q _ _ p,map_smul,map_smul]; congr 1
    change H.eval (col i * F.tag t)= F.eval (Q.term i * Q.tag t); rw [Absorb.eval (show Plain (col i) from Absorb.blade (mem_univ (true,i))) (yellow _) H,Absorb.eval (show Plain (Q.term i) from (Poly.tag_once Q i) ▸ loom_piece T ({i}:Finset n)) (loom_piece T t) F,he,ih]
lemma finalF (S t x s : Finset n) (A : Op n) : zap S t ((tube t A).eval (monu x s))= if S=x then quant A s t else 0 := by
  let F := tube t A; let V:=loom (cutM t*Aᵀ); let U := cutM t*Aᵀ
  have he : F.eval (monu x s)=∑ i:Finset n, quant U i s • monu x i := by
    rw [monu,map_smul,Absorb.eval (thetaB _) (yellow _) F, show F.eval ((θ n).tag x)= _ from theta_inv .., show F.eval ((η n).tag s)= (η n).eval (V.tag s) from transcribe .., (Absorb.full (loom_piece U s)),map_sum]; simp_rw [map_smul,Poly.eval_oneT]; rw [mul_sum,smul_sum]; refine sum_congr rfl ?_; intro i _
    rw [show crumb _ _=quant U i s from padQ U s i]; rw [Algebra.mul_smul_comm]; by_cases g:i.card=s.card
    · unfold monu; rw [g,smul_comm]
    rw [quant_grade _ i s g,zero_smul,smul_zero,zero_smul]
  change zap _ _ (F.eval _)=_; rw [he,zap_sum]; simp_rw [zap_s, zap_one]; by_cases p:S=x
  · subst x; rw [sum_eq_single_of_mem _ (mem_univ t), if_pos rfl,if_pos rfl,mul_one]; unfold U; rw [quant_mul,quantCut,cutM, Matrix.diagonal_mul, if_pos (by simp),one_mul,flip_at] -- wrong h; use quant_cut
    intro i _ h; simp [h.symm]
  rw [if_neg p]; apply sum_eq_zero; intro i _; simp [p]
lemma zach {S t : Finset n} (A : Op n) {P : EF n} (h : Plain P) : zap S t ((tube t A).eval P)=∑ i, zap S i P * quant A i t := by
  nth_rw 1 [absorb_monu h]; simp_rw [map_sum,zap_sum,map_smul,zap_s]; rw [sum_comm]; apply sum_congr rfl; intro i _; simp [finalF,mul_ite] -- tune maps order
end YM.CF.Reed

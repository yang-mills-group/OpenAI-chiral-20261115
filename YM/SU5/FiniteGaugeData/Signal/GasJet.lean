import YM.SU5.FiniteGaugeData.Signal.Furnace
import YM.CF.Graph.Mars
/-! Actual ket estimate for each representative lamp. Use enhanced height purchased before
sufficient large N stage prices. Don't truncate powers of Grassmann with no budget. -/
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal.Furnace
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Scree Pastry
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
open Phase Spire
variable {n:Type*}[LinearOrder n][Fintype n]
variable {P X:Op n}(h:IsStarProjection P){H R c:ℝ}(p:0<H)
local notation "W"=> quant (upstairs P H)
local notation "V"=> quant (downstairs P H)
local notation "T"=> exp (dg X)
include h p
lemma self_r : W*V=1:= by rw [←quant_mul,street h p,quant_one]
lemma self_p : V*W=1:=mul_eq_one_comm.mp (self_r h p)

section alg
local instance : NormedAlgebra ℚ (FC n):= NormedAlgebra.restrictScalars ℚ ℝ _
/-- work at the same Fock space, but weight relative to occupied proj P. -/
def glare : FC n→ₐ[ℂ]FC n where
 toFun f:= W*f*V
 map_one' := by rw [mul_one,self_r h p]
 map_zero':= by simp
 map_add' x y:= by rw [mul_add,add_mul]
 map_mul' x y:= by rw [show W*x*V*(W*y*V)=W*(x*(V*W)*y)*V by simp only [mul_assoc],self_p h p,mul_one]
 commutes' c:= by simp_rw [Algebra.algebraMap_eq_smul_one, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,mul_one,self_r h p]
local notation "Q"=> glare h p
lemma glare_hit (x:FC n) : Q x* W=W*x:=by change W*x*V*W=W*x; rw [mul_assoc _ V,self_p h p,mul_one]
lemma glare_eq (x y:FC n)(a:y*W=W*x): Q x=y:=by rw [show Q x=W*x*V from rfl,←a,mul_assoc,self_r h p,mul_one]
lemma lure (v:Ket n): Q (create v)=create (acts (upstairs P H) v):= glare_eq h p _ _ (quant_create ..).symm
lemma rally (v: Ket n): Q (remove v)=remove (acts (downstairs P H) v):= glare_eq h p _ _ (by rw [quant_ann,staled h,←act_mul, street h p,act_one])
lemma light (i: LeanV n): Q (drawT P i)= (H:ℂ) • drawT P i:=by
  rcases i with ⟨_|_,i⟩
  · change Q (hideF P i)= (H:ℂ) • hideF P i; rw [hideF,prong_t,rally h p,←act_mul,rento h,act_smul]; simp [remove]
  change Q (seekF P i)= (H:ℂ) • seekF P i; rw [seekF,prong_p,lure h p,←act_mul,permit h,act_smul,map_smul]

variable (f: ribbon n)
omit p in
lemma rent (q:TagG P X): Commute T (tank P f):=by
  unfold tank; apply Commute.sum_right; intro i _; apply Commute.smul_right -- inspect
  refine (Commute.list_prod_right _ _ ?_); intro a v; obtain ⟨j,hj,rfl⟩:= List.mem_map.mp v; cases j with| mk b k=> cases b; exact Proa.moves _ _ h q (true,k); exact Proa.moves _ _ h q (false,k)
variable [Nonempty n]
lemma flash (r:ribbon n)(x: H ≤ R): ‖Q (tank P r)‖ ≤ tier R r.val:=by
 simp only [tank,map_sum]; refine (norm_sum_le ..).trans (sum_le_sum fun i _=>?_)
 rw [map_smul Q,norm_smul,mul_comm (‖crumb _ _‖)]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
 have he (L:List (LeanV n)) : ‖((L.map (fun i=>Q (drawT P i))).prod)‖ ≤ R^L.length:=by
    induction L with
    | nil=> simp
    | cons j l ih=> simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ']; have he: ‖Q (drawT P j)‖ ≤ R:= by rw [light h p,norm_smul,(show ‖(H:ℂ)‖=H from by simp [Real.norm_of_nonneg p.le])]; exact (mul_le_of_le_one_right p.le (Graph.vital P h j)).trans x
                    exact (norm_mul_le ..).trans (mul_le_mul he ih (norm_nonneg _) (p.le.trans x))
 unfold Scree.column; rw [map_list_prod,List.map_map]; convert he _ using 1 <;> first|rfl|rw [length_sort]

lemma beam (f b: ribbon n) (x:H ≤ R) : ‖Q (tank P ((exp f)*b))‖ ≤ Real.exp (tier R f.val)*tier R b.val := by
 rw [Graph.shape P f b h,map_mul,map_exp Q (Q).toLinearMap.continuous_of_finiteDimensional]
 exact (norm_mul_le ..).trans (mul_le_mul ((Graph.bootC _).trans (Real.exp_le_exp.mpr (flash h p f x))) (flash h p b x) (norm_nonneg _) (Real.exp_pos _).le)
end alg

variable (q: TagG P X)
local notation "U"=> quant (1-X)
-- a price that is composable!
def transformed (P X:Op n)(H:ℝ)(x:FC n):= quant (upstairs P H)*quant (1-X)*x*exp (dg X)*quant (downstairs P H)
local notation "J"=> transformed P X H
include q
omit h p in
-- repair
lemma starts : T*U=1:=by rw [tallied _ q.nil, ←quant_mul, mul_sub, mul_one, add_mul, one_mul, q.nil, add_zero, add_sub_cancel_right,quant_one]
include q
private lemma glossary : J 1=1:=by unfold transformed; rw [mul_one, mul_assoc _ U, mul_eq_one_comm.mp (starts q), mul_one,self_r h p]
lemma glossary_mul (x y:FC n): J (x*y)=J x*J y:=by
 unfold transformed; have he:T*(V*W)*U=1:= by rw [self_p h p,mul_one,starts q]
 conv_rhs =>
    rw [show W*U*x*T*V*(W*U*y*T*V) = W*U*(x*(T*(V*W)*U)*y)*T*V by noncomm_ring,he,mul_one]
lemma word_b {I:Type*} (A:I→ FC n)(L:List I) : J ((L.map A).prod)= (L.map (J∘A)).prod:=by -- p shadow
 induction L with
 | nil=> exact glossary h p q -- includes 2 p?
 | cons i l ih=> simp only [List.map_cons,List.prod_cons, glossary_mul h p q,ih,comp_apply]
lemma steam (x:FC n): T*V* J x=x*T*V:= by
 unfold transformed; have he:T*(V*W)*U=1:= by rw [self_p h p,mul_one,starts q];
 calc _ = T*(V*W)*U*x*T*V:= by noncomm_ring
      _ = _:= by rw [he]; simp
lemma press_C (v:Ket n): J (create v)=create (acts ((upstairs P H)*(1-X)) v):=by
 unfold transformed; rw [← quant_mul,quant_create,mul_assoc _ _ T]; have he:= starts q; rw [quant_mul,mul_assoc _ U, mul_eq_one_comm.mp he, mul_one,mul_assoc,self_r h p,mul_one]
lemma press_D (v: Ket n): J (remove v)=remove (acts ((downstairs P H)*(1+star X)) v) := by
 unfold transformed; rw [tallied X q.nil, mul_assoc _ _ V,mul_assoc (W*U) (remove v),←quant_mul (1+X),quant_ann]; have he:= starts q; rw [tallied _ q.nil] at he; rw [quant_mul,mul_assoc _ U,←mul_assoc U, ←mul_assoc U, mul_eq_one_comm.mp he,one_mul,←mul_assoc W, self_r h p,one_mul,star_mul, staled h,star_add,star_one] -- tune

variable [Nonempty n]
-- number of operators varying; per-letter badness. board still includes any outside-support pressure.
theorem spotlight {Ψ:Wave n}(v:Sea P Ψ)(b:1 ≤ H)(x:H ≤ R)(f z:ribbon n) {I:Type*}(A:I→FC n)(L:List I)(t:∀ i∈L, ‖J (A i)‖≤ c)(d:0≤c):
    ‖acts ((L.map A).prod*tank P (exp f*z)*T) Ψ‖ ≤ ‖T‖*Real.exp (tier R f.val)*tier R z.val*c^L.length:=by
 let B:=tank P (exp f*z); let W':=glare h p B; let O:=(L.map A).prod; have hJ (L:List I)(t:∀ i∈L,‖J (A i)‖≤ c) : ‖J ((L.map A).prod)‖≤ c^L.length:=by
    induction L with
    | nil=> simp [glossary h p q]
    | cons i l ih=> simp only [List.map_cons,List.prod_cons, List.length_cons,pow_succ', glossary_mul h p q]; exact (norm_mul_le ..).trans (mul_le_mul (t i List.mem_cons_self) (ih (fun i u=> t i (List.mem_cons_of_mem _ u))) (norm_nonneg _) d)
 obtain ⟨C,a,r,g⟩:= claim h b v
 have he:T*V* J O* W'* W=O*B*T:=by
    change T*V* J O* glare h p B* W=O*B*T; rw [steam h p q, mul_assoc (O*T*V),glare_hit h p,show O*T*V*(W*B)=O*(T*(V*W)*B) by simp only [mul_assoc],self_p h p,mul_one, (rent h (exp f*z) q).eq, mul_assoc]
 change ‖acts (O*B*T) Ψ‖≤_; rw [←he]; simp only [act_mul,r,map_smul]; rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg a.le]
 have hb: ‖glare h p B‖≤ Real.exp (tier R f.val)*tier R z.val:= beam h p f z x; let tF:= Real.exp (tier R f.val)*tier R z.val; let cV:=c^L.length; have hv:‖acts (J O) (acts W' Ψ)‖≤ cV*tF := (Graph.spentS n (J O) _).trans (mul_le_mul (hJ L t) ((Graph.spentS n W' Ψ).trans (by rw [v.2,mul_one]; exact hb)) (norm_nonneg _) (pow_nonneg d _))
 have hf :‖acts T (acts V (acts (J O) (acts W' Ψ)))‖≤ ‖T‖*(C*(cV*tF)):= (Graph.spentS n T _).trans (mul_le_mul_of_nonneg_left ((Graph.spentS n V _).trans (mul_le_mul g hv (norm_nonneg _) a.le)) (norm_nonneg _))
 exact (mul_le_mul_of_nonneg_left hf (inv_pos.mpr a).le).trans_eq (by unfold cV tF; field_simp <;> ring)
end YM.CF.Signal.Furnace
#print axioms YM.CF.Signal.Furnace.spotlight

import YM.CF.Haro.Power
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
open Branch Laic
open Skye Precision
open Jet Scree
variable{n:Side}(F:Op (Single n))(h:AxisB F)
abbrev Monos(F:Op (Single n)):Prop:=∀ i:Cover,∀ g:SU.E,Commute (tapH F i) (KinX g)
def heroP(F:Op (Single n))(p:Momentum):Pal:= ∑ i∈ porchY n, mode p i • loft F i
include h
private lemma step_q(s: Signed)(J:Cover→ Op (SpinIdx ×Slot)): ∑ i∈ porchY n,J i= ∑ i∈ porchY n,J (s.act i):=by -- no F
 let T:=porchY n; nth_rw 1 [show porchY n=(porchY n).image s.act from ?_]; rw [sum_image s.act_injective.injOn]
 ext i; obtain ⟨i,rfl⟩:= (s.actEquiv (R:=ℤ)).surjective i; change s.act i∈ T↔ _; unfold T; rw [loft_g, mem_image]; exact ⟨fun h=>⟨i,h,rfl⟩,fun ⟨j,h,t⟩=> (s.act_injective t) ▸ h⟩
private lemma modeH (x:Cover)(p: Momentum)(h:p∈baseCube): mode p (-x)=star (mode p x):=by
 have hu:=form p flipL false h.1 x; rw [flip_p,show cadence flipL false p=-p from ?_] at hu; swap; · funext i; simp [cadence, Signed.act]
 rw [mode_negate p h.1 (-x)] at hu; change star _=mode p x at hu; rw [←hu,star_star]
lemma issue_p (k: Monos F): AxisP (heroP F):=by
 refine ⟨fun s b U hv p0 hx=>?_,fun i p u=>?_,fun i=>?_⟩
 · let W(p:Momentum)(x:Cover):=mode p x • loft F x; let v:=detX s; change sings b (twoU U b) (∑ x∈ porchY n,W (cadence s b p0) x) = Thera.jazz v _; rw [step_q F h s,singT,win_sum,map_sum]; simp_rw [← singT]
   have ht(x:Cover): sings b (twoU U b) (W (cadence s b p0) (s.act x))=if detX s then -star (W p0 (-x)) else W p0 x:=by
      unfold W; rw [singT,win_c, twist_scalar,← singT, price_p F h x s b U hv, Scroll.form _ _ _ hx.1]
      have hl : cSignX b (cSignX b (mode p0 x))=mode p0 x:=by rw [sign_seq]; cases b<;>rfl
      rw [hl]; cases hz:detX s; simp
      rw [show mode p0 (-x)=_ from modeH F h _ p0 hx]; simp only [star_smul, star_star,ite_true,smul_neg]
   simp_rw [ht]; unfold v; cases w:detX s
   · simp only [Bool.false_eq_true,ite_false]; rfl
   change _= -star (∑ x∈ porchY n,W p0 x)
   conv_rhs=> rw [step_q F h flipL]
   simp only [flip_p,star_sum,ite_true,sum_neg_distrib]
 · unfold heroP Commute SemiconjBy; rw [Matrix.sum_mul,Matrix.mul_sum]; apply sum_congr rfl; intro j y; rw [loft,if_pos y,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_smul]; exact congrArg _ (congrArg _ ((k j i).eq))
 unfold heroP; apply DifferentiableAt.fun_sum; intro j _; unfold Laurent.mode Tap.bout; fun_prop
omit h
lemma ladL: Reads (loft F) (heroP F):=by
 let Y:= porchY n; have hp (x:Cover)(p:x∉ Y):loft F x=0:=if_neg p
 refine ⟨fun x y=> summable_of_ne_finset_zero (s:=Y) fun i p=>?_, fun p u i j=>?_ ⟩
 · simp [hp _ p]
 unfold heroP; rw [Matrix.sum_apply]; simp_rw [Matrix.smul_apply]; unfold Laurent.read; exact tsum_eq_sum (fun x hx=>by change mode p x • loft F x i j=0; rw [hp _ hx]; simp)
end YM.CF.Haro

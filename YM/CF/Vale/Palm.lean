import YM.CF.Vale.Wing
import YM.CF.Siete.Cloud
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef Hom PhysicalNext.JointLoad.Heir
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {K:Teller group}{P:RG.Patch}{R:ChartRatio group}{W:Postal}{η e:ℝ}{n k v:ℕ}{f g a b d:ℝ}{B m c u:Side}{C:Credit}
lemma Gold.seamL(A: Gold K P R W)(i:ℕ)(p:u.val=c.val*P.L.val):Seam (A.mint i p) K.η K.C:=by
 let X:=A.roof i; let Y:= A.roof (i+1); have hh:=A.deed i; have he:=(hh.pay.2.2.2 [] (by simp)).2
 exact ⟨he, A.H i,A.H (i+1),hh.link (A.sized i p),mul_eq_one_comm.mp (X.2.1 _).diagonalInv, X.1.2.2.2.2,Y.1.1⟩
variable {U: Pricing K.j P.L P.odd_side (Thread K.j)} {D:Grasp U B e}
-- clocks IR to UV
variable (L:Side)
def billX:ℝ:= group.slopeConstant*Real.log L.val
def billC:ℝ:= spiceM*Real.log L.val
def net:=billX L-billC L
def hat(b:ℝ)(i:ℕ):= b+i*billX L
lemma hat_succ(x:ℝ)(i:ℕ):hat L x (i+1)=betaF group (hat L x i) L:=by unfold hat betaF billX; push_cast; ring
lemma pitch:0≤billX L:= mul_nonneg (Gauge.slopeConstant_pos yet_one).le (Real.log_nonneg (by exact_mod_cast (L.property))) -- adjust
lemma crown(x:ℝ)(i:ℕ):x≤hat L x i:= le_add_of_nonneg_right (mul_nonneg (by positivity) (pitch L))
lemma mastK(L: Side) :∀ᶠ x in atTop,∀i:ℕ, radiusB (hat L x i) ≤ 2*radiusB (hat L x (i-1)):=by
 have hx : ∀ᶠ x:ℝ in atTop,radiusB (x+billX L)≤2*radiusB x:= ?_
 · obtain ⟨A,hA⟩:= eventually_atTop.mp hx; filter_upwards [eventually_ge_atTop A] with y hy i; cases i with| zero=> simp; omega| succ i=> exact hA _ (hy.trans (crown L y i))|>.trans' (by rw [hat_succ]; simp [billX,betaF]) -- tune sub
 exact (Extra.Iteration.Rebuild.geometry (billX L)).mono fun i g=>g.1.1
lemma fates(n s:ℕ)(p:6 ≤ n)(v:2 ≤ s)(L:Side):∀ᶠ x in atTop,∀ (w:ℝ),0<w→ ∃ A:ℕ→RG.BudgetPoint, (∀ i,(A i).threshold=temp (hat L x i)∧(A i).power=s∧(A i).order=n∧(A i).B=radiusB (hat L x i)∧(A i).supportExponent=w)∧∀ i, Siete.Find (A i) (A (i+1)) n s (hat L x i) L:=by
 have he:= Work.E09.radiusB_temp 0; have hx: Tendsto temp atTop (𝓝 0):=by simpa using he
 obtain ⟨B,hB⟩:= eventually_atTop.mp ((Work.E01.radiusB_tendsto.eventually_gt_atTop 0).and (hx.eventually (ge_mem_nhds (by norm_num : (0:ℝ)< 1)))) -- tune arg name
 filter_upwards [eventually_ge_atTop B, eventually_gt_atTop (0:ℝ),mastK L] with x h h' hk w hw
 let A(i):RG.BudgetPoint:=⟨s,n,w,radiusB (hat L x i),temp (hat L x i),v,p, hw,(hB _ (h.trans (crown L x i))).1,Work.E09.temp_pos (h'.trans_le (crown L x i)),(hB _ (h.trans (crown L x i))).2⟩ -- tune ≤
 refine ⟨A,fun i=>⟨rfl,rfl,rfl,rfl,rfl⟩,fun i=>⟨rfl,?_,rfl,rfl,hk (i+1),rfl,le_rfl⟩⟩
 change temp _= temp _; rw [hat_succ]
lemma bulk_size(x:ℝ)(z n:ℕ)(p:2≤P.L.val)(h:∀ i,radiusB (hat P.L x i) ≤2*radiusB (hat P.L x (i-1)))(v:z*(1+radiusB (hat P.L x 0)) ≤ m.val): z*(1+radiusB (hat P.L x n)) ≤ (cell m B P.L n).val:=by
 induction n with
 | zero=> exact v.trans (amplit ..)
 | succ n ih=> rw [grows]; change _ ≤ _ * P.L.val; apply (Nat.mul_le_mul ih p).trans'; rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left z (by have he: radiusB (hat P.L x (n+1)) ≤2*radiusB (hat P.L x n):= h _; omega)
end YM.CF.Vale

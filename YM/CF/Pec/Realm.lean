import YM.CF.Pec.Daub
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}
def gloss(a: Cloud n)(i:Axis)(x:Orig n):=collect group a (x,i)
def bookJ(a:Cloud n)(i:Axis)(x:Orig n):= (1/2:ℝ) • (gloss a i x+gloss a i (x-step i))
def whale(a:Cloud n)(x: Orig n): Hue group.Color:=centaur (bookJ a) x
lemma worth (a:Cloud n)(p: PlaqAxes)(x:Orig n):let F(y):=heat x (collect group a) (Sum.inl (y,p)); let i:=p.val.1; let j:=p.val.2
 whale a x i j = (1/4:ℝ) • (F x+F (x-step i)+F (x-step j)+ F (x-step i-step j)):=by
 intro f i j; let A:= gloss a i; let B:=gloss a j
 have ht(y):f y=B (y+step i)- B y - (A (y+step j)-A y):=by
    simp only [f,Font.heat]; rw [fundamental]; ext k; exact d_plaquettes _ _ (parts _ 1 a k)
 rw [ht,ht,ht,ht]; unfold whale centaur central bookJ
 change (1/2:ℝ) • ((1/2:ℝ) • (B _+B _)-(1/2:ℝ) • (B _+B _))-(1/2:ℝ) • ((1/2:ℝ) • (A _+ A _)-(1/2:ℝ) • (A _+A _))=_
 have he:x+step i-step j=x-step j+step i:=by abel
 have hf:x+step j-step i=x-step i+step j:=by abel
 simp only [he,hf,sub_add_cancel]; rw [show x-step i-step j+step i=x-step j by abel,show x-step j-step i=x-step i-step j by abel]; simp only [smul_add,smul_sub,smul_smul]; ring_nf; abel -- tune
lemma pos_act(s:Signed)(i:Axis)(h:s.flip i=false)(x:Orig n): s.act (x+step i)=s.act x+step (s.perm i):=by simpa [affine] using RG.StepData.possite s 0 x i h
lemma neg_act(s:Signed)(i:Axis)(h:s.flip i=true)(x:Orig n): s.act (x+step i)=s.act x-step (s.perm i):=by simpa [affine] using RG.StepData.negsite s 0 x i h
lemma edge_p(s:Signed)(x:Orig n)(a:Cloud n)(i:Axis): bookJ (litX s a) i x= dye s i • bookJ a (s.perm i) (s.act x):=by
 unfold bookJ dye gloss collect litX Bid.pulled; simp only [show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply _]; cases h:s.flip i
 · have hv : s.act (x-step i)=s.act x-step (s.perm i):=eq_sub_of_add_eq (by rw [←pos_act s i h,sub_add_cancel]); simp [Step.used, Step.rotate,posDir,h,hv,affine]
 have ht := neg_act s i h (x-step i); rw [sub_add_cancel] at ht; have hv := sub_eq_iff_eq_add.mp ht.symm; simp only [Step.used,Step.rotate, posDir,h, ↓reduceIte,Bool.false_xor,Bool.xor_false, affine,add_zero]; rw [←ht]; simp; abel -- tune
lemma helm(s:Signed)(x:Orig n)(a:Cloud n)(i j:Axis): central i (bookJ (litX s a) j) x= (dye s i*dye s j) • central (s.perm i) (bookJ a (s.perm j)) (s.act x):=by
 unfold central; rw [edge_p,edge_p,←smul_sub,smul_comm _ (dye s j)]; cases h:s.flip i
 · have hv : s.act (x-step i)=s.act x-step (s.perm i):=eq_sub_of_add_eq (by rw [←pos_act s i h,sub_add_cancel]); rw [pos_act s i h,hv,show dye s i=1 from if_neg (by simp [h]),one_mul]
 have ht : s.act (x-step i)=s.act x+step (s.perm i):=sub_eq_iff_eq_add.mp (by rw [←neg_act s i h,sub_add_cancel]); rw [neg_act s i h,ht, ← neg_sub (bookJ a (s.perm j) (s.act x + step (s.perm i))) _,show dye s i= -1 from if_pos h]; simp only [smul_neg,neg_mul,one_mul,neg_smul] -- tune
lemma cluster(s:Signed)(x:Orig n)(a:Cloud n):whale (litX s a) x=skew s (whale a (s.act x)):=by
 funext i j; unfold whale centaur skew; dsimp only; rw [helm s x a i j,helm s x a j i, smul_sub,mul_comm (dye s i)] -- tune
-- projections total
lemma hum_pay(P:Case)(U:Cloud n): let S:=∑ i:Orig n, hum P (whale U i) (whale U i); S=(↑(priceC P* ∑ i:Orig n,∑ k:PlaqAxes,‖whale U i k.val.1 k.val.2‖^2):ℂ) :=by
 intro S; apply Complex.ext; · unfold S; rw [Complex.re_sum,Complex.ofReal_re,Finset.mul_sum]; apply sum_congr rfl; intro i _; exact roots_r _ _ (centaur_anti _ i)
 unfold S; rw [Complex.im_sum,Complex.ofReal_im]; exact plume P (bookJ U)
end YM.CF.Pec

import YM.CF.Nacre.Sift
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nacre
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m:ℕ}{n:Side}
def foil(a: Signed)(f:Bkg (More n)→ Op (Single n))(U:Bkg (More n)):=ZoneH (incX a) (f (Yg (incX a⁻¹) U))
def sumU (f:Bkg (More n)→Op (Single n))(U:Bkg (More n)):=(↑(Fintype.card Signed):ℝ)⁻¹ • ∑ a:Signed, foil a f U
lemma hail_tx (a: Signed)(f:Bkg (More n)→ Op (Single n))(U:Bkg (More n)):sumU f (Yg (incX a) U)=ZoneH (incX a) (sumU f U):=by
 unfold sumU; rw [map_smul,map_sum,← Equiv.sum_comp (Equiv.mulRight a)]; congr 1; apply sum_congr rfl; intro i _; unfold foil; rw [zno, ←kor, wink,wink]; change ZoneH (incX (i*a)) (f (Yg (incX (a*(i*a)⁻¹)) U))= _; rw [_root_.mul_inv_rev, ←mul_assoc,mul_inv_cancel,one_mul]
lemma rent_tx (a:Cover)(f:Bkg (More n)→Op (Single n))(h:Across f)(U:Bkg (More n)):sumU f (Yg (lagX a) U)=ZoneH (lagX a) (sumU f U):=by
 unfold sumU; rw [map_smul,map_sum]; congr 1; apply sum_congr rfl; intro i _; unfold foil; rw [←kor]; let t:=i.act a; rw [show joinX (lagX a) (incX i⁻¹)= joinX (incX i⁻¹) (lagX t) by unfold joinX lagX incX t; simp,kor,h,zno,zno]; congr 1; unfold joinX lagX incX t; -- tune twist inverse rotation formula wrong
 simp
lemma symmetry (a:Shape)(f:Bkg (More n)→Op (Single n))(h:Across f)(U:Bkg (More n)):sumU f (Yg a U)=ZoneH a (sumU f U):=by
 nth_rw 1 [show a=joinX (lagX a.t) (incX a.s) from (vines ..).symm]; rw [kor,hail_tx,rent_tx _ _ h,zno,vines]
def ripeF (F:Bkg (More n)→Op (Single n)):Prop:=∀ (U:Bkg (More n))(t), F (Lattice.gauge t U)=twist (tradew n t) (F U)
lemma troop (f:Bkg (More n)→Op (Single n))(h:ripeF f):ripeF (sumU f):=by
 intro U t; unfold sumU; rw [map_smul,map_sum]; congr 1; apply sum_congr rfl; intro i _; unfold foil; rw [van,h,GaugeT]; have hv: (t ∘ (incX i⁻¹).anon n) ∘ (incX i).anon n=t:=by
    funext x; obtain ⟨x,rfl⟩:∃ y,wrap _ y=x:=⟨natural x,nat_true _⟩; unfold comp; rw [Shape.anno,Shape.anno,←palm,wink,inv_mul_cancel]; unfold Shape.motion incX; simp
 rw [hv]
lemma toneP(P: Toy m n)(V:Cloud n→Bkg (More n))(x:Cloud n)(H:∀ e: Edge (FiX n),ContDiffAt ℝ ω (fun t=>group.mat (V t e)) x): ContDiffAt ℝ ω (sumU (cavil P) ∘ V) x:=by
 refine ContDiffAt.const_smul ((↑(Fintype.card Signed):ℝ)⁻¹) (ContDiffAt.sum (s:=univ) (f:=fun i t=> foil i (cavil P) (V t)) (n:=ω) ?_); intro i _; apply (ZoneH (incX i)).contDiff.contDiffAt.comp x (cantor x P _ ?_); intro e; change ContDiffAt ℝ ω (fun y=>group.mat (Yg (incX _) _ _)) x; simp_rw [Ywin]; unfold Lattice.pull Step.read; split
 · simp_rw [group.mat_inv]; exact (starL ℝ : group.Mat≃L[ℝ] group.Mat).contDiff.contDiffAt.comp x (H _)
 exact H _
def litX (a:Signed)(V:Cloud n):Cloud n:=Bid.pulled V a
def spurTx(P:Toy m n)(V:Cloud n):=(↑(Fintype.card Signed):ℝ)⁻¹ • ∑ a:Signed, ZoneH (incX a) (pyre P (litX a⁻¹ V))
lemma roomy(i:Signed)(V:Cloud n)(t:ℝ): Yg (incX i) (represent (t • V))=represent (t • litX i V):=by rw [Ywin,Work.F03.represent_pulled]; rfl
lemma priced(x:Cloud n)(P:Toy m n): Tendsto (fun t:ℝ=> (t^m)⁻¹ • sumU (cavil P) (represent (t • x))) (𝓝[≠] 0) (𝓝 (spurTx P x)):=by
 let f(a:Signed)(t:ℝ):= (t^m)⁻¹ • foil a (cavil P) (represent (t • x)); have hp(a:Signed): Tendsto (f a) (𝓝[≠] 0) (𝓝 (ZoneH (incX a) (pyre P (litX a⁻¹ x)))):=by unfold f foil; simp_rw [roomy,←map_smul]; exact ((ZoneH (n:=n) (incX a)).continuous.tendsto _).comp (peak_e ..)
 refine (tendsto_finsetSum _ (f:=f) (fun a _=>hp a)).const_smul ((↑(Fintype.card Signed):ℝ)⁻¹) |>.congr ?_; intro i; unfold f sumU; rw [smul_comm]; simp only [Finset.smul_sum]
end YM.CF.Nacre

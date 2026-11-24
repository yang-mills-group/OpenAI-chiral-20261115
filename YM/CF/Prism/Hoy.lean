import YM.CF.Prism.Pecu
set_option autoImplicit false
noncomputable section
namespace YM.CF.Prism
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset SU Fock Lat Spire Scroll MeasureTheory Skye Scree Cube RG PhysicalNext.JointLoad Next.Foundations
open MultiNext.SignedSource Lyre Banjo Analysis Push.Local AnalyticBridge.VerifiedReset
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.Frobenius
variable {n:Side}{a b r C d:ℝ}{k p j m:ℕ}{B:BudgetPoint}{X:Support (More n)}{o:Seat n}{F: Pane n→ℂ}{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma oracle (k:ℕ)(hp:2≤k)(u:ℝ)(p:1≤u): ∃ C:ℝ,1≤C∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{n:Side}(B: BudgetPoint)(X:Support (More n))(o:Seat n)(v:E→tangD n)(F:Pane n→ℂ)(c r:ℝ)(R:E→Prop)(x:E), Nonwrapping X o → k ≤ B.order → 4 ≤ (More n).val → Roman r u B X o F c → 0 ≤ r → r ≤ 1 → Proofs B X o v x R k u r → ContDiffAt ℝ k (F ∘ (increment 1 ∘ v)) x∧∀ m:ℕ,m ≤ k → ∀ l: Fin m → E, (∀ i,R (l i)) → ‖iteratedFDeriv ℝ m (F∘ (increment 1 ∘ v)) x l‖ ≤ C*r^2*c:=by
 obtain ⟨A,g,h⟩:= hoped k hp u p; obtain ⟨T,w,hT⟩:=Siete.factorial k; refine ⟨T*A,one_le_mul_of_one_le_of_one_le w g,@fun E _ _ n B X o v F c r R x z y q e f t l=>?_⟩
 have ht:pingS B.threshold X (increment 1 (v x)):=by simpa using l.sails 1 (by simp)
 have hz:Proofs B X o v x R k u r:=l; have hg : ContDiffAt ℝ (k:ℕ∞ω) (F ∘ increment 1) (v x):=(stirring (1:Pane n) (v x) e.depends c (e.track _ ht)).of_le (Nat.cast_le.mpr y)
 refine ⟨hg.comp x l.flow,fun m hv L hl=>?_⟩; let f0: Fin 0→E:=fun i=> Fin.elim0 i
 have hh : Promise 2 u r B o X (v x):=by simpa using l.grade 0 (by omega) f0 (fun i=>Fin.elim0 i)
 have he:0≤c:=(e.track _ ht).grade
 refine (advances k _ _ _ hg l.flow (h n X B o (v x) F c r z y q e hh f t l.mark l.sails) R (fun i _ h=> l.grade i h) m hv L hl).trans ?_
 rw [show T*A*r^2*c=T*(A*r^2*c) by ring]; exact mul_le_mul_of_nonneg_right (hT m hv) (by positivity)
open Heir Precision Push.Uniform 
-- absolute shift of color tests composed with germs from Fame
lemma stopF (b:Bool)(i l:SU.Slot)(n:ℕ) (hp:1 ≤ n):∃ K:ℝ,1 ≤ K ∧∀ {c f:Side}(a:Seat f)(Θ:tangD c→Seat f→ group.Color)(g:BudgetPoint)(t:Seat c) (ε:ℝ),g.order=n→ Guide _ (g.dirBound t) 0 Θ n ε → ε ≤ 1 → Signs g t (fun w=> aull b i l (-Θ w a)-aull b i l 0) (K*ε):=by
 let F(z:group.Color):=aull b i l (-z)
 have he : ContDiff ℝ ω F:= (curr b i l).comp contDiff_id.neg
 let T:=Metric.closedBall (0:group.Color) 1; let L:= F - fun _=> F 0
 obtain ⟨K,h,H⟩:= Push.Uniform.exists_allows (f:=L) (isCompact_closedBall _ 1) (fun _ _=> (he.sub contDiff_const).contDiffAt) n; let M:=K+1; have hp':1≤ M:=by linarith
 obtain ⟨C,v,hT⟩:= Siete.factorial n
 refine ⟨C*M, one_le_mul_of_one_le_of_one_le v hp', @fun c f a Θ g t ε hn p hg=>?_⟩
 let B:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Seat f=>group.Color) a; let z:=B ∘ Θ; have hz:Guide _ (g.dirBound t) 0 z n ε:=by refine ⟨B.contDiff.contDiffAt.comp 0 p.1,fun j h v hg=>?_⟩; rw [show z=B∘ Θ from rfl,B.iteratedFDeriv_comp_left p.1 (Nat.cast_le.mpr h)]; exact (norm_le_pi_norm (iteratedFDeriv ℝ j Θ 0 v) a).trans (p.2 _ h v hg)
 have hl:= hz.size; have hu:0≤ ε:= (norm_nonneg _).trans hl
 have hi: (L ∘ z)=fun w=> aull b i l (-Θ w a)-aull b i l 0:=funext fun w=> by change aull _ _ _ (-Θ w a) - aull b i l (- (0:group.Color))=_; rw [neg_zero]
 have he': z 0∈ T:= mem_closedBall_zero_iff.mpr (hl.trans hg); rw [←hi]
 have hx(z:group.Color)(g:z∈T):‖fderiv ℝ L z‖ ≤ K:=by rw [←norm_iteratedFDeriv_one]; exact (H z g).norm_le _ hp -- tune names
 refine ⟨by positivity,by rw [hn]; exact (((he.sub contDiff_const).of_le le_top).contDiffAt).comp _ hz.1,fun j p l q=>?_⟩; have hu': 0 ≤ K:=h; have hℓ:=p.trans_eq hn
 by_cases v0:j=0; subst j
 · rw [iteratedFDeriv_zero_apply,Function.comp_apply]; have hK:= convex_closedBall (E:=group.Color)  (0:group.Color) 1; have hh:= Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f:=L) (f':=fun x=> fderiv ℝ L x) (fun x _=> (((he.sub contDiff_const).differentiable (by simp) x).hasFDerivAt).hasFDerivWithinAt) hx hK (show (0:group.Color)∈ T from mem_closedBall_self zero_le_one) he'
   rw [show L 0=0 from sub_self _,sub_zero,sub_zero] at hh; apply hh.trans; gcongr; apply le_trans _ (le_mul_of_one_le_left (zero_le_one.trans hp') v); unfold M; linarith
 rw [iteratedFDeriv_comp (g:=L) (f:=z) (((he.sub contDiff_const).of_le le_top).contDiffAt) hz.1 (Nat.cast_le.mpr hℓ),FormalMultilinearSeries.taylorComp,_root_.sum_apply]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> K*ε) (fun iA pA=>?_ )).trans ?_)
 · let w(d:Fin iA.length):=iteratedFDeriv ℝ (iA.partSize d) z 0 (l ∘ iA.emb d); have hw:(∏ i,‖w i‖) ≤ ε^iA.length:= le_trans (prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> hz.2 _ ((iA.partSize_le j).trans hℓ) _ fun _=> q _)) (le_of_eq (by simp)); let A:=iteratedFDeriv ℝ iA.length L (z 0); change ‖A w‖ ≤ _; exact (A.le_opNorm w).trans (mul_le_mul ((H _ he').norm_le _ (iA.length_le.trans hℓ)) (hw.trans (pow_le_of_le_one hu hg (iA.length_pos (Nat.pos_of_ne_zero v0)).ne')) (prod_nonneg fun i _=>norm_nonneg _) hu')
 rw [sum_const,card_univ,nsmul_eq_mul,←mul_assoc]; gcongr; exact hT _ hℓ; unfold M; linarith
end YM.CF.Prism

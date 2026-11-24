import YM.SU5.FiniteGaugeData.ArchiveK.Petrichor
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
open MeasureTheory.Measure
namespace Midway
open LightK Violas
variable {c:ℝ}{S:Set Space3}(q w:ℕ){q' u v:ℕ} (D:ℕ)
local notation "T"=> Stamp q w
namespace GramK
variable {x:Type*} [MeasurableSpace x] {μ:Measure x} {X:Type*}[Fintype X][DecidableEq X](K:X→X→x→ℂ)(h:∀ i j,Integrable (K i j) μ)
def helm (p:x): Op X:= Matrix.of fun i j=> K i j p
def stageK (U:Set x): Op X:= Matrix.of fun i j=>∫ p in U,K i j p ∂μ
-- gas ⇂. row formula. rank-one dem.R.
omit h in
lemma grow (A:Op X)(x y:Ket X): inner ℂ x (ract A y)=∑ i:X,∑ j:X, A i j*(y j*star (x i)):=by rw [PiLp.inner_apply]; simp_rw [RCLike.inner_apply,R_at,Matrix.mulVec,dotProduct, Finset.sum_mul]; apply sum_congr rfl; intro i _; refine sum_congr rfl fun j _=> ?_ ; rw [mul_assoc]; rfl -- tune
variable (r:Set x)
include h
lemma money_I(x':Ket X) : Integrable (fun i=> gas (helm K i) x') μ:=by
 unfold gas; simp_rw [grow,helm,Matrix.of_apply,Complex.re_sum]; refine integrable_finsetSum _ (fun i _=>integrable_finsetSum _ fun j _=>?_); exact ((h i j).mul_const _).re
lemma receipt(x':Ket X): gas (stageK (μ:=μ) K r) x'=∫ i in r,gas (helm K i) x' ∂μ:=by
 unfold gas; simp_rw [grow, helm,Matrix.of_apply, Complex.re_sum]; let k(i j : X)(x_ : x):= (K i j x_* ((x' j)*star (x' i))).re; have he(i j): IntegrableOn (k i j) r μ:= ((h i j).mul_const _).re.integrableOn
 rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ fun j _=> he i j)]; apply sum_congr rfl; intro i _; rw [integral_finsetSum _ (fun j _=> he i j)]; refine sum_congr rfl fun j _=>?_ ; unfold stageK; rw [Matrix.of_apply,←integral_mul_const]; exact (integral_re ((h i j).integrableOn.mul_const _)).symm -- tune
-- sums b.Discount. rank-one playout.
omit h
lemma chordB (L:X→ℂ)(A:ℂ)(P:Op X)(h:∀ i j, P i j=A*(L i*star (L j)))(x:Ket X): gas P x=A.re*‖∑ i:X,x i*star (L i)‖^2 :=by
 unfold gas; rw [grow]; let v:=fun i:X=>x i*star (L i); let t:=∑ i,v i
 have hp:∑ i:X,∑ j:X,P i j*(x j*star (x i))=A*(star t*t):=by
    unfold t; simp_rw [star_sum, Finset.sum_mul, Finset.mul_sum]; apply sum_congr rfl; intro i _; refine sum_congr rfl fun j _=>?_ ; unfold v; rw [h,star_mul,star_star]; ring
 change (∑ i:X,∑ j:X,P i j*_).re=A.re*‖t‖^2; rw [hp,show star t*t= ((‖t‖^2:ℝ):ℂ) from ?_, Complex.re_mul_ofReal]; rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
end GramK
open GramK
local notation "τ"=> Largo.τ -- not needed
local notation "U"=> Helix D
local notation "Θ"=> hiveV D
abbrev tLab (i:Stamp q w)(p:Space3):= aim D (ground i.1) p -- Tang used across.
def boon (i j:Stamp q w)(x:Space3):ℂ:= if i.2=j.2 then tLab q w D i x * star (tLab q w D j x) else 0
local notation "F"=> boon q w D
@[fun_prop] lemma book_c (i j:Stamp q w) : Continuous (boon q w D i j):=by by_cases p:i.2=j.2 <;> unfold boon <;> simp only [p,↓reduceIte, tLab] <;> fun_prop
lemma book_h (u:0<D) (i j:Stamp q w) : Integrable (boon q w D i j) Θ:= by letI:=heist u; apply (integrable_const (μ:=hiveV D) (1:ℝ)).mono' ((book_c ..).aestronglyMeasurable); apply Eventually.of_forall; intro a; unfold boon; split<;> simp [norm_mul,tLab,aim_cash]
def bridgeW (Ut:Set Space3): Op (Stamp q w):=stageK (μ:=hiveV D) (boon q w D) Ut
lemma gem_univ(u:0<D)(i:Stamp q w) : ∫ p,boon q w D i i p∂(hiveV D)= ((lobby D:ℝ):ℂ):=by
 unfold boon; simp_rw [ if_true, tLab,aimed, sub_self, aim, songQ,Pi.zero_apply,Int.cast_zero, mul_zero]; change ∫ p,coastE (inner ℝ p (0:Space3))∂(hiveV D)= _; simp_rw [inner_zero_right,coast_zero]; rw [hiveV,setIntegral_const,gem_r u]; simp -- tune
lemma bridge_full(u:0<D): bridgeW q w D Set.univ=((lobby D:ℝ):ℂ) • (1:Op (Stamp q w)):=by
 apply Matrix.ext; intro i j; simp only [bridgeW,stageK, Matrix.of_apply,setIntegral_univ]; by_cases e:i=j; · subst j; rw [gem_univ q w D u, Matrix.smul_apply,Matrix.one_apply,if_pos rfl]; simp [smul_eq_mul]; -- tune
 rw [Matrix.smul_apply,Matrix.one_apply,if_neg e, smul_zero]; unfold boon; by_cases h:i.2=j.2; swap; · simp_rw [if_neg h]; simp
 simp_rw [if_pos h,tLab,aimed,aim_eq _ u,hiveV]; rw [song_a]; swap; · exact horn_p u
 rw [if_neg (fun v=> e (Prod.ext (ground_in (sub_eq_zero.mp v)) h))]
abbrev kNote (D q w:ℕ)(p:Space3)(z:Ket (Stamp q w))(v:Zpo w):= ∑ i:Pix q,z (i,v)*star (aim D (ground i) p)
lemma bridge_value(p:Space3)(x:Ket (Stamp q w)): gas (helm F p) x=∑ i:Zpo w,‖kNote D q w p x i‖^2:=by
 let f(v:Zpo w):Ket (Pix q):= WithLp.toLp 2 (fun i=> x (i,v)); let P(v:Zpo w):Op (Pix q):= Matrix.of fun i j=> aim D (ground i) p *star (aim D (ground j) p); let Q:=helm (boon q w D) p
 have hk(i:Zpo w): gas (P i) (f i)= ‖kNote D q w p x i‖^2:=by
    rw [chordB (fun i=>aim D (ground i) p) 1]; swap; · intro u v; rw [one_mul]; rfl
    rw [Complex.one_re,one_mul]; -- tune
 have he (i j:Pix q)(v l:Zpo w) : Q (i,v) (j,l)=if v=l then P v i j else 0:=rfl
 change gas Q x=_; simp_rw [←hk]; unfold gas; rw [GramK.grow,Complex.re_sum]; simp_rw [Stamp,Fintype.sum_prod_type]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [GramK.grow, Complex.re_sum]; apply sum_congr rfl; intro j _; simp_rw [he,ite_mul,zero_mul, Finset.sum_ite_eq, mem_univ,if_true]; rfl
lemma plank (u:0<D)(S:Set Space3)(p:MeasurableSet S) (x:Ket (Stamp q w)): 0 ≤ gas (bridgeW q w D S) x ∧ gas (bridgeW q w D S) x ≤ lobby D*‖x‖^2:=by
 let f(z):=gas (helm F z) x; have he:Integrable f Θ:= money_I F (book_h q w D u) x; have ht(z):0 ≤ f z:=by unfold f; rw [bridge_value]; positivity
 unfold bridgeW; rw [receipt F (book_h q w D u)]; refine ⟨integral_nonneg ht,?_⟩; apply le_trans (setIntegral_le_integral he (ae_of_all _ ht)); rw [← setIntegral_univ,←receipt F (book_h q w D u), show stageK _ Set.univ= _ from bridge_full q w D u]; unfold gas; rw [map_smul]; simp only [ContinuousLinearMap.smul_apply]; rw [R_one,inner_smul_right,re_ofReal_mul]; exact le_of_eq (by rw [show (inner ℂ x x).re=_ from inner_self_eq_norm_sq (𝕜:=ℂ) x])
lemma stereoY (u:0<D)(S:Set Space3): (bridgeW q w D S).IsHermitian:=by
 let P:= bridgeW q w D S; change Pᴴ=P; apply Matrix.ext; intro i j; rw [Matrix.conjTranspose_apply]; unfold P bridgeW stageK; simp only [Matrix.of_apply]; rw [Complex.star_def,← integral_conj]; refine integral_congr_ae (Eventually.of_forall fun x=>?_); unfold boon; dsimp only; by_cases h:i.2=j.2 <;> first |(rw [if_pos h, if_pos h.symm]; simp [mul_comm])| (rw [if_neg h,if_neg (Ne.symm h)]; simp) -- tune
lemma retinue (p:0<D)(S:Set Space3)(h:MeasurableSet S)(t:S⊆U)(x:lobby D*(3/4)≤ MeasureTheory.volume.real S): ∃ W : Violas.PlansM (Stamp q w), page (Stamp q w) ≤ 2*Violas.dim W ∧ (∀ z∈ W,lobby D/2*‖z‖^2 ≤ ∫ p in S, ∑ i:Zpo w,‖kNote D q w p z i‖^2):=by
 let A:=bridgeW q w D S; have ht:MeasureTheory.volume.restrict S = (Θ).restrict S:=by rw [hiveV,Measure.restrict_restrict h,Set.inter_eq_left.mpr t]
 have hp:3/4*lobby D*page (Stamp q w)≤ A.trace.re:=by
    unfold A
    unfold Matrix.trace; rw [Complex.re_sum]; refine le_trans (show _ ≤ (∑ i:Stamp q w,lobby D*(3/4)) from (by simp [page]; ring_nf; simp)) (sum_le_sum (fun i _=>?_)) -- tune b explicit.
    unfold bridgeW stageK boon; simp_rw [Matrix.diag_apply, Matrix.of_apply]; rw [←ht]; simp only [↓reduceIte,tLab,aimed,sub_self]; simp [aim,songQ]; change _≤ (∫ p:Space3 in S,coastE (inner ℝ p 0)).re; simpa using x
 obtain ⟨L,hL,T'⟩:= Violas.polarCharge (stereoY q w D p S) _ (lobby_p p) hp (fun x=>(plank q w D p S h x).2)
 · refine ⟨L,hL,fun z u=>?_⟩; simp_rw [ht,←bridge_value]; exact (receipt F (book_h q w D p) S z) ▸ T' _ u -- issue ht volume Snow
#print axioms retinue
end Midway
end YM.CF.Window.ArchiveK

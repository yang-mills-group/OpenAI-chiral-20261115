import YM.CF.Jet.Foster
import YM.CF.Broc.Wisdom
import YM.CF.Jet.Vista
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Finset MeasureTheory Phase Phase.Sample Lattice Cube Lat Broc Branch Dial Drapes Tulip Matrix SU.Pair
open scoped Topology BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace Kronecker Matrix
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra
variable {E I:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Fintype I][DecidableEq I]{k:ℕ} {X:E→Op I}
lemma matt (h:∀ i j,ContDiff ℝ (↑k:WithTop ℕ∞) (fun p=> X p i j)): ContDiff ℝ (↑k:WithTop ℕ∞) X:=by
 let Z:(I→I→ℂ)→ₗ[ℝ] Op I:=⟨⟨Matrix.of,fun _ _=> rfl⟩,fun _ _=> rfl⟩
 exact Z.toContinuousLinearMap.contDiff.comp (show ContDiff ℝ (↑k:WithTop ℕ∞) (fun x i j=>X x i j) from contDiff_pi.mpr fun i=>contDiff_pi.mpr fun j=> h i j)
lemma elem (i j:I): ContDiff ℝ (↑k:WithTop ℕ∞) (fun x:Op I=>x i j):=by
  let Z:Op I→ₗ[ℝ]ℂ:=⟨⟨fun A=>A i j,fun _ _=>rfl⟩,fun _ _=>rfl⟩; exact Z.toContinuousLinearMap.contDiff
lemma elem_k (i:I): ContDiff ℝ (↑k:WithTop ℕ∞) (fun p:Ket I=>p.ofLp i) :=(PiLp.proj (p:=2) (𝕜:=ℝ) (fun _=>ℂ) i).contDiff
lemma cc_w {F:E→ℂ} (h:ContDiff ℝ (↑k:WithTop ℕ∞) F): ContDiff ℝ (↑k:WithTop ℕ∞) (fun i=>star (F i)):=Complex.conjCLE.toContinuousLinearMap.contDiff.comp h
lemma det_k (A:E→Op I) (h:∀ i j,ContDiff ℝ (↑k:WithTop ℕ∞) (fun p=> A p i j)): ContDiff ℝ (↑k:WithTop ℕ∞) (fun i=>(A i).det) :=by
 simp_rw [Matrix.det_apply]; apply ContDiff.sum; intro i _; have ht:ContDiff ℝ (↑k:WithTop ℕ∞) (fun p=>∏ j,A p (i j) j):=contDiff_prod (fun j _=> h _ _)
 rcases Int.units_eq_one_or i.sign with h|h<;> rw [h]; simpa using ht
 simp only [Units.smul_def, Units.val_neg,Units.val_one,neg_smul,one_smul]; exact ht.neg
lemma full_k : ContDiff ℝ (↑k:WithTop ℕ∞) fullM:=by
 apply matt; rintro ⟨x,i⟩ ⟨y,j⟩; apply ContDiff.mul (g:=fun u:Vect=>pairM u.ofLp i j) contDiff_const
 cases i <;> cases j
 · simp only [pairM,Matrix.fromBlocks_apply₁₁,cc_apply,eps,Matrix.of_apply]
   apply cc_w; apply det_k; intro i j; fin_cases i <;> first | exact contDiff_const | exact elem_k _ -- check
 all_goals simp only [pairM, Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,mix,lone, Matrix.transpose_apply,Matrix.of_apply,ExTwo.exterior, Matrix.neg_apply, Matrix.vecMulVec_apply,Pi.star_apply]
 all_goals first|exact (ContDiff.mul (elem_k _) contDiff_const).sub (ContDiff.mul (elem_k _) contDiff_const)|exact ((cc_w (elem_k _)).mul (cc_w (elem_k _))).neg
lemma cc_full : ContDiff ℝ (↑k:WithTop ℕ∞) localPair:=by
 apply matt; rintro ⟨x,i⟩ ⟨y,j⟩; exact ContDiff.mul contDiff_const ((elem i j).comp full_k)
lemma trie : ContDiff ℝ (↑k:WithTop ℕ∞) SU.triple :=by
 have h: ContDiff ℝ (↑k:WithTop ℕ∞) SU.each:=by
    apply matt; intro i j; cases i <;> cases j
    · simp only [SU.each,CF.Join.both,Matrix.fromBlocks_apply₁₁,ExTwo.wedge_entry]; exact ((elem _ _).mul (elem _ _)).sub ((elem _ _).mul (elem _ _))
    · exact contDiff_const
    · exact contDiff_const
    exact cc_w (elem _ _)
 apply matt; rintro ⟨x,i⟩ ⟨y,j⟩; exact ContDiff.mul contDiff_const ((elem i j).comp h)
variable {c e a r:ℝ}
def seek {N:Side}(Z:E→Stun N)(n:ℕ)(x:E)(K:ℝ):Prop:=∀ i, Allows n (fun t=> hook (Z t) i) x K
lemma blend_r(B:ℝ)(b:0≤B)(n:ℕ):∃ C:ℝ,1≤C ∧∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (N P:Side) (F:E→Sew N P) x, TransK n (fun i=>(F i).1.1) x B → TransK n (fun i=>(F i).1.2) x B → seek (fun i=>(F i).2.1) n x B → seek (fun i=>(F i).2.2) n x B→ Allows n (post ∘ F) x C:=by
 obtain ⟨C,hC,H⟩:=compact_allow n b SU.triple trie; obtain ⟨D,hD,P⟩:= compact_allow n b localPair cc_full
 let a:=composeCost n C B; let u:=composeCost n D B; let W:=starL' ℝ (A:= Twig); let S:= starL' ℝ (A:=Op QuiltF); let Z:=max a B
 let Y:=max (max Z (‖W.toContinuousLinearMap‖*Z)) (max u (‖S.toContinuousLinearMap‖*u))
 refine ⟨max 1 Y,le_max_left ..,fun E _ _ N M F x f g i j=>?_⟩
 let A:=max 1 Y; have hp :0≤ A:= le_max_of_le_left zero_le_one
 have he {N:Side}(v:E→Stun N)(g:seek v n x B):Allows n (fun t=>palt (v t)) x A:= by
   apply allows_pi hp; intro i; apply allows_pi hp; intro j; let z:=fun t=> hook (v t) i
   have h : Allows n (localPair ∘ z) x u:= (P _ (g i).value).comp (f:=z) (g i); cases j <;> simp only [palt,Bool.false_eq_true,ite_false,ite_true]
   exact (h.linear S.toContinuousLinearMap le_rfl).mono (((le_max_right ..).trans (le_max_right ..)).trans (le_max_right ..)); exact h.mono (((le_max_left ..).trans (le_max_right ..)).trans (le_max_right ..))
 have hQ {N:Side}(U:E→Bkg N)(g:TransK n U x B):Allows n (fun y=>profile (U y)) x A:=by
    apply allows_pi hp; intro i; apply allows_pi hp; intro j; let z:=fun t=> SU.fund (U t i)
    have h:=g i; have hx: Allows n (fun t=>brand (U t i)) x Z:= (((H _ h.value).comp (f:=z) h).mono (le_max_left ..)).pair (h.mono (le_max_right ..)); cases j
    exact (hx.linear W.toContinuousLinearMap le_rfl).mono (((le_max_right ..).trans (le_max_left ..)).trans (le_max_right ..))
    exact hx.mono (((le_max_left ..).trans (le_max_left ..)).trans (le_max_right ..))
 exact ((hQ _ f).pair (hQ _ g)).pair ((he _ i).pair (he _ j))
end YM.CF.Jet

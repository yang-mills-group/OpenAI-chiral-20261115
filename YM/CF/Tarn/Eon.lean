import YM.CF.Arena.Petal
import YM.CF.Tarn.Reap
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
lemma dict_sum{ι:Type}[Fintype ι](Q:ι→DirP c): dict (∑ i,Q i)= ∑ i,dict (Q i):=by ext1 i; simp_rw [dict,Finset.sum_apply]; nth_rw 1 [sum_comm]; nth_rw 2 [sum_comm]; unfold dict; rw [Finset.sum_sub_distrib]
lemma pool_t(n:ℕ)(h:2 ≤ n)(Z: SU.group.Color→ₗᵢ[ℝ] SU.group.Color) : ∃ M K,CapY M ∧ (∀ l,l ≤ M l)∧nib K∧ ∀ r σ (A D:ℝ),0<σ→σ ≤1→0 ≤ D→D ≤ A →∀ (c:Side)(F:FileM (More c) G), LayerP c F→ Head (More c) Z F → M r < (More c).val → (∀ i,CakeF (F i) i r n σ A∧cFoot 2 (satX (F i))) → Prox F 2 D → ∃ B:DirP (More c),(∀ i j,B i j≠0→separation i j ≤ M r) ∧ (∀ i j,Urge (B i j) i 2 1 (M r) n σ (A*K r) 0) ∧∀ i,Urge (F i+dict B i) i 2 2 (M r) n σ (A*K r) (D*K r):=by
 obtain ⟨M,K,hM,hR,hK,H⟩:=journey G Z Thera.yet_one n 0 1 h (by omega)
 let S(r):= 1+(4:ℝ)*K r; let X(v):=(Fintype.card Charm:ℝ)*S v
 have hs:nib S:= (nib_const _ (by norm_num)).add ((nib_const _ (by norm_num)).mul hK)
 refine ⟨M,X,hM,hR,(nib_const _ (by positivity)).mul hs,?_⟩
 intro r σ A D hv hu hD hA c F hp hz hr hf hx
 have he:∀ i,2 ≤ i→i<2+1→ Prox F i D:=fun i hx' hh=> by rwa [show i=2 by omega]
 have ha:0 ≤ A:=hD.trans hA
 choose W Q hW hQ hvQ hpQ using fun d:Charm=> (H r σ hv hu A D ha hD hA c F hr hp (fun i=>(hf i).1) (fun i=>(hf i).2) he (fun _=>hz) d).legs
 choose B hB hb' hZ using fun d:Charm=> river (hW d) hv h
 let N(i:Charm):= laidC i c F; let T (i:Charm):= N i+dict (B i); have hτ:F+dict (∑ i,B i)= ∑ i,T i:=by unfold T; rw [sum_add_distrib,dict_sum,show ∑ i,N i=F from ssum c F hp] -- tune
 have hP: K r ≤ S r:=by unfold S; linarith only [hib hK r]
 have hT(d:Charm)(i:Site (More c)):Urge (T d i) i 2 2 (M r) n σ (A*S r) (D*S r):=by
    let v:=gammaT c d; let X:= N d 0+W d-Q d
    have he: Urge (Q d) 0 2 2 (M r) n σ (D*K r) (D*K r):= ⟨hQ d,hvQ d,fun i _ hl=> pollen hv (hQ d) (hl.trans h)⟩
    let A':= A+2*(A*K r)+D*K r; have ht:Urge X 0 2 2 (M r) n σ A' 0:= Foot.change (hpQ d) (by decide) (by decide) le_rfl ((((mer hp d (fun i=>(hf i).1) 0).under le_rfl (hR _) le_rfl).add ((hW d).cakeF hv h).1).less (hQ d))
    have hh:T d i=Sean v X i+Sean v (Q d) i:=by
       rw [← scroll_p]; unfold X; rw [sub_add_cancel,scroll_p,show stroll v i (W d)=_ from hZ d i,show stroll v i (N d 0)=_ from congrFun (orbit_G _ _ (revive d c F)).symm i]; rfl -- hZ order? unfold v
    rw [hh]; refine (urge_add _ _ (urgeS i v ht hv h h) (urgeS i v he hv h h) hv h h).under ?_ (by rw [zero_add]; exact mul_le_mul_of_nonneg_left hP hD) le_rfl
    unfold A' S; nlinarith only [mul_le_mul_of_nonneg_right hA (hib hK r)]
 refine ⟨∑ i,B i,?_,?_,?_⟩
 rotate_left 2
 · intro i; change Urge ((F+dict (∑ i,B i)) i) _ _ _ _ _ _ _ _; rw [hτ,Finset.sum_apply]; refine (urgeSum univ (fun d _=> hT d i) hv h h).under (le_of_eq (by unfold X; rw [card_univ]; ring)) (le_of_eq (by unfold X; rw [card_univ]; ring)) le_rfl -- swap order tune
 · intro i j p; by_contra! he; apply p; rw [Finset.sum_apply,Finset.sum_apply]; exact sum_eq_zero (fun d _=>not_not.mp (mt (hB d _ _) (not_le.mpr he)))
 intro i j; rw [Finset.sum_apply,Finset.sum_apply]; refine (urgeSum univ (fun d _=> Foot.change (hb' d i j).2 le_rfl (by decide:1<0+2) (le_refl 0) (hb' d i j).1) hv h (by omega)).under ?_ (by simp) le_rfl; rw [card_univ]; unfold X; nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP ha) (Nat.cast_nonneg (Fintype.card Charm) (α:=ℝ))]
end YM.CF.Tarn

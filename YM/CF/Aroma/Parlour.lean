import YM.CF.Aroma.Trail
/-! infrared coefficient via chiral polarization at smallest periodic height; nonsingular on precise cut shifted torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Aroma
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Rush Cube MeasureTheory NormedSpace
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {n:Type}[Fintype n][DecidableEq n]
def port(N:Side):Momentum:=spark 0 (pinch N)
theorem infrared(T:Op n)(hp:star T=T)(j:ℕ)(hj:1≤j)(η C:ℝ)(h:0<η)(k:0<C) :∃ F:ℝ,∃ G:ℕ,∀ (N:Side)(M:Side)(J:InJ n N),G≤N.val→Even N.val → Foot T j M J→ bill J η≤C→ b2 (Met J) η ≤ C→
 ‖room J (port N) / ((Fintype.card (Site (More N)):ℝ)*pinch N^2)-((Matrix.trace (T*T)).re/(12*Real.pi^2))*Real.log N.val‖ ≤ F:=by
 obtain ⟨F,G,H⟩:= polar_h T hp j hj η C h k; refine ⟨F,G+16,fun N M J ht e P v g=>?_⟩
 have hb:16≤N.val:=by omega
 let l:=pinch N
 let U:Tween T j M N η C:=⟨P.oddM,e,by omega,oak J,float (Met J),paidL _ h k v,petals _ h k g,growth P hb⟩
 have he(a:Axis): room J (spark a (pinch N))=(∑ i:Site N,(U.flame (mel i) a l+ U.flame (mel i) a (- (l:ℂ))).re)/4:=by
    let p:=spark a (pinch N); have hp: spark a (- (l:ℂ))=-p:=by unfold spark p spark; rw [neg_smul] -- tune
    have ht(s:ℝ)(h:|s|≤ l)(i:Site N):= trail8 a 1 hb i s h
    have hz: ∀ i: Site N, spoon (mel i) (-p)∈realCube zone:=fun i=>by rw [← hp,← Complex.ofReal_neg]; apply ht; rw [abs_neg,abs_of_pos (pinch_pos _)];
    change room J p=_; rw [P.reel U rfl rfl p (tide_pos a) (fun i=>ht _ (by rw [abs_of_pos (pinch_pos _)]) i) hz]
    congr 1; apply sum_congr rfl; intro i _; unfold Tween.flame; rw [hp]; unfold p l; ring -- tune
 have hs: room J (port N) / ((Fintype.card (Site (More N)):ℝ)*pinch N^2)=(∑ x,U.valley x)/(N.val:ℝ)^4:=by
    have hm:= aiming P hb; change room J (spark _ _)=0 at hm; rw [he] at hm
    have hk(i:Site N): river (bark i)=mel i:=riverB _
    rw [port,← sub_zero (room J _),← aiming P hb,why, he,he]
    simp only [Tween.valley,hk,site_card,More]; rw [←Finset.sum_div]
    simp only [Tween.slab,hk, Complex.sub_re,Complex.add_re, sum_sub_distrib, sum_add_distrib,l]; push_cast; ring -- tune
 rw [hs]; exact H _ (by omega) _ U
end YM.CF.Aroma

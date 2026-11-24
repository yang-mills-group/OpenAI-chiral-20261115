import YM.CF.Buffered.Gutter
import YM.CF.Buffered.Shower
/-!
 Positive, scalar joint partition. Choose bins by COMMON Haar center average in each boundary registry. No conditioning with exact matching.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 520000
noncomputable section
namespace YM.CF.Buffered.Crust.Grid
open Function Filter Finset Lattice Wilson RG PathData Work.F03 Cube Region Roost Rush MeasureTheory Metric
open scoped InnerProductSpace Matrix.Norms.Frobenius BigOperators Topology ENNReal Classical
variable {G:Gauge}{N P D:Side}{a b r C L β:ℝ}{s:ℕ}
abbrev deckK(K:Planck N P D): Tower D× Edge (Site P)≃ Edge (Site N) := ((Equiv.prodAssoc (Tower D) (Site P) Axis).symm.trans (Equiv.prodCongr (send K) (Equiv.refl Axis))) -- syntax
lemma issue_mp (K:Planck N P D): MeasurePreserving (issue (G:=G) K) (Measure.pi (fun _=> Wilson.prior G P)) (Wilson.prior G N):= by
 have ht: MeasurePreserving _ _ _:= (Ordered.reEnd (deckK K) G.probHaar).comp (unc_mp (I:=Tower D) (J:=Edge (Site P)) _); exact ht
def tubing (s:Finset (Edge (Site P)))(a:ℝ)(U:Config G P) := {V: Config G P| ∀ i∈ s,Dg G (U i) (V i)≤a}
lemma tubing_closed (s:Finset (Edge (Site P)))(a:ℝ)(U:Config G P): IsClosed (tubing s a U):=by
 unfold tubing Dg; simp only [Set.setOf_forall]; exact isClosed_iInter fun i=> isClosed_iInter fun _=> isClosed_le (by fun_prop) continuous_const
lemma tubing_mass (s:Finset (Edge (Site P)))(a:ℝ)(p:0<a)(h:a≤1)(U:Config G P): (a/4)^(Module.finrank ℝ G.Mat*s.card) ≤ (Wilson.prior G P).real (tubing s a U):=by
 let z:= G.shell a; let d(i:Edge (Site P)):= (fun x:G.El=> (U i)⁻¹*x) ⁻¹' z
 have he:tubing s a U=Set.univ.pi (fun i=> if i∈ s then d i else Set.univ):=by
   ext x; constructor
   · intro h i _; dsimp only; split; next e=> exact h i e
     trivial
   intro h i g; specialize h i (Set.mem_univ _); dsimp only at h; rw [if_pos g] at h; exact h
 let f(i):= G.probHaar (d i); let V:=G.probHaar z; have hx(i):f i=V:= (measurePreserving_mul_left G.probHaar (U i)⁻¹).measure_preimage (G.shell_meas a).nullMeasurableSet
 have hi : Wilson.prior G P (tubing s a U)= V^s.card:= by
   rw [he, Wilson.prior, Measure.pi_pi]
   rw [←Finset.prod_subset (s.subset_univ)]; swap; · intro i h v; rw [if_neg v,measure_univ]
   rw [←prod_const]; apply prod_congr rfl; intro i h; rw [if_pos h]; exact hx i
 rw [measureReal_def,hi,pow_mul,ENNReal.toReal_pow]; exact pow_le_pow_left₀ (by positivity) (G.shell_ge a p h) _

lemma hose_bin (s:Finset (Edge (Site P)))(a:ℝ)(p:0<a)(h:a≤1)(f:Config G P→ℝ)(z:Envelope f)(u:∀ x,0≤f x)(v:0< (∫ x,f x∂ Wilson.prior G P)): ∃ U:Config G P,(a/4)^(Module.finrank ℝ G.Mat*s.card)/2 * (∫ x,f x∂ Wilson.prior G P) ≤ ∫ x in tubing s a U,f x∂ Wilson.prior G P:=by
 let μ:=Wilson.prior G P; letI : IsProbabilityMeasure μ:=by unfold μ; infer_instance
 let S:Set (Config G P × Config G P):={x| x.2∈ tubing s a x.1}; have hs: MeasurableSet S:=by
    change MeasurableSet {x:Config G P × Config G P | ∀ i∈s,Dg G (x.1 i) (x.2 i)≤a}; simp only [Set.setOf_forall]; exact MeasurableSet.iInter fun i=> MeasurableSet.iInter fun p=> (isClosed_le (by unfold Dg; fun_prop) continuous_const).measurableSet
 let t(x y:Config G P):= S.indicator (fun x=>f x.2) (x,y); have ht: Integrable (uncurry t) (μ.prod μ):= (show Integrable (S.indicator (fun x=>f x.2)) (μ.prod μ) from ((measurePreserving_snd (μ:=μ) (ν:=μ)).integrable_comp_of_integrable (z.integrable μ)).indicator hs)
 let Z:=(a/4)^(Module.finrank ℝ G.Mat*s.card); let T:=∫ x, f x∂μ; have hT:0<T:=v; have hZ:0<Z:=by unfold Z; positivity
 have hv(y:Config G P): (∫ x,t x y ∂μ) ≥ Z*f y:=by
    have he: (fun x=>t x y)= (tubing s a y).indicator (fun _=>f y):=by
       funext x; unfold t; by_cases p:x∈tubing s a y
       · rw [Set.indicator_of_mem p,Set.indicator_of_mem (show (x,y)∈S from fun i v=>by rw [Dg_comm]; exact p i v)]
       rw [Set.indicator_of_notMem p,Set.indicator_of_notMem (show (x,y)∉S from fun e=>p (fun i v=>by rw [Dg_comm]; exact e i v))]
    rw [he,integral_indicator (tubing_closed ..).measurableSet,setIntegral_const]; exact mul_le_mul_of_nonneg_right (tubing_mass s a p h y) (u y)
 let B:=fun y:Config G P=>∫ x,t y x∂μ
 have hx:∫ x,B x∂ μ ≥ Z*T:=by
    unfold T B; rw [integral_integral_swap ht,← MeasureTheory.integral_const_mul]; exact integral_mono ((z.integrable _).const_mul Z) ht.integral_prod_right hv -- direction names
 have hB :∃ x, Z/2*T≤ B x:=by by_contra! k; have he:= integral_mono ht.integral_prod_left (integrable_const (Z/2*T)) (fun i=> (k i).le); rw [integral_const,probReal_univ,one_smul] at he; change (∫ x,B x∂μ) ≤ _ at he; nlinarith
 obtain ⟨b,u⟩:=hB; refine ⟨b,u.trans (le_of_eq ?_)⟩; unfold B
 have he:t b= (tubing s a b).indicator f:=by
   funext x; by_cases k:x∈tubing s a b; unfold t; rw [Set.indicator_of_mem k,Set.indicator_of_mem (show (b,x)∈ S from k)]; unfold t; rw [Set.indicator_of_notMem k,Set.indicator_of_notMem (show (b,x)∉ S from k)]
 simp_rw [he]; exact integral_indicator (tubing_closed ..).measurableSet
#print axioms hose_bin
end YM.CF.Buffered.Crust.Grid

import YM.SU5.Relativistic.Yokel
import YM.CF.Onyx.Pelt
/-! # true compact Cell price. no rotating mark sectors. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.Papyrus.Franc.Loaves
open Function Set Filter Topology NormedSpace Fock Finset Thera MeasureTheory Lattice Cube Lat Fir Onyx Rush Ember SU Scroll Tulip
open YM.Next.Free
set_option quotPrecheck false
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered BPress.Spin.Blank
open Stationary (Gaia cartWeight exileE boundsEarth earth_meas earth_oaks)
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal
attribute [local instance] opCStarAlgebra
local notation "B" => angle true
local notation "F" M:max => bent true 4 ((M:Tulip.Male).val)
local notation "NΩ" => Op SpinIdx
section
variable {A:Type*}{l:Filter A}{M:A→Tulip.Male} (h:Tendsto (fun i=>(M i).val) l atTop){N:A→Side}(Y:∀ i, Site (N i)){g:Gaia} (p:g∈boundsEarth) (e:g≠0) (x:Tendsto (fun i=> bark (Y i)) l (𝓝 g))
local notation "Z" => Op SpinIdx
private def ix(p:Gaia):= tough (exileE p)
private def τ(p:Gaia):ℂ:= ↑(∑ a:Axis,((ix p a).re)^2:ℝ)
def noon(g:Gaia) : Op SpinIdx := let X:= (1+τ g)⁻¹; (1/2:ℂ) • (1:NΩ)+(X-1/2) • grading + grading*Fir.zen (X • ix g)
abbrev cn(p:Gaia):Momentum:= tmap (exileE p)
include x
lemma mill : Tendsto (fun i=>mel (Y i)) l (𝓝 (cn g)):=by
 have he: Continuous (cn) :=by -- tune Gaia simple Pi
    unfold cn exileE; apply continuous_pi; intro i; change Continuous fun p:Gaia=>((p i:ℝ):ℂ); fun_prop
 apply Tendsto.congr ?_ ((he.tendsto g).comp x); intro i; unfold Function.comp cn bark; rw [MeasurableEquiv.apply_symm_apply]; rfl
include e p h
lemma chute : Tendsto (fun i=> bent true 4 ((M i).val) (mel (Y i))) l (𝓝 (noon g)):=by
 let f:= fun i=> mel (Y i)
 let v(i):= mixL 4 (M i).val (f i)
 have he:Jill.Bound Real.pi (exileE g):=by
    apply (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr; intro i; exact abs_le.mpr ⟨(p i).1.le,(p i).2⟩
 have hk:exileE g≠0:=fun t=>e (exileE.injective t)
 have hv:Tendsto v l (𝓝 (ix g)):= tendsto_pi_nhds.mpr fun j=> Shore.gulch h (mill Y x) (Eventually.of_forall (fun i=>(M i).property)) he hk j (Eventually.of_forall (fun i=>mel_h _))
 let L:= fun i=>shell 4 (M i).val (f i)
 have hh:Tendsto L l (𝓝 (1+τ g)⁻¹):=by
    let X(p:Momentum):ℂ:= ↑(∑ i:Axis,((p i).re)^2:ℝ); have ht:0< (1+X (ix g)).re:=by
       unfold X; rw [Complex.add_re,Complex.one_re,Complex.ofReal_re]; positivity
    have ha: Continuous X:=by unfold X; fun_prop
    refine Tendsto.congr (?_) ((Tendsto.add tendsto_const_nhds ((ha.tendsto _).comp hv)).inv₀ (show 1+X (ix g) ≠0 from (fun k=> ne_of_gt ht (by rw [k];rfl))))
    intro i; let F':=base_subset_realCube zone_pos (mel_h (Y i)); unfold L; change (1+X (v i))⁻¹=_; rw [shell_inv 4 _ F' (mel_away _), prodM_self _ (phys_mix _ _ (M i).property _ F'.1)] -- tune infer binder
 have hl:Tendsto (fun i=>skin 4 (M i).val (f i)) l (𝓝 ((1+τ g)⁻¹ • ix g)):=by
    refine (hh.smul hv).congr fun i=> ?_; exact Eq.symm (skin_mix 4 _ (base_subset_realCube zone_pos (mel_h _)))
 change Tendsto (fun i=> bar 4 (M i).val (mel (Y i))) _ _
 exact (Tendsto.add (Tendsto.add tendsto_const_nhds ((hh.sub_const _).smul tendsto_const_nhds)) (Tendsto.mul tendsto_const_nhds ((Continuous.tendsto (f:=Fir.zen) (by unfold Fir.zen; fun_prop) _).comp hl)))
end
section
variable {I:Type*}[NormedAddCommGroup I][NormedSpace ℝ I][CompleteSpace I]
-- arbitrary marks vectors, integrate against volume. special easier Cλ
variable (N:Side)
private def planH (f:Site N→ℂ)(x:Gaia):ℂ:= ∑ i:Site N,(Set.indicator (cellH i) (fun _=> f i)) x
private lemma plan_int (f:Site N→ℂ)(i:Site N): Integrable (Set.indicator (cellH i) (fun _=> f i)) volume:= (integrable_indicator_iff (cell_meas _)).2 (integrableOn_const (by rw [cellCore]; finiteness))
private lemma plan_p (f:Site N→ℂ)(k:Site N)(x:Gaia)(h:x∈cellH k): planH N f x=f k:=by unfold planH; rw [sum_eq_single k,Set.indicator_of_mem h]; intro i _ p; exact Set.indicator_of_notMem (show x∉cellH i from fun g=> Set.disjoint_left.mp (Ember.clears p) g h) _; simp
private lemma t_pay(f:Site N→ℂ) (p:Even N.val):
    (((N.val:ℂ)^4))⁻¹*(∑ i,f i)=(cartWeight:ℂ)*(∫ x:Gaia in boundsEarth,planH N f x):=by
 let l:ℝ:=(2*pinch N)^4
 have hx:(∫ x:Gaia in boundsEarth,planH N f x)= (l:ℂ) * ∑ i,f i:=by
    rw [setIntegral_congr_set (canopy p).symm]; have he: Integrable (planH N f) volume:= integrable_finsetSum _ (fun i _=>plan_int N f i)
    rw [integral_iUnion_fintype cell_meas Ember.clears (fun _=>he.integrableOn),mul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [setIntegral_congr_fun (g:=fun _=>f i) (cell_meas _) (fun x v=>plan_p N f i x v),setIntegral_const, Measure.real,cellCore,ENNReal.toReal_pow,ENNReal.toReal_ofReal (by have hp:=pinch_pos N; positivity)]; rfl
 rw [hx,←mul_assoc]; apply congrArg (·*∑ i,f i); rw [show (N.val:ℂ)=↑(N.val:ℝ) from (Complex.ofReal_natCast _).symm,←Complex.ofReal_pow,←Complex.ofReal_inv,←Complex.ofReal_mul]; apply congrArg; unfold cartWeight l; rw [payH (N:=N)]; field_simp [(pinch_pos N).ne',(nPos N).ne'] <;> ring
omit N
variable {s:ℕ→Side} {F':∀ i,Site (s i)→ℂ}(h:Tendsto s atTop atTop)
include h
lemma registry (e:∀ i,Even (s i).val) (B':Gaia→ℂ) (P:∀ g∈boundsEarth,g≠0→∀ y:∀ i,Site (s i),(∀ i,g∈cellH (y i))→ Tendsto (fun i=>F' i (y i)) atTop (𝓝 (B' g)))
    (C:ℝ)(v:∀ i x,‖F' i x‖≤C) : Tendsto (fun i:ℕ=> (((((s i).val:ℂ)^4))⁻¹:ℂ)*∑ j,F' i j) atTop (𝓝 ((cartWeight:ℂ)* ∫ p:Gaia in boundsEarth,B' p)):=by
 let μ:Measure Gaia:=volume.restrict boundsEarth; have hp:∀ i:ℕ,∀ᵐ x ∂μ,x∈boundsEarth ∧∃ g:Site (s i),x∈ cellH g:=fun i=>arboretum (e i) earth_meas (Subset.refl _)
 let G(n):=planH _ (F' n); have hg i:Integrable (G i) volume:= integrable_finsetSum _ (fun j _=>plan_int _ _ j)
 simp_rw [t_pay (s _) _ (e _)] -- tune dependent simp
 refine Tendsto.const_mul _ (tendsto_integral_of_dominated_convergence (bound:=fun _=> C) (fun i=>(show Integrable (G i) μ from (hg i).integrableOn).aestronglyMeasurable) (integrableOn_const earth_oaks) (fun i=> (hp i).mono fun x u=> ?_) ?_)
 · obtain ⟨g,t⟩:=u.2; change ‖planH _ _ _‖ ≤ _; rw [plan_p _ _ _ _ t]; exact v i g
 filter_upwards [ae_all_iff.mpr hp,ae_restrict_of_ae (show ∀ᵐ x:Gaia,x≠0 from by rw [ae_iff]; rw [show {x:Gaia | ¬x≠0}={0} from (by ext; simp),measure_singleton])] with x hx ex
 choose y hy using fun i=>(hx i).2; apply Tendsto.congr _ (P x (hx 0).1 ex y hy); intro i; exact Eq.symm (plan_p _ _ _ _ (hy i)) -- tune
end
end YM.CF.Papyrus.Franc.Loaves

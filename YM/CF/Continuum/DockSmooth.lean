import YM.CF.Continuum.CanalTwo
import Mathlib.MeasureTheory.Function.ContinuousMapDense
/-! # Approximation of buffered gauge probes by the SAME continuous stencils

Use a bounded projection after smoothing actual Borel transfers before Reynolds.
Observation-level thermal RP can then apply even though active branch kernels
use Borel decisions. Prices needn't be uniform over top cutoff for this.
-/
set_option maxHeartbeats 800000
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
namespace YM.CF.Window.Evenly
open Function Finset NormedSpace Filter Metric Lattice Wilson Laurent MeasureTheory RG
open Lat Cube RP Push.GridApprox Topology Next.Rank.Thirst
open scoped Topology BigOperators Classical
variable {n:Side} {I:Type*}[TopologicalSpace I][CompactSpace I][MeasurableSpace I][BorelSpace I][SecondCountableTopology I][FirstCountableTopology I]
local notation "G5" => SU.group
local notation "ζ" => (Site n → SU.group.El)
local notation "Γ"=>Config SU.group n
local notation "τ" => Measure.pi (fun _:Site n => SU.group.probHaar)
lemma tiltIntegral {A B Y:Type*}[MeasurableSpace A][MeasurableSpace B][NormedAddCommGroup Y][NormedSpace ℝ Y]{μ:Measure A}{ν:Measure B}{f:A→B}(hf:MeasurePreserving f μ ν){g:B→Y}(he:AEStronglyMeasurable g ν) : (∫ i,g (f i) ∂μ)= ∫ i,g i ∂ν:=by
 have he':AEStronglyMeasurable g (μ.map f):= hf.map_eq.symm ▸ he
 have hi:=integral_map hf.aemeasurable he'
 rw [hf.map_eq] at hi; exact hi.symm
private theorem clipFit [NormalSpace I] (ε:ℝ)(u:0 < ε)(c:ℝ)(hc:0<c)(μ:Measure I)[IsFiniteMeasure μ][μ.WeaklyRegular]{X:I→ℂ}(h: Envelope X)(v: ∀ x,‖X x‖≤c) : ∃ Y:I→ℂ, Continuous Y∧(∀ x,‖Y x‖≤c)∧ ∫ x,‖X x-Y x‖ ∂μ ≤ ε :=by
 let R(z:ℂ):= (c/max c ‖z‖) • z; have hm(z:ℂ):0 < max c ‖z‖:=hc.trans_le (le_max_left ..); have hs:Continuous R:= (continuous_const.div (continuous_const.max continuous_norm) (fun z=> (hm z).ne')).smul continuous_id
 have ht(z:ℂ):‖R z‖ ≤ c:=by unfold R; rw [norm_smul, Real.norm_of_nonneg (div_pos hc (hm _)).le]; calc
       _ ≤ c/max c ‖z‖ * (max c ‖z‖):=by gcongr; exact le_max_right ..
       _ = c := div_mul_cancel₀ _ (hm z).ne'
 obtain ⟨f,he,m⟩:= (h.integrableC μ).exists_boundedContinuous_integral_sub_le (by linarith : 0<ε/2)
 refine ⟨R ∘ f, hs.comp f.continuous,fun i=>ht _,?_⟩
 refine le_trans (integral_mono (((Envelope.subC h (Envelope.compactC (hs.comp f.continuous))).integrableC μ).norm) (((h.integrableC μ).sub m).norm.const_mul (2:ℝ)) (fun i=> ?_)) (le_trans (Eq.le (integral_const_mul ..)) ?_)
 swap; · change 2*(∫ x, ‖X x - f x‖ ∂μ)≤_; linarith
 let x:= X i; let y:= f i; change ‖x-R y‖ ≤ 2*‖x-y‖
 rcases le_total c ‖y‖ with v'|v'; swap
 · rw [show R y=y from by unfold R; rw [max_eq_left v', div_self hc.ne', one_smul]]; linarith [norm_nonneg (x-y)]
 have hm:0<‖y‖:= hc.trans_le v'; have he:‖y-R y‖=‖y‖-c:=by
    rw [show y-R y=(1-c/‖y‖)•y from (by unfold R; rw [max_eq_right v',sub_smul,one_smul]),norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ((div_le_one hm).mpr v')),sub_mul, one_mul, div_mul_cancel₀ _ hm.ne']
 have huv:‖x‖≤c:=v i; have hu:=norm_sub_norm_le y x; rw [norm_sub_rev] at hu
 linarith [norm_sub_le_norm_sub_add_norm_sub x y (R y)] -- tune

variable (P:Patch)(c:Side)
local notation "FZ" => Tenant.Edges n
abbrev Peg (U:Finset (Tenant.Edges n)):= ↥U → SU.group.El
abbrev knows (U:Finset (Tenant.Edges n))(A:Config SU.group n→ℂ):Prop:=∀ (x y : Config SU.group n),(∀ i∈U, x i=y i) → A x=A y
private lemma getApprox (U:Finset (Tenant.Edges n)){A:Config SU.group n→ℂ}(u:knows U A)(h: Envelope A)(r:ℝ)(hr:0<r)(d:∀ i,‖A i‖≤r)(e:ℝ)(he:0<e): ∃ Y:Config SU.group n→ℂ, Continuous Y ∧ knows U Y∧(∀ i,‖Y i‖≤r)∧∫ x,‖A x-Y x‖ ∂prior G5 n ≤e :=by
 let f:Γ → Peg U:= fun x i=>x i.val; have ht: Continuous f:=continuous_pi (fun i=>continuous_apply i.val)
 let g:Peg U→Γ:=fun x i=> if hi:i∈U then x ⟨i,hi⟩ else 1; have hg:Measurable g:= measurable_pi_lambda _ (fun i=> (by unfold g; split; exact measurable_pi_apply _; exact measurable_const)); let A':= A ∘ g; have hu:∀ i, A i=A' (f i):=fun i=>u i _ (fun j h=> (by unfold g; rw [dif_pos h]))
 let v:= (prior G5 n).map f; have hx:MeasurePreserving f (prior G5 n) v:=⟨ht.measurable,rfl⟩; obtain ⟨Y,v,p,hV⟩:= clipFit e he r hr v (h.comp_env hg) (fun x=>d (g x)) -- opacity measure requires metric
 refine ⟨Y ∘ f,v.comp ht,fun x y h=>congrArg Y (funext fun m=>h m.val m.property),fun i=>p _,?_⟩; -- rewrite
 simp_rw [hu]
 -- caution also hV goal only lhs can use A
 exact (tiltIntegral hx (g:=fun x=> ‖A' x-Y x‖) (((h.meas.comp hg).sub v.measurable).norm.aestronglyMeasurable)).le.trans hV
open Set
private lemma gaugeCont : Continuous (fun i: ζ × Γ=> gauge i.1 i.2) := continuous_pi fun x=> by unfold Lattice.gauge; fun_prop
private lemma gaugeMeas_g (g:ζ):MeasurePreserving (fun t:ζ=>t*g) τ τ:= measurePreserving_pi (fun _=>SU.group.probHaar) _ (f:=fun i t=>t*g i) (fun i=>measurePreserving_mul_right _ _)
private theorem nearC[Xv: T2Space I](Y:I→Γ→ℂ)(e:Continuous (fun i:I × Γ=>Y i.1 i.2))(p: ℝ)(h:∀ i v,‖Y i v‖≤p)(μ:Measure I)[IsProbabilityMeasure μ]: Continuous fun v=>∫ i,Y i v ∂μ:=by
 apply continuous_iff_continuousAt.mpr; intro i; refine tendsto_integral_filter_of_dominated_convergence (fun _=>p) (Eventually.of_forall (fun i=>?_)) (Eventually.of_forall (fun i=>?_)) (integrable_const _) (Eventually.of_forall fun u=>?_)
 · exact (e.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
 · exact Eventually.of_forall (fun u=>h u i)
 exact (e.comp (continuous_const.prodMk continuous_id)).continuousAt
lemma fund_Y (X: Finset (Tenant.Edges n)){A: Config SU.group n→ℂ}(u:knows X A)(e:GaugeInvariant A)(h: Envelope A)(r:ℝ)(hr:0<r)(hv:∀ i,‖A i‖ ≤ r) (ε:ℝ)(hp:0<ε) : ∃ Y:Config SU.group n→ℂ, Continuous Y ∧ knows X Y ∧ GaugeInvariant Y ∧(∀ i, ‖Y i‖ ≤ r) ∧ ∫ i,‖A i-Y i‖ ∂prior G5 n ≤ ε:=by
 obtain ⟨A',ht,hz,hv',e'⟩:= getApprox X u h _ hr hv _ hp
 let g:= (A' ∘ (fun i:ζ × Γ=> gauge i.1 i.2)); let f(V:Γ):=∫ i,g (i,V) ∂τ
 have hF:Continuous g:= ht.comp gaugeCont; have hb(t:ζ)(v:Γ):‖g (t,v)‖≤r:= hv' _
 have hg(v:Γ): Envelope fun t=>g (t,v):= Envelope.compactC (hF.comp (continuous_id.prodMk continuous_const)); let Q(V:Γ):= A V - f V
 have hc:Continuous f:= nearC (fun i v=>g (i,v)) (by convert hF) r hb _; refine ⟨f,hc,?_ ,?_ ,?_,?_⟩
 · intro x y h; unfold f; apply integral_congr_ae; refine Eventually.of_forall fun i=>?_ ; refine hz _ _ (fun i v=>?_ ); unfold Lattice.gauge; dsimp only; rw [h i v]
 · intro t x; unfold f; have he(s:ζ):g (s,gauge t x)=g (s*t,x):=by change A' (gauge s (gauge t x)) = A' (gauge (s*t) x); apply congrArg A'; funext i; unfold Lattice.gauge; dsimp; group
   simp_rw [he]; exact tiltIntegral (gaugeMeas_g t) (g:=fun s=>g (s,x)) (hg x).meas.aestronglyMeasurable
 · intro i; unfold f; simpa using norm_integral_le_of_norm_le_const (μ:=τ) (C:=r) (f:=fun v=>g (v,i)) (Eventually.of_forall (fun t=> hb t i))
 let F(x:Γ)(j:ζ):= ‖(A (gauge j x)- A' (gauge j x))‖; have hu(x:Γ):‖Q x‖ ≤ ∫ j,F x j ∂τ:=by
   unfold F; simp_rw [e _ _]; let Z(i:ζ):=A x-g (i,x); change _ ≤ ∫ i:ζ,‖Z i‖ ∂τ; apply le_trans _ (norm_integral_le_integral_norm ..); apply le_of_eq; rw [show (∫ i,Z i ∂τ)=Q x from (by rw [show Z=fun i=>A x-g (i,x) from rfl,integral_sub (integrable_const _) ((hg x).integrableC _),integral_const,probReal_univ,one_smul])] -- tune
 have hp := h.subC (Envelope.compactC ht)
 have hgI : Integrable (Function.uncurry F) ((prior G5 n).prod τ):=((hp.comp_env ((gaugeCont.comp continuous_swap).measurable)).integrableC _).norm
 refine le_trans (integral_mono (((h.subC (Envelope.compactC hc)).integrableC _).norm) hgI.integral_prod_left hu) (le_trans (integral_integral_swap hgI).le ?_)
 have he(t:ζ): (∫ x,F x t ∂prior G5 n)= ∫ x, ‖A x-A' x‖ ∂prior G5 n:= tiltIntegral (prior_gauge t) (g:=fun x:Γ=>‖A x-A' x‖) hp.meas.norm.aestronglyMeasurable
 simp_rw [he, integral_const,probReal_univ,one_smul]; exact e'
end YM.CF.Window.Evenly

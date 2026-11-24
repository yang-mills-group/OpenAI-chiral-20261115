import YM.CF.BPress.Template
import YM.CF.Reflect.Merged
import YM.Push.SECTOR_MEASURE.Decompose
/-!
CB factor errors/changes of variables. Keep envelopes pointwise. Use the finite-volume measability room (not claimed uniform norm in Envelope statements). First tools: splice two measure pi's (finite probability factors), Haar-ball noise at 1 and density/movement at all such copies, reorder by index.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Law
open Function MeasureTheory RG Filter Wilson Lattice
open Push.SectorMeasure Env
open scoped Topology ENNReal NNReal BigOperators Classical
variable {G : Gauge} {s:Side}
section prob
variable {X Y Z : Type*} {I J : Type*}[Fintype I] [Fintype J] [MeasurableSpace X][MeasurableSpace Y][MeasurableSpace Z][NormedAddCommGroup Z][NormedSpace ℝ Z][CompleteSpace Z] [BorelSpace Z][SecondCountableTopology Z]
lemma restore (μ:Measure X)(ν:Measure Y)(f:X→Y)(p:MeasurePreserving f μ ν)(g:Y→Z)(h: Integrable g ν):∫ x,g x ∂ν=∫ x,g (f x) ∂μ:=by
 nth_rw 1 [←p.map_eq]; exact integral_map p.measurable.aemeasurable (p.map_eq.symm ▸ h.1)
variable (S : Finset I)
-- `patch` picks x at S; everywhere else original v. Want measure inputs all coordinates everywhere `Measure.pi μ`. Reuse RP.patch_mp or reprove general for any pi. Need conditional integral with variables ordered.
def rep {X : Type*} (x y : I→X) : I→ X:=fun i=> if i∈S then x i else y i
lemma rep_joint : Measurable (fun x: (I→X) × (I→X)=> rep S x.1 x.2):= by apply measurable_pi_lambda; intro i; unfold rep; split <;> fun_prop
@[simp] lemma rep_L {X : Type*} (x y : I→X)(i:I)(p:i∈S):rep S x y i=x i:=if_pos p
@[simp] lemma rep_R {X : Type*} (x y : I→X)(i:I)(p:i∉S):rep S x y i=y i:=if_neg p
variable (μ:Measure X) [IsProbabilityMeasure μ]
abbrev chain (μ : Measure X)(I : Type*)[Fintype I] : Measure (I→X) := Measure.pi fun _=> μ
lemma splice : MeasurePreserving (fun x:(I→X)×(I→X)=> rep S x.1 x.2) ((chain μ I).prod (chain μ I)) (chain μ I):=by
 -- RP.patch_mp available?
 exact RP.patch_mp μ S
lemma splice_mem (f:(I→X)→ Z)(h:Envelope f):∫ x,f x ∂chain μ I= ∫ x, (∫ y,f (rep S x y) ∂chain μ I)∂chain μ I:=by
 rw [restore _ _ _ (splice S μ) f (integrableX h _), integral_prod]; apply integrableX (along h (rep_joint S))

lemma reindex (e : I ≃ J) : MeasurePreserving (fun f:I→X=> f ∘ e.symm) (chain μ I) (chain μ J):=by
 have h:= measurePreserving_piCongrLeft (α:=fun _:J=>X) (fun _=>μ) e; convert! h using 1; ext i f; obtain ⟨k,rfl⟩:=e.surjective f; rw [MeasurableEquiv.piCongrLeft_apply_apply]; simp -- tune
-- reduce maps with injective keys. later others supplied fresh. rewrite as Set.range equival.
lemma keys (f:J→ I)(h: Injective f) : MeasurePreserving (fun g : I→X=> g ∘ f) (chain μ I) (chain μ J):=by
 let T:=Set.range f; let P:=MeasurableEquiv.piEquivPiSubtypeProd (fun _:I=>X) (·∈ T); let q := Equiv.ofInjective f h; haveI : Fintype T:=inferInstanceAs (Fintype {i:I// i∈ T}); let ν:= chain μ T; let υ:= chain μ {i:I//i∉T}; -- tune inst
 have p: MeasurePreserving P (chain μ I) (ν.prod υ):= by unfold ν υ chain; convert! measurePreserving_piEquivPiSubtypeProd (fun _ : I=> μ) (·∈T)
 exact (reindex μ (I:=↥T) q.symm).comp (measurePreserving_fst.comp p) -- tune
end prob

variable {I : Type*} [Fintype I]
lemma vl_cost (r : ℝ) {G : Gauge} (c : I→G.El) : Envelope fun x:I→G.El=> ∏ i, chord.ballDensity r (c i) (x i):=by
 refine ⟨?_,chord.charge G r^Fintype.card I,fun x=>?_⟩; apply Finset.measurable_fun_prod; intro i _; exact (chord.density_meas r).comp (f:=fun x:I→G.El=>(c i,x i)) (measurable_const.prodMk (measurable_pi_apply i)) -- tune
 rw [Real.norm_eq_abs,Finset.abs_prod,←Finset.card_univ,← Finset.prod_const]; exact Finset.prod_le_prod (fun _ _=>abs_nonneg _) fun _ _=>chord.bound ..
open Set
-- sampler from center 1. independent draws, (multiply templates from right)
def noise (G : Gauge)(r:ℝ) : Measure G.El:= ENNReal.ofReal (chord.charge G r) • G.probHaar.restrict (G.shell r)
instance (r : ℝ) : IsFiniteMeasure (noise G r):=by unfold noise; exact Measure.smul_finite _ ENNReal.ofReal_ne_top -- tune
lemma noise_p {r:ℝ} (p:0<r)(t:r≤1): IsProbabilityMeasure (noise G r):= by
 constructor; have hx:= chord.charge_pos (G:=G) p t; unfold noise chord.charge; rw [Measure.smul_apply,Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, ENNReal.ofReal_inv_of_pos (by exact inv_pos.mp hx), Measure.real,ENNReal.ofReal_toReal (measure_ne_top G.probHaar (G.shell r)), smul_eq_mul, ENNReal.inv_mul_cancel (fun v=>?_) (measure_ne_top G.probHaar (G.shell r))]; unfold chord.charge Measure.real at hx; simp [v] at hx
lemma noise_ae (r : ℝ) : ∀ᵐ x∂noise G r,G.chord x ≤ r:= Measure.ae_smul_measure (ae_restrict_mem (G.shell_meas r)) _ -- tune

variable {E : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][MeasurableSpace E][BorelSpace E][CompleteSpace E][SecondCountableTopology E] (g : (I→G.El) → E)
lemma menu (r : ℝ) : chain (noise G r) I= ENNReal.ofReal ((chord.charge G r)^ (Fintype.card I)) • (chain G.probHaar I).restrict (univ.pi (fun _=> G.shell r)):=by
 unfold chain; rw [Measure.restrict_pi_pi]; apply Measure.pi_eq; intro s h; simp_rw [noise, Measure.smul_apply, smul_eq_mul, Measure.pi_pi]; rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ENNReal.ofReal_pow (by unfold chord.charge; positivity)]
lemma entry_at (r : ℝ) : ∫ x, g x∂chain (noise G r) I=∫ x, (∏ i, chord.ballDensity r 1 (x i)) • g x ∂chain G.probHaar I:=by
 let S:= univ.pi (fun _:I=>G.shell r); let f:= chord.charge G r^(Fintype.card I); rw [menu, integral_smul_measure, ENNReal.toReal_ofReal (by unfold chord.charge; positivity),← integral_smul,← integral_indicator (MeasurableSet.univ_pi fun _=> G.shell_meas r)]
 apply integral_congr_ae; apply Eventually.of_forall; intro w; by_cases h:w∈ S
 · rw [Set.indicator_of_mem h]; have he (i:I): chord.ballDensity r 1 (w i)=chord.charge G r:= if_pos (chord.one _|>.le.trans (mem_univ_pi.mp h i)); simp_rw [he,Finset.prod_const,Finset.card_univ]
 rw [Set.indicator_of_notMem h]; dsimp only; rw [Finset.prod_eq_zero_iff.mpr ?_,zero_smul]; obtain ⟨i,v⟩:= not_forall.mp (fun l=> h (mem_univ_pi.mpr l)); exact ⟨i,Finset.mem_univ _,if_neg (fun h=> v (le_trans (chord.one _|>.symm.le) h))⟩
lemma translate_at (r : ℝ) (h:Envelope g) (v:I→ G.El): ∫ x, g (v*x)∂chain (noise G r) I=∫ x, (∏ i,chord.ballDensity r (v i) (x i)) • g x ∂chain G.probHaar I:=by
 let μ:=chain G.probHaar I; have he : MeasurePreserving (fun x:I→ G.El=> v*x) μ μ := measurePreserving_pi _ _ (f:=fun i (x:G.El)=> v i*x) (fun i=>measurePreserving_mul_left _ (v i)); let V(x:I→G.El):=(∏ i,chord.ballDensity r (v i) (x i)) • g x
 have hp : Integrable V μ:= integrableX (scale (vl_cost ..) h) _; rw [entry_at, restore μ μ _ he V hp]; apply integral_congr_ae; apply Eventually.of_forall; intro x; unfold V; apply congrArg (· • g (v*x)); apply Finset.prod_congr rfl; intro i _; unfold chord.ballDensity; rw [Pi.mul_apply, ← chord.left (x i) 1 (v i),mul_one]

end YM.CF.BPress.Law

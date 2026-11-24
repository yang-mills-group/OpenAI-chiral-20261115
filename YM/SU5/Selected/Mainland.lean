import YM.SU5.Selected.Flights
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.WithDensityFinite
/-! # Box approximation machinery
Continuity approximation (on pair links!) despite being built from Borel joint
marks. Handles possible hard step; independent proof on local cover coordinates, no claim that step outputs continuity. On one D support, with one net for any
countably many positions in this hierarchy (use this for ALL s and periods,
no reliance on pressure schedule cost). -/
set_option autoImplicit false
set_option maxRecDepth 3000
set_option synthInstance.maxSize 30000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Tapestry (Swatch render spread daub pigment pigmentLe)
open Theory Set

section func
private lemma smooth_enough (μ:Measure PairsC) [IsFiniteMeasure μ]
    {f:PairsC→ℂ} (p:Measurable f) (D:ℝ)(v:0<D)(hx:∀ x,‖f x‖≤D):
    ∃ u:ℕ→PairsC→ℂ,(∀ n, Continuous (u n)) ∧ (∀ n i,‖u n i‖≤ D) ∧ ∀ᵐ x∂μ, Tendsto (fun n=>u n x) atTop (𝓝 (f x)):=by
  let LpC:= Lp ℂ 1 μ
  have hp:= Measurable.aestronglyMeasurable (μ:=μ) p
  have he:= memLp_top_of_bound hp D (Eventually.of_forall hx)
  let h₁:= he.mono_exponent (show (1:ℝ≥0∞)≤⊤ from le_top)
  let x:= MemLp.toLp f h₁
  haveI : Measure.WeaklyRegular μ := inferInstance
  let F : ContinuousMap PairsC ℂ→L[ℝ] LpC:= ContinuousMap.toLp 1 μ ℝ
  have hv : x∈ closure (range F):= ContinuousMap.toLp_denseRange ℂ μ ℝ ENNReal.one_ne_top _ -- tune `range`
  obtain ⟨u,y,h⟩:= mem_closure_iff_seq_limit.mp hv
  choose g e using y
  have H:= tendstoInMeasure_of_tendsto_Lp h
  obtain ⟨k,w,hh⟩:= H.exists_seq_tendsto_ae
  have hq(n): (u (k n) : PairsC→ℂ) =ᵐ[μ] fun i=>g (k n) i:=by rw [←e]; exact ContinuousMap.coeFn_toLp (p:=1) μ (𝕜:=ℝ) _
  -- radial cutoff (same price even if >0 tiny). All approximants Lipschitz-free and clipped.
  let W(y:ℂ):= (D/(max D ‖y‖)) • y
  have hu : Continuous W := by
    have hz(x:ℂ):max D ‖x‖≠0:=(lt_of_lt_of_le v (le_max_left ..)).ne'; unfold W; fun_prop -- side cond
  have hc(y): W (f y)=f y:=by unfold W; rw [max_eq_left (hx y),div_self v.ne',one_smul]
  refine ⟨fun n i=> W (g (k n) i), fun n=>hu.comp (g (k n)).continuous, fun n i=>?_, ?_⟩
  · dsimp only; let z:= g (k n) i; let d:= max D ‖z‖; have hd:0<d:=lt_of_lt_of_le v (le_max_left ..)
    change ‖(D/d) • z‖ ≤ D; rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left (le_max_right ..) (by positivity : 0≤D/d)).trans_eq (div_mul_cancel₀ _ hd.ne')
  filter_upwards [hh,ae_all_iff.mpr hq,h₁.coeFn_toLp] with y h1 H' h2
  change Tendsto (fun n=>W (g (k n) y)) atTop (𝓝 _)
  have hp : Tendsto (fun n=> u (k n) y) atTop (𝓝 (f y)):=by change x y=f y at h2; rw [←h2]; exact h1
  rw [← hc y]; exact ((hu.tendsto _).comp hp).congr fun i=> congrArg W (H' i)
end func
section pass
variable (S:Finset Cover)
private def gatherInside (x:LinksC):LinksC:=fun k=>if k.1∈ S ∧ k.1+step k.2∈ S then x k else 1
private lemma inside_screen(x:LinksC): Agrees S x (gatherInside S x):=fun e p t=> (if_pos ⟨p,t⟩).symm
private lemma screen_eq{x y:LinksC}(e:Agrees S x y):gatherInside S x=gatherInside S y:= by
  funext i; unfold gatherInside; split_ifs with v; exact e i v.1 v.2; rfl -- tune
private lemma gatherInterior : Continuous (gatherInside S):= by
  apply continuous_pi; intro i; unfold gatherInside; split; exact continuous_apply _; exact continuous_const
variable (s:ℕ)
local notation "J" i:max=>side Y i s
noncomputable abbrev reportChart (a:ℕ)(x:Orbit (side Y a s)):PairsC:= Prod.map (onC (J a)) (onC (J a)) (drawn ((Y.voyage a).CapeT s) x)
private lemma report_m (a:ℕ): Measurable (reportChart Y s a) := (((on_cont _).prodMap (on_cont _)).measurable).comp (drawn_m _ ((Y.voyage a).ownership s).paid.bill)

/-- Land support-paid charts at EVERY course period at level s. -/
lemma cover_pigment (f:Tapestry.Pigment S) (D:ℝ) (hD:0<D)(p:‖f‖≤D):
    ∃ (F:ℕ→Tapestry.Pigment S), (∀ n,Continuous (daub S (F n))) ∧ (∀ n,‖F n‖≤ D) ∧ ∀ a,∀ᵐ x∂city (J a), Tendsto (fun n=> daub S (F n) (reportChart Y s a x)) atTop (𝓝 (daub S f (reportChart Y s a x))) := by
  let R:= Prod.map (gatherInside S) (gatherInside S); have hr:Continuous R:= (gatherInterior S).prodMap (gatherInterior S)
  let W:= daub S f; let U(m:ℕ):Measure PairsC:= (city (J m)).map (R ∘ reportChart Y s m); letI i:∀ (i:ℕ), IsFiniteMeasure (U i):=fun n=> inferInstanceAs (IsFiniteMeasure ((city (J n)).map _))
  let μ:= Measure.sum U; haveI : SFinite μ:= inferInstanceAs (SFinite (Measure.sum U))
  let hp:Measurable W:= (Tapestry.authentic S f).env.meas
  obtain ⟨g,u,hv,e⟩:=smooth_enough μ.toFinite hp D hD (fun i=>(Tapestry.daubLe ..).trans p)
  have he(x:PairsC): W x=W (R x):= (Tapestry.authentic S f).locus _ _ (inside_screen S x.1) (inside_screen S x.2)
  have hμ(m:ℕ): ∀ᵐ z∂(city (J m)), Tendsto (fun i=>g i (R (reportChart Y s m z))) atTop (𝓝 (W (reportChart Y s m z))):= by
    simp_rw [ae_toFinite] at e
    filter_upwards [(Measure.tendsto_ae_map (hr.measurable.comp (report_m Y s m)).aemeasurable).eventually (Measure.ae_sum_iff.mp e m)] with x h ; rw [he]; exact h
  let k (i:ℕ):=g i∘ R
  have ht(i): Continuous (k i):= (u i).comp hr
  have hh (i):Coeff true S (k i):=⟨fun _=>by contradiction, Env.compact (ht i),fun a b t h=>congrArg (g i) (Prod.ext (screen_eq S t) (screen_eq S h))⟩
  refine ⟨fun n=>pigment S (hh n),ht,fun n=>?_,hμ⟩
  apply pigmentLe S _ hD.le; rw [Tapestry.daub_pigment]; exact fun x=> hv n _
variable (f:Swatch S)
lemma present_spool (i:ℕ)(v:Fields (side Y i s)): Tapestry.present Y H s i S f v= ∑ k:Evens S, daub S (f k) (Prod.map (onC (J i)) (onC (J i)) v) • spool (J i) (tagWord S k.val):=castSpool (J i) _ _ v
where castSpool(O:Side)(m:Side) (p:(tent Y H).c m=O) (v:Fields O): Tapestry.arrange _ _ p (Tapestry.appear S K m f) v= ∑ k:Evens S, daub S (f k) (Prod.map (onC O) (onC O) v) • spool O (tagWord S k.val):=by subst O; exact Tapestry.appearSpool ..

lemma movie : ∃ F:ℕ→Swatch S,(∀ a:Side,∀ i,Continuous (render S K (F i) a)) ∧(∀ i,‖F i‖ ≤ ‖f‖+1) ∧ ∀ m:ℕ, ∀ᵐ v∂city (J m),
      let q:=drawn ((Y.voyage m).CapeT s) v
      Tendsto (fun i=> Tapestry.present Y H s m S (F i) q) atTop (𝓝 (Tapestry.present Y H s m S f q)):= by
  let D:=‖f‖+1; have hd:0<D:=by unfold D; positivity
  choose F u v p using (fun x:Evens S=>cover_pigment Y S s (f x) D hd ((norm_le_pi_norm ..).trans (le_add_of_nonneg_right zero_le_one)))
  let F'(n:ℕ):Swatch S:=fun i=> F i n
  have h(m:Side)(i:ℕ):Continuous (render S K (F' i) m):=by
    change Continuous (fun x=> Tapestry.appear S K m (F' i) x); simp_rw [Tapestry.appearSpool]; exact continuous_finsetSum _ fun j _=> ((u ..).comp ((on_cont _).prodMap (on_cont _))).smul continuous_const -- tune metavars
  refine ⟨F',h,fun i=> (pi_norm_le_iff_of_nonneg hd.le).mpr (fun j=>v j i),fun m=> ?_⟩
  filter_upwards [ae_all_iff.mpr (fun x:Evens S=> p x m)] with t r
  dsimp only; simp_rw [present_spool]
  exact tendsto_finsetSum _ fun i _=> Tendsto.smul (show _ from r i) tendsto_const_nhds
end pass
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.movie

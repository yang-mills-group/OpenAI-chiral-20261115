import YM.SatinExist.Prun
/-!
 # Heat-gap boundary on ordered Mink positions. Genuine external phase.
-/
set_option autoImplicit false
set_option maxRecDepth 2450
set_option maxHeartbeats 350000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS OS.Semigroup
open CF.Buffered.Afterglow.Hierarchy.Seld Poin LineDeriv
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j:Axis} (S : OS.Semigroup H j)
local notation "Λ" => 𝓝[>] (0:ℝ)
local notation "E" => elast S
local notation "D" => Bench S
local notation "K" => Cache S
local notation "R" => saucer S
local notation "T" => M S
variable (x:H){n:ℕ}(p:E4)
variable (F G:Fin n→H.Op)
lemma badge_many (i:Fin n)(m:ℕ) : ∃ P:Joint n→L[ℂ] Joint n,∀ F:Fin n→H.Op,∀ f : Joint n, wishL S x p F G f= wishL S x p (badge F i (K m)) G (P f):=by
 induction m with
 | zero=> refine ⟨ContinuousLinearMap.id ℂ _, fun F f=>?_⟩; rw [show badge F i (K 0)=F from (by unfold badge Cache; simp)]; rfl
 | succ m ih=>
   obtain ⟨P,q⟩:= ih
   refine ⟨P.comp (penny j i), fun F f=>?_⟩; rw [badge_one S x p F G i f,q (badge F i R)]; congr 1; unfold badge Cache
   rw [Function.update_self,←mul_assoc,← pow_succ,Function.update_idem]
local notation "ΠY" n:max=> Joint n →L[ℂ] Joint n
lemma badge_all (r:Fin n→ℕ) : ∃ P: ΠY n,∀ F:Fin n→H.Op,∀ f:Joint n,wishL S x p F G f= wishL S x p (fun i=>K (r i)*F i) G (P f):=by
 have he(Q:Finset (Fin n)): ∃ P: ΠY n,∀ F:Fin n→H.Op,∀ f:Joint n,wishL S x p F G f= wishL S x p (fun i=>if i∈ Q then K (r i)*F i else F i) G (P f):=by
    induction Q using Finset.induction_on with
    | empty => exact ⟨ContinuousLinearMap.id ℂ _,fun F f=>by simp⟩
    | @insert i Q h ih=>
        obtain ⟨P,b⟩:= ih; obtain ⟨P',t⟩:= badge_many S x p G i (r i)
        refine ⟨P.comp P', fun F f => ?_⟩
        rw [t F f,b (badge F i (K (r i)))]; let Z:=badge F i (K (r i)); refine DFunLike.congr_fun (congrArg (fun F=> wishL S x p F G) ?_) _; ext1 k; rcases eq_or_ne k i with e|e
        · subst k; simp [Function.update_self,badge,h]
        · simp [Function.update_of_ne,badge,e]
 simpa only [Finset.mem_univ,↓reduceIte] using he Finset.univ
variable (r:Fin n→ℕ)
abbrev cords (h:Fin n→ℝ≥0): Fin n → H.Op:= S.E ∘ h
abbrev slew (r:Fin n→ℕ) (h:Fin n→ℝ≥0): Fin n→H.Op:= fun i=> Par S (r i) (h i)
variable {Q:Type*}[TopologicalSpace Q]
lemma activated {f:Q→H.space}(g:Q→ Fin n→ℝ≥0)(w:∀ i,Continuous fun y=> g y i)(d:Continuous f)(y:Fin n→E4): Continuous fun z=> regiaN S (f z) n (S.E ∘ g z) G p y:=by
 induction n generalizing p with
 | zero=> exact d
 | succ n ih=>
    simp_rw [regiaN,comp_apply]; let T'(z:Q):= Fin.tail (g z); let Y'(z:Q):= regiaN S (f z) n (S.E ∘ T' z) (Fin.tail G) (y 0) (Fin.tail y)
    have he:Continuous Y':= ih (y 0) (Fin.tail G) T' (fun i=> w i.succ) (Fin.tail y) -- order
    have hh:Continuous (fun z:Q=> S.E (g z 0) (G 0 (Y' z))):= (duet S).comp (((G 0).continuous.comp he).prodMk (w 0)); exact (M S _).continuous.comp hh
-- No number of scales compatibility premise
lemma cold_open (f:Joint n)(C : Fin n → ℝ≥0): ContinuousAt (fun h:Fin n→ℝ≥0=> wishL S x p (cords S h) G f) C:=by
 obtain ⟨L,l⟩:=Finite.bddAbove_range (fun i:Fin n=>‖G i‖)
 let D':=(max 0 L)^n*‖x‖; let d(h:Fin n→ℝ≥0)(z:Points n):= f z • regia S x p (cords S h) G z
 simp_rw [wishL_eq]; let O(z:Points n):= ‖f z‖*D'
 apply (show ContinuousAt (fun h=>∫ z,d h z) _ from tendsto_integral_filter_of_dominated_convergence O (Eventually.of_forall (fun h=> (regiaI ..).aestronglyMeasurable)) (Eventually.of_forall fun h=> Eventually.of_forall fun z=> ?_) (f.integrable.norm.mul_const D') (Eventually.of_forall fun z=>?_))
 · dsimp only [d]; rw [norm_smul]; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
   exact regia_nrm S x (cords S _) _ (max 0 L) (fun u=> ((mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _)).trans ((l (mem_range_self u)).trans (le_max_right ..)))) (le_max_left ..) p _
 change Tendsto (fun h=>d h z) _ _; exact (((activated S p G (f:=fun _=>x) id (fun i=> (continuous_apply i)) continuous_const z.ofLp).continuousAt).tendsto.const_smul _)

-- actual tube estimate, ANY approach from full compact inside to boundary.We take gap real shifts; same Proof for tending complex (real Mink part is a translation).
abbrev Margins (n:ℕ): Set (Fin n→ℝ≥0):= {z|∀ i,0<z i}
lemma margin_here : NeBot (𝓝[Margins n] (0: Fin n→ℝ≥0)):=by
 let g(t:ℝ≥0):Fin n→ℝ≥0 := fun _=>t; have hc:Continuous g:=continuous_pi (fun i=>continuous_id); have H:Tendsto g (𝓝[>] (0:ℝ≥0)) (𝓝[Margins n] (0:Fin n→ℝ≥0)):= tendsto_nhdsWithin_iff.mpr ⟨(show Tendsto g (𝓝 0) (𝓝 (g 0)) from hc.tendsto 0).mono_left nhdsWithin_le_nhds,(show ∀ᶠ i:ℝ≥0 in 𝓝[>] 0, 0 < i from self_mem_nhdsWithin).mono fun y p i=> p⟩; exact H.neBot
abbrev RoadLimit (Y: Joint n→L[ℂ] H.space):Prop:= ∀ f:Joint n,Tendsto (fun h=> wishL S x p (slew S r h) G f) (𝓝[Margins n] (0:Fin n→ℝ≥0)) (𝓝 (Y f))
lemma boundary_R : ∃ Y: Joint n→L[ℂ] H.space,RoadLimit S x p G r Y:=by
 obtain ⟨P,e⟩:= badge_all S x p G r
 let Z:= wishL S x p (cords S (0:Fin n→ℝ≥0)) G
 refine ⟨Z.comp P, fun f=> (show Tendsto _ _ (𝓝 (Z (P f))) from (cold_open S x p G (P f) 0).tendsto.mono_left nhdsWithin_le_nhds)|>.congr' ?_⟩
 filter_upwards [self_mem_nhdsWithin] with y d; refine (e (slew S r y) f|>.trans ?_).symm; have he:(fun i=> K (r i)*(slew S r y i))= cords S y:=funext fun i=> P_Heq S (y i) (r i) (d i)
 rw [he]
-- analytic all gap parameters. FREE independent variation ---- decide use complex coords fin.
lemma regia_ana (y:Fin n→E4) {Q:Type} [NormedAddCommGroup Q][NormedSpace ℂ Q](u:Q)(A:Q→Fin n→H.Op)(h:∀ i:Fin n,AnalyticAt ℂ (fun z=> A z i) u): AnalyticAt ℂ (fun z=> regiaN S x n (A z) G p y) u:=by
 induction n generalizing p with
 | zero=> exact analyticAt_const
 | succ n ih=>
    simp only [regiaN]; let F(z:Q):= Fin.tail (A z); let V(z:Q):= regiaN S x n (F z) (Fin.tail G) (y 0) (Fin.tail y); let z:=T (y 0 - p)
    have hv: AnalyticAt ℂ V u:= ih (y 0) _ (Fin.tail y) F (fun i=> h i.succ)
    let B:H.space →L[ℂ] H.Op →L[ℂ] H.space:=ContinuousLinearMap.apply ℂ H.space; have hQ:AnalyticAt ℂ (fun i=> A i 0 (G 0 (V i))) u:= B.analyticAt_bilinear _ |>.comp (((G 0).analyticAt _|>.comp hv).prod (h 0)); exact (z.analyticAt _).comp hQ
end YM.SatinJets

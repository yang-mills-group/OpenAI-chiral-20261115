import GaugeFieldConstruction.Tidings
import GaugeFieldConstruction.Proton
import GaugeFieldConstruction.Depot
import YM.Work.A15
/-!
# Average on SO, infinitesimal-invariant inner product from the free *active* corner
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Apit
open Stage Angles Matrix Function Filter Set MeasureTheory Module Fathom Sailing
open scoped Topology Matrix Matrix.Norms.Frobenius BigOperators InnerProductSpace ContDiff

-- physical not using all O(4). Needs Compact & measure
local instance closedR : CompactSpace Stage.SO:= by
  letI : CompactSpace Ortho := YM.Work.A15.compact_ortho
  apply isCompact_iff_compactSpace.mp
  have t : Continuous fun i: Ortho=> i.val.det:=continuous_subtype_val.matrix_det -- check
  have he :(Stage.orbit:Set Ortho)={p| p.val.det=1}:= Set.ext fun i=>covers_all i
  rw [he]; exact (isClosed_eq t continuous_const).isCompact

local instance : SecondCountableTopology Stage.SO:= by
  haveI : SecondCountableTopology M4:= inferInstanceAs (SecondCountableTopology (Axis→Axis→ℝ))
  haveI : SecondCountableTopology Ortho:= inferInstanceAs (SecondCountableTopology ↥((Matrix.unitaryGroup Axis ℝ:Set M4)))
  exact inferInstanceAs (SecondCountableTopology ↥((Stage.orbit:Set Ortho)))
local instance : MeasurableSpace Stage.SO := borel Stage.SO
local instance : BorelSpace Stage.SO:=⟨rfl⟩
private def freeze : TopologicalSpace.PositiveCompacts Stage.SO:=⟨⟨Set.univ,isCompact_univ⟩,by simp⟩
private def μ : Measure Stage.SO:= Measure.haarMeasure freeze
local instance : μ.IsHaarMeasure:=by unfold μ; infer_instance
local instance : IsProbabilityMeasure μ:= ⟨Measure.haarMeasure_self⟩ -- adjust

variable {X Y Z:Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z] {t :ℝ}
def Price (f:ℝ→X) (t:ℝ) (d:X): Prop:=∀ L:X→ₗ[ℝ]ℝ,HasDerivAt (L ∘ f) (L d) t
namespace Price
variable {p:ℝ→X} {q:ℝ→Y} {x:X} {y:Y}
lemma map (h:Price p t x) (T:X→ₗ[ℝ]Y) : Price (fun i=>T (p i)) t (T x):= fun L=> h (L ∘ₗ T)
lemma stone (x:X): Price (fun _:ℝ=>x) t 0:=fun L=>by unfold Function.comp; rw [map_zero]; exact hasDerivAt_const ..
lemma plus {g:ℝ→X} {z} (h: Price p t x) (u:Price g t z): Price (fun j=> p j+g j) t (x+z):= fun L=>by simp only [comp_def,map_add]; exact (h L).add (u L)
lemma perigee (h:Price p 0 x): Price (fun i=> p (-i)) 0 (-x):= fun L=> by
  have g := (hasDerivAt_id' (0:ℝ)).neg
  have u :HasDerivAt (L ∘ p) (L x) (-(0:ℝ)):=by rw [neg_zero]; exact h L
  have e:= HasDerivAt.comp (0:ℝ) (h:=fun s:ℝ=> -s) u g -- adjust
  simpa [Function.comp_def] using! e

lemma product [Module.Finite ℝ X] (h:Price p t x) (u:Price q t y) (W:X→ₗ[ℝ]Y→ₗ[ℝ]Z): Price (fun s=>W (p s) (q s)) t (W x (q t)+W (p t) y):= by
  intro L; let b:=Module.finBasis ℝ X; let I:=Fin (Module.finrank ℝ X)
  have e (x:X) (y:Y):L (W x y)= ∑ i:I,b.coord i x*L (W (b i) y):=by
    conv_lhs=> rw [← b.sum_repr x,map_sum,LinearMap.sum_apply,map_sum]
    exact Finset.sum_congr rfl fun s _=>by rw [map_smul,LinearMap.smul_apply,map_smul]; rfl
  have E i: HasDerivAt (fun s=> (b.coord i (p s))*L (W (b i) (q s))) (b.coord i x*L (W (b i) (q t))+b.coord i (p t)* L (W (b i) y)) t := (h (b.coord i)).mul (u (L ∘ₗ (W (b i))))
  rw [map_add,e x,e (p t) y, ← Finset.sum_add_distrib]; rw [show (⇑L ∘ fun s=> W (p s) (q s)) = (fun s=> ∑ i:I,b.coord i (p s)*L (W (b i) (q s))) from funext fun s=> e _ _]; exact HasDerivAt.fun_sum fun i _=> E i
lemma self {p:ℝ→ℝ} {x}:Price p t x→ HasDerivAt p x t:=fun h=>h LinearMap.id
-- weak test synthesis
lemma collect [Module.Finite ℝ X] {I:Type*} (P : X→ₗ[ℝ]I→ℝ) (v:Injective P) (h:∀ i,HasDerivAt (fun s=>P (p s) i) (P x i) t): Price p t x:= by
  intro L
  have H :L∈Submodule.span ℝ (Set.range (feel P)):= replaces P v ▸ Submodule.mem_top
  refine Submodule.span_induction (p:=fun (L:X→ₗ[ℝ]ℝ) _=> HasDerivAt (L ∘ p) (L x) t) ?_ ?_ ?_ ?_ H
  · rintro _ ⟨i,rfl⟩; exact h i
  · exact hasDerivAt_const t 0
  · intro f g _ _ v w; exact v.add w
  intro a g _ v; exact v.const_smul a
end Price

section
variable [Module.Finite ℝ X] (Y:Tour X) (R:Stage.SO→*Endr X) (h:∀ g: X→ₗ[ℝ]ℝ, ∀ v,Continuous fun p:Stage.SO=>g (R p v))

private def pr (p:Stage.SO) (x:X):=pixels ℝ X (R p⁻¹ x)
private lemma pr_add (p:Stage.SO) (x y:X): pr R p (x+y)= pr R p x+pr R p y:=by simp [pr]
private lemma pr_c (p:Stage.SO) (x:X) (r :ℝ):pr R p (r • x)=r • pr R p x:= by simp [pr]
include h
private lemma oracle (x y:X): Integrable (fun p:Stage.SO=> inner ℝ (pr R p x) (pr R p y)) μ:= by
  have e (x:X):Continuous (fun p=> pr R p x):=by
    refine continuous_iff_continuousAt.mpr (fun z=>?_); apply (angel (F:=ℝ) _ _).mp
    intro g; exact (h (g ∘ₗ (pixels ℝ X).toLinearMap) x).continuousAt.comp (continuous_inv.continuousAt (x:=z))
  exact ((e x).inner (𝕜:=ℝ) (e y)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private def pay₁ : X →ₗ[ℝ] X →ₗ[ℝ] ℝ:= LinearMap.mk₂ ℝ (fun x y:X=> ∫ p:Stage.SO, inner ℝ (pr R p x) (pr R p y) ∂μ)
  (fun x y z=>by simp_rw [pr_add,inner_add_left,integral_add (oracle R h ..) (oracle R h ..)])
  (fun a x y=> by simp_rw [pr_c,real_inner_smul_left,integral_const_mul]; rfl)
  (fun x y z=>by simp_rw [pr_add,inner_add_right,integral_add (oracle R h ..) (oracle R h ..)])
  (fun a x y => by simp_rw [pr_c,real_inner_smul_right,integral_const_mul]; rfl) -- need `h` variable on def explicitly
omit [Module.Finite ℝ X] h in
lemma crest (u : G): Angles.rise u 0=1:=Subtype.ext (_root_.YM.Work.A13.oneParameter_zero _)
private lemma have_px (a:Stage.SO) (x y):pay₁ R h (R a x) (R a y)=pay₁ R h x y := by
  change (∫ p:Stage.SO, inner ℝ (pr R p _) (pr R p _) ∂μ)=∫ p:Stage.SO,inner ℝ (pr R p x) (pr R p y) ∂μ
  rw [← (measurePreserving_mul_left μ a).integral_comp (Homeomorph.mulLeft a).measurableEmbedding]
  have hP (p v): pr R (a*p) (R a v)=pr R p v:= by unfold pr; rw [_root_.mul_inv_rev,map_mul,Module.End.mul_apply,again']
  exact integral_congr_ae (Eventually.of_forall fun v=>by change inner ℝ (pr R (a*v) _) (pr R (a*v) _) =_; rw [hP,hP])
def moon (V:∀ i:G,∀ x,Price (fun t:ℝ=>R (Angles.rise i t) x) 0 (Y i x)): Dome Y where
  form:=pay₁ R h
  sym a b:= integral_congr_ae (Eventually.of_forall fun i=>real_inner_comm (pr R i b) (pr R i a)) -- adjust
  pos x p:=by
    have ht (i):pr R i x≠0:=fun e=> p (by
      have u:R i⁻¹ x=0:= (pixels ℝ X).injective (e.trans (map_zero _).symm)
      rw [← again R i x,u,map_zero])
    have E i:= real_inner_self_pos.mpr (ht i)
    refine (integral_pos_iff_support_of_nonneg (μ:=μ) (f:=fun i:Stage.SO=> inner ℝ (pr R i x) (pr R i x)) (fun i=>(E i).le) (oracle R h x x)).mpr ?_
    rw [show support (fun i=>inner ℝ (pr R i x) (pr R i x))=Set.univ from Set.eq_univ_of_forall fun i=> (E i).ne']; simp
  neg i x y:= by
    have H:= Price.self ((V i x).product (V i y) (pay₁ R h))
    simp_rw [crest,map_one,Module.End.one_apply] at H -- actual rewrite at t? 
    have u :HasDerivAt (fun t:ℝ=> pay₁ R h (R (Angles.rise i t) x) (R (Angles.rise i t) y)) 0 0:=by simp_rw [have_px R h]; exact hasDerivAt_const ..
    exact eq_neg_of_add_eq_zero_left (H.unique u)
end
end YM.GaugeFieldConstruction.Apit

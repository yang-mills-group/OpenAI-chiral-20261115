import YM.CF.BPress.Wealth.Vertical
/-! Angular real orthonormal space and linear support estimates (`eq:B-Hess`). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ContDiff
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)
abbrev Axon := X.Air × group.ColorIndex
abbrev RaySpace:= EuclideanSpace ℝ (Axon X)
abbrev BEnd:= RaySpace X →L[ℝ] RaySpace X

def lead : RaySpace X ≃ₗ[ℝ] Bills X ink where
 toFun w i:= WithLp.toLp 2 (fun x=> w (i,x))
 invFun w:= WithLp.toLp 2 (fun i=> w i.1 i.2)
 left_inv x:= by apply PiLp.ext; intro v; rfl
 right_inv x:=by ext; rfl
 map_add' x y:=by ext; rfl
 map_smul' c x:=by ext; rfl
lemma ray_price (w:RaySpace X) : ‖w‖^2=∑ i:X.Air, ‖lead X w i‖^2:=by
 rw [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; exact (EuclideanSpace.norm_sq_eq (lead X w i)).symm
lemma lampH (w:RaySpace X)(i:X.Air) : ‖lead X w i‖ ≤ ‖w‖ := by
 apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg w)).mp; rw [ray_price]; exact single_le_sum (f:=fun i=> ‖lead X w i‖^2) (fun i _=> sq_nonneg _) (mem_univ _)

-- norm-preserving rearrangements for Gauss measures eventually.
def keepOnly (S:Finset X.Hcols) (w:RaySpace X) : RaySpace X:= WithLp.toLp 2 (fun i:Axon X=>if i.1.1∈S then w i else 0)
lemma stay (S: Finset X.Hcols)(w:RaySpace X)(t:X.Air): lead X (keepOnly X S w) t=if t.1∈ S then lead X w t else 0:= by
 apply PiLp.ext; intro i; split; next k=>exact if_pos k -- tune direction order rewriting inside pair product
 next k=>exact if_neg k
def keeper (S:Finset X.Hcols) : BEnd X:= (show RaySpace X→ₗ[ℝ] RaySpace X from {
 toFun:=keepOnly X S
 map_add' x y:=PiLp.ext fun i=>by by_cases h:i.1.1∈S<;> simp [keepOnly,h]
 map_smul' c x:=PiLp.ext fun i=>by by_cases h:i.1.1∈ S<;> simp [keepOnly,h] }).toContinuousLinearMap
lemma tally_ray (S:Finset X.Hcols)(x:RaySpace X) : ‖keepOnly X S x‖^2= ∑ i:X.Air, (if i.1∈S then ‖lead X x i‖^2 else 0):=by rw [ray_price]; refine sum_congr rfl fun i _=>?_ ; rw [stay]; split; rfl; simp
lemma ray_mask (S:Finset X.Hcols)(x y:RaySpace X) : inner ℝ (keepOnly X S x) y=inner ℝ x (keepOnly X S y):=by simp only [PiLp.inner_apply]; refine sum_congr rfl fun i _=>?_ ; unfold keepOnly; by_cases h:i.1.1∈ S <;> simp [h]
lemma id_mask (S:Finset X.Hcols)(x:RaySpace X): keepOnly X S (keepOnly X S x)=keepOnly X S x:= by ext i; by_cases p:i.1.1∈S<;> simp [keepOnly,p]
lemma mask_norm (S:Finset X.Hcols)(x:RaySpace X): inner ℝ x (keepOnly X S x)= ‖keepOnly X S x‖^2:= by rw [← real_inner_self_eq_norm_sq,ray_mask, id_mask]
lemma mask_add (S:Finset X.Hcols)(x:RaySpace X) : x= keepOnly X S x+keepOnly X Sᶜ x:=by ext i; by_cases h:i.1.1∈ S<;> simp [keepOnly,h]
-- Seal sees linear map formR evaluated only within data it owns (including full formal variables).
variable {X}
lemma weight_price (d:Clip) (j:Root s) : 0≤ wgt d j:=by cases j; exact d.quadratic_pos.le; exact chPrice_pos.le
lemma direct_price (d:Clip)(j:Root s) : wgt d j ≤ d.direct+chPrice:=by cases j; exact le_add_of_nonneg_right chPrice_pos.le; exact le_add_of_nonneg_left d.quadratic_pos.le
variable (M:ℕ)(R:PathData group){d:Clip}{σ C Λ:ℝ}{u v : Directions group s}
lemma aperture_cur {t:Signed}{j:Bonding s}(p:∀ i:Fin 4, u (address t (aperture j i)) = v (address t (aperture j i))) : orbitP t j u=orbitP t j v:=congrArg circle (funext fun i=> show brandW t u j i= brandW t v j i from by unfold brandW orbitW; rw [p])
lemma form_local (i:Root s)(p: Set.EqOn u v (tickets M i)): form R M i u=form R M i v:=by
 rcases i with i|⟨a,i⟩; · exact aperture_cur fun j=> by rw [addr_id]; exact p (mem_image_of_mem (aperture i) (mem_univ j))
 apply tsum_congr; intro j; unfold prime; split; next k=> refine congrArg (fun x:ink=>(R.row i.2 j).1 • x) (aperture_cur (fun x=> p (door_leg M (R.row i.2 j).2 a i.1 k x))) -- tune (explicit)
 next=> simp
lemma shape_seen (i:Root s)(p:retained X M i)(h:High B M)(x y:Bills X ink)(v:∀ j:X.Air,j.1∈danger X M i→ x j=y j) : form R M i (canon X x)=form R M i (canon X y):= form_local M R _ (canon_agrees X M i h p x y fun j t=> v j t)

variable (X) (H : R.Bounds d σ C Λ)
include H
lemma shape_zero (i:Root s): form R M i 0=0:=by
 rcases i with i|⟨t,i⟩; exact map_zero _; have he:= base_lin M t R H i (0:Directions group s) 0; simpa [form] using he
lemma shape_add (i:Root s)(x y:Directions group s): form R M i (x+y)=form R M i x+form R M i y:=by
 rcases i with i|⟨t,i⟩; exact map_add ..; have he:=base_lin M t R H i (x+y) y; rw [add_sub_cancel_right] at he; exact ((eq_sub_iff_add_eq ..).mp he).symm -- tune
lemma shape_smul (i:Root s)(k:ℝ)(x:Directions group s): form R M i (k • x)= k • form R M i x:=by cases i with| inl i=> exact map_smul ..| inr j=> exact base_smul M _ R H k j.2 x
-- binder proof dependence must include explicitly for def
omit H
def shine (H:R.Bounds d σ C Λ) (i:Root s) : RaySpace X →L[ℝ] ink := (show RaySpace X →ₗ[ℝ] ink from {
 toFun w:= form R M i (canon X (lead X w))
 map_add' x y:=by rw [map_add,map_add,shape_add M R H]
 map_smul' x y:=by rw [map_smul,map_smul,shape_smul M R H,RingHom.id_apply]
 }).toContinuousLinearMap
variable {X}
def coefH (M:ℕ)(C:ℝ) := 4*(1+C)
include H
lemma range_price (x:Root s)(y:Directions group s)(t:ℝ)(q:∀ i: Link s,‖y i‖≤t) : ‖form R M x y‖ ≤ coefH M C*t:= by
 have he:=budget_nonneg H.three; have ht:0≤t:=(norm_nonneg _).trans (q (0,0)); rcases x with x|⟨v,x⟩; apply (psi_norm 1 q x).trans; unfold coefH; nlinarith
 apply (baseT M v R H x y t q).trans; unfold coefH; nlinarith
lemma beaming (x:Root s)(p:retained X M x)(t:High B M)(w:RaySpace X): let S:= danger X M x; shine X M R H x (keepOnly X S w)=shine X M R H x w := by
 intro S; refine shape_seen M R x p t (lead X _) (lead X w) ?_; intro i u; rw [stay]; exact if_pos u
lemma shine_price (x:Root s)(p:retained X M x)(t:High B M)(w:RaySpace X) : ‖shine X M R H x w‖ ≤ coefH M C*‖keepOnly X (danger X M x) w‖:=by
 rw [← beaming M R H x p t w]; refine range_price M R H x _ _ (fun i=>?_ ); exact raw_le (norm_nonneg _) _ (fun i=> lampH X (keepOnly X _ w) i) _ -- tune arg order H X M etc
end YM.CF.BPress.Wealth

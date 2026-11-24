import YM.CF.Rush.Livery
import YM.CF.Drapes.Awash
import YM.CF.Lattice.FrameFee
/-! Ambient analytic sector domain. Enlarged link ports (orientation + matter replica) for differentiation. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tulip
open Fir Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N P:Side}
abbrev Twig := Op Slot × Op SU.F
abbrev Stem (N:Side) := Edge (Site N) → Bool → Twig

def brand (x:E) : Twig := ((matter x).val,(firstF x).val)
lemma brand_one : brand 1=1:=by unfold brand; simp
lemma brand_mul (x y:E):brand (x*y)=brand x*brand y:=by simp only [brand,map_mul]; rfl
lemma brand_inv (x:E):brand x⁻¹=star (brand x):=by simp only [brand,map_inv]; rfl
lemma brand_unit (x:E):brand x∈unitary Twig:=⟨Prod.ext (matter x).property.1 (firstF x).property.1,Prod.ext (matter x).property.2 (firstF x).property.2⟩
lemma brand_norm (x:E): ‖brand x‖=1:=by rw [Prod.norm_def, show ‖(brand x).1‖=1 from CStarRing.norm_of_mem_unitary (matter x).property, show ‖(brand x).2‖=1 from CStarRing.norm_of_mem_unitary (firstF x).property,max_self]
def profile (U:Bkg N):Stem N:=fun i h=> if h then brand (U i) else star (brand (U i))
lemma profile_trivial : profile (1:Bkg N)=1:=by funext i h; cases h <;> simp [profile,brand_one]
def relayg (t : Site N→E)(W:Stem N):Stem N:=fun ⟨x,i⟩ u=> if u then brand (t x)*W (x,i) u*star (brand (t (x+step i))) else brand (t (x+step i))*W (x,i) u*star (brand (t x))
lemma profile_g (t:Site N→E)(U:Bkg N):profile (gauge t U)=relayg t (profile U):=by
  funext ⟨x,i⟩ u; cases u <;> simp [profile,relayg,Lattice.gauge,brand_mul,brand_inv,mul_assoc]
lemma brand_lef (x:E)(p:Twig): ‖brand x * p‖=‖p‖:=by let u:unitary Twig:=⟨_,brand_unit x⟩; exact CStarRing.norm_coe_unitary_mul u p
lemma brand_rig (x:E)(p:Twig): ‖p*star (brand x)‖=‖p‖:=by rw [← brand_inv]; let u:unitary Twig:=⟨_,brand_unit x⁻¹⟩; exact CStarRing.norm_mul_coe_unitary p u
lemma relayg_eq (t:Site N→E)(x y:Stem N): ‖relayg t x-relayg t y‖=‖x-y‖:=by
  have hh (z k) : ‖(relayg t x-relayg t y) z k‖=‖(x-y) z k‖:=by obtain ⟨z,l⟩:=z; cases k <;> simp [relayg,← sub_mul,← mul_sub,brand_lef,brand_rig]
  apply le_antisymm <;> refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=> (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun u=>?_
  · rw [hh]; exact le_trans (norm_le_pi_norm ((x-y) i) u) (norm_le_pi_norm (x-y) i)
  rw [← hh]; exact le_trans (norm_le_pi_norm ((relayg t x-relayg t y) i) u) (norm_le_pi_norm (relayg t x-relayg t y) i)

def Openc (N:Side)(δ:ℝ):Set (Stem N):= {x|∃ U:Bkg N, Guard U δ ∧ ‖x-profile U‖<δ}
lemma openc (N:Side)(e:ℝ) : IsOpen (Openc N e):=by rw [show Openc N e= ⋃ U : {U:Bkg N//Guard U e}, Metric.ball (profile U.val) e by ext x; simp [Openc,Metric.mem_ball,dist_eq_norm]]; exact isOpen_iUnion fun _=> isOpen_ball
lemma filt' (x:Stem N) (e f:ℝ) (h:x∈Openc N e)(l:e≤f): x∈Openc N f:=by obtain ⟨U,h,v⟩:=h; exact ⟨U,h.shrink l,v.trans_le l⟩
lemma o_act (t:Site N→E)(x:Stem N)(e:ℝ)(hx:x∈Openc N e): relayg t x∈Openc N e:=by obtain ⟨U,h,f⟩:=hx; exact ⟨gauge t U,h.cov t,by rwa [profile_g,relayg_eq]⟩
lemma guard0 {e:ℝ}(h:0≤e) : Guard (1:Bkg N) e :=by constructor <;> intro i j k _ <;> simpa [square,travel]
lemma vacancy0 (e:ℝ)(h:0<e): (1:Stem N)∈Openc N e:=⟨1,guard0 h.le,by simpa [profile_trivial]⟩
lemma seasonal (e:ℝ)(x:Stem N)(h:x∈Openc N e)(i u): ‖x i u‖≤1+e:=by
  obtain ⟨U,h,k⟩:= h; apply (norm_le_norm_sub_add _ (profile U i u)).trans
  have hv : ‖(x-profile U) i u‖≤e:= (le_trans (norm_le_pi_norm ((x-profile U) _) _) (norm_le_pi_norm _ _)).trans k.le
  have hm : ‖profile U i u‖=1:=by cases u <;> simp [profile,norm_star,brand_norm]
  rw [hm,add_comm (1:ℝ)]; exact add_le_add hv le_rfl

def fare (S : Seal (Site N))(x y:Stem N):ℝ := ∑ i∈leaks S, ‖x i-y i‖
lemma fare_inc {S T: Seal (Site N)} (h:S⊆T)(x y:Stem N) : fare S x y ≤ fare T x y:= by
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi=> Finset.mem_filter.mpr ⟨Finset.mem_univ _,h (Finset.mem_filter.mp hi).2.1,h (Finset.mem_filter.mp hi).2.2⟩) (fun _ _ _=> norm_nonneg _)
lemma fare_t (S:Seal (Site N))(x y:Stem N): 0≤fare S x y:=by unfold fare; positivity

def affair {I:Type*}(e:ℝ)(p:I→Site N): Stage (Site N) I ↥(Openc N e) (Site N→E):=
 ⟨terr N,p,fun t x=> ⟨_,o_act t x _ x.property⟩,fun S x y=> fare S x y/|e|,fun S x y=>div_nonneg (fare_t ..) (abs_nonneg _),fun h x y=> div_le_div_of_nonneg_right (fare_inc h x.val y.val) (abs_nonneg _)⟩

def ice (x: Stem N) : Stem N:=fun i u=>star (x i (!u))
lemma ice_pr (U:Bkg N): ice (profile U)=profile U:=by funext i u; cases u <;> simp [profile,ice]
lemma ice_f (S: Seal (Site N))(x y: Stem N) : fare S (ice x) (ice y)=fare S x y:=by
  apply Finset.sum_congr rfl; intro i _
  -- sup distance at each bool
  apply le_antisymm <;> refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k=>?_
  · simp only [Pi.sub_apply,ice,←star_sub,norm_star]; exact norm_le_pi_norm (x i-y i) _
  have h:=norm_le_pi_norm (ice x i-ice y i) (!k); simp only [Pi.sub_apply,ice,Bool.not_not, ← star_sub,norm_star] at h; exact h
lemma ice_norm (x y: Stem N) : ‖ice x-ice y‖=‖x-y‖:=by
  apply le_antisymm <;> refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=> (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k=> ?_
  · simp only [Pi.sub_apply,ice,←star_sub,norm_star]; exact le_trans (norm_le_pi_norm (x i-y i) _) (norm_le_pi_norm (x-y) _)
  have h:=norm_le_pi_norm (ice x i-ice y i) (!k); simp only [Pi.sub_apply,ice,Bool.not_not, ← star_sub,norm_star] at h; exact h.trans (norm_le_pi_norm (ice x-ice y) i)
lemma ice_o (x: Stem N)(e:ℝ)(h:x∈Openc N e):ice x∈Openc N e:=by obtain ⟨U,h,k⟩:=h; exact ⟨U,h,by rw [← ice_pr,ice_norm]; exact k⟩
end YM.CF.Tulip

import YM.SU5.Selected.Concert
import YM.SU5.Selected.Dilation
/-! # Boundary responses on the true operator spaces
Fixed supports only. Norm estimate from smooth Passage to limit in
operator norm (`transfer_limit` via stretch) and period a.e convergence.
Hence strong enough for selecting curvature-probes, gauge-density etc.
Does not prove spacetime translation continuity. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
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
open Tapestry (Swatch render render_fabric fabric texture spread)
open Set
variable (S:Finset Cover) (s:ℕ)
local notation "R"=>wingspan Λ l S
local notation "rx"=>render S K
local notation "ry"=>render R K
local notation "Tx"=>transfer Y H G S s
local notation "Lt" r:max=>i (G.rows r)

/-- Any pointwise-null on participating tori/eventual positions along this
history, suffices for ALL box operators and selected components. A.e.
for each period with **city** including joint Loom. -/
def Dues (f:ℕ→Family (tent Y H)) : Prop :=
  ∀ᶠ r:ℕ in atTop,∀ᵐ x:Orbit (side Y ((i) (G.rows r)) s) ∂city (side Y ((i) (G.rows r)) s),
    Tendsto (fun n=> Tapestry.exhibit Y H s ((i) (G.rows r)) (f n) (drawn ((Y.voyage ((i) (G.rows r))).CapeT s) x)) atTop (𝓝 0)
include V in
lemma respond (f:ℕ→Swatch S) (A':ℝ)(p:∀ n,‖f n‖≤A')(h:Dues Y H G s (rx ∘ f)): Tendsto (Tx ∘ f) atTop (𝓝 0) := by
  have hx:Tendsto (i ∘ G.rows) atTop atTop:= (V.pick.grow_i.comp G.history.growsA).tendsto_atTop
  let F (r:ℕ):=Tapestry.coupon Y H S s (Lt r) (k (G.columns r))
  have he:Tendsto F atTop (𝓝 Tx):= transfer_limit Y H V G S s
  have hv:∀ᶠ r:ℕ in atTop,Tapestry.Spanned Y S s (Lt r) (k (G.columns r)):= by
    filter_upwards [G.history.finance (s+1),hx.eventually (Tapestry.seasons Y H S s)] with t p v; exact ⟨⟨p.depth,p.enters⟩,v⟩
  have hu: 0≤ A':=(norm_nonneg _).trans (p 0)
  refine Metric.tendsto_nhds.mpr fun ε g=> ?_
  let δ:= ε/2/(A'+1); have hp:0<δ:=by unfold δ; positivity
  obtain ⟨r,v,t,e⟩:= (((Metric.tendsto_nhds (a:=Tx)).mp he δ hp).and (hv.and h)).exists
  have ht:= Tapestry.dilationFixed Y H S s (Lt r) (k (G.columns r)) t (f:=f) _ p e
  filter_upwards [Metric.tendsto_nhds.mp ht (ε/2) (by positivity)] with n m
  change dist (F r (f n)) 0 < _ at m
  apply lt_of_le_of_lt (dist_triangle _ (F r (f n)) _) _
  rw [dist_eq_norm, Function.comp_apply, norm_sub_rev]; rw [dist_eq_norm (F r) (Tx)] at v
  let Z:= F r-(Tx)
  have hl:‖Z‖*(‖f n‖)≤ δ*A':= mul_le_mul v.le (p n) (norm_nonneg _) hp.le
  have hh:δ*A'<ε/2:=lt_of_lt_of_le (mul_lt_mul_of_pos_left (lt_add_one A') hp) (div_mul_cancel₀ (ε/2) (by positivity : A'+1 ≠ 0)).le
  have hq: ‖F r (f n)-(Tx) (f n)‖≤ ‖Z‖ * ‖f n‖:= Z.le_opNorm _
  linarith

section op
variable (Tc:Arena Y H G.history.circuit j 0 false)
local notation "ϕ" S:max v:max=>allCap Y H V G j S v Tc
lemma sealStep (f:Swatch S) : (ϕ S s) f=(ϕ (R) (s+1)) (Tx f) := by
  let g:=chartFamily Y H false S (allHues Y H S f)
  let h:=upward Y H G.history false g s 1
  rw [capₐ Y H V G j S s Tc f g rfl,capₐ Y H V G j (R) (s+1) Tc (Tx f) h]
  · apply Subtype.ext; convert (Vacancy.cap_level (F:=g) Y H V s G.history G.clipped j false Tc (s+1) (by omega)).symm using 1
    · rfl
    rw [show s+1-s=1 from by omega]; rfl
  exact transferred ..

lemma responsiveCap (f:ℕ→Swatch S)(A':ℝ)(p:∀ i,‖f i‖≤A')(h:Dues Y H G s (rx ∘ f)) : Tendsto (fun n=>(ϕ S s) (f n)) atTop (𝓝 0):=by
  simp_rw [sealStep Y H V G j S s Tc] -- loops? same S
  have he: (ϕ (R) (s+1)) 0=0:= (ϕ (R) (s+1)).map_zero; exact he ▸ ((ϕ (R) (s+1)).continuous.tendsto 0|>.comp (respond Y H V G S s f A' p h))
lemma at_r (f:ℕ→Family (tent Y H))(g: Family (tent Y H))(hg:InTest K true S false g) {A':ℝ} (p:∀ i, InTest K true S false (f i))(hp:∀ i,pay (f i-g) A')(h:Dues Y H G s (fun i=>f i-g)) :
    Tendsto (fun n=>seal₀ Y H V G j false Tc s (observe (aux_test (p n)))) atTop (𝓝 (seal₀ Y H V G j false Tc s (observe (aux_test hg)))) := by
  let W(n):=fabric S K (p n); let F:=fabric S K hg
  have he(n):rx (W n - F)= f n - g:=by rw [map_sub]; unfold W F; rw [render_fabric,render_fabric]
  have ht:=responsiveCap Y H V G j S s Tc (fun i=>W i-F) A' (fun i=>sample_price Y H S _ ((he i).symm ▸ hp i)) (show Dues Y H G s _ from (show (render S K)∘(fun i=>W i-F) = (fun i=> f i-g) from funext he).symm ▸ h)
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp_rw [dist_eq_norm]
  have h'':=ht.norm; simp only [(ϕ S s).map_sub,norm_zero] at h''
  simp_rw [show ∀ n,(ϕ S s) (W n)=seal₀ Y H V G j false Tc s (observe (aux_test (p n))) from (fun n=>capₐ Y H V G j S s Tc _ _ (render_fabric S K (p n)).symm), show (ϕ S s) F=seal₀ Y H V G j false Tc s (observe (aux_test hg)) from capₐ Y H V G j S s Tc _ _ (render_fabric S K hg).symm] at h''
  exact h''
local notation "Ht" => Ark.Ht Y H G.history.circuit j 0 false Tc
variable (w:ℕ)(p:Between (tent Y H) j 0 (ruler Λ.block*w) S)(hw:0<w)
noncomputable def allBox : Swatch S →L[ℂ] (Ht).Op := -- notation projection
   (boxCLM Y H V G j false Tc S s w p hw).comp (allHues Y H S)
local notation "Z" S:max s:max α:max p:max h:max=>allBox Y H V G j S s Tc α p h
lemma box_chart {x:Entry Y H s j false w}(f:Swatch S)(h:x.val.val=rx f) : boxOp Y H V s G.history G.clipped j false Tc w x hw=(Z S s w p hw) f:=
   congrArg (fun x:Entry Y H s j false w=>boxOp Y H V s G.history G.clipped j false Tc w x hw) (Subtype.ext (Subtype.ext h) : x= toEntry Y H j false S s w p (allHues Y H S f))
local notation "K₁"=> Λ.R.L.val ^ (s+1-s) * w
include p hw
lemma escalatesPlace : Between K j 0 (ruler Λ.block*((K₁:ℕ):ℤ)) (R)∧ 0<K₁:=by
  have he:=expands_shape Y H p (s+1-s); rw [show s+1-s=1 from by omega] at *; rw [Nat.cast_mul,Nat.cast_pow,mul_left_comm]; exact ⟨he,Nat.mul_pos (pow_pos Λ.R.L.property _) hw⟩ -- he volumeAround not wingspan
lemma responsiveBox (f:ℕ→Swatch S)(A':ℝ)(h₀:∀ i,‖f i‖≤A')(h:Dues Y H G s (rx ∘ f)) : Tendsto (fun n=> (Z S s w p hw) (f n)) atTop (𝓝 0):=by
  obtain ⟨p',hw'⟩:= escalatesPlace Y H j S s w p hw
  have hx(x:Swatch S): (Z S s w p hw) x=(Z (R) (s+1) (K₁) p' hw') (Tx x) := by
    let y:= toEntry Y H j false S s w p (allHues Y H S x); let y':=furnished Y H s G.history j false w y (s+1) (by omega)
    have he:y'.val.val=ry (Tx x):=by
      change stream Y H G.refine s (s+1-s) (rx x)=_
      rw [show s+1-s=1 from by omega]; exact transferred ..
    exact (refined_box Y H V s G.history G.clipped j false Tc w _ hw (s+1) (by omega)).trans (box_chart Y H V G j (R) (s+1) Tc K₁ p' hw' (Tx x) he)
  simp_rw [hx]; simpa only [(Z (R) (s+1) (K₁) p' hw').map_zero] using! ((Z (R) (s+1) (K₁) p' hw').continuous.tendsto 0|>.comp (respond Y H V G S s f A' h₀ h))

end op
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.at_r
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.responsiveBox

import YM.SU5.FiniteGaugeData.Tapestry.Cantina
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin Haro
attribute [local instance] opCStarAlgebra
open Pastry Tap Nacre Ember Pec
open Push.BetaTransport
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill

section
-- Burn-in, on componentwise Hausdorff uniform structures. Use for two levels of participation.
variable {X Y Z:Type*}[NormedAddCommGroup X][NormedSpace ℂ X][NormedAddCommGroup Y][NormedSpace ℂ Y][NormedAddCommGroup Z][NormedSpace ℂ Z]
open ContinuousLinearMap
lemma concertFort {V:Type*}{v:Filter V}{A:V→ Y →L[ℂ] Z}{a:Y→L[ℂ]Z} (L:X→L[ℂ]Y)(h:IsCompactOperator L){C:ℝ}(g:∀ᶠ i in v, ‖A i‖ ≤ C)(p:∀ x,Tendsto (fun i=> A i x) v (𝓝 (a x))): Tendsto (fun i=> (A i).comp L) v (𝓝 (a.comp L)):=by
  apply Metric.tendsto_nhds.mpr; intro ε e; let c:= max 1 C; have hh:0<c:=zero_lt_one.trans_le (le_max_left ..); let d:= (ε/4)/(c+‖a‖); have ht:0<d:=by unfold d; positivity
  let U:= Metric.closedBall (0:X) 1
  obtain ⟨K,t,m⟩:= (isCompactOperator_iff_image_closedBall_subset_compact L.toLinearMap (r:=1) zero_lt_one).mp h
  obtain ⟨S,b,H,k⟩:= Metric.finite_approx_of_totallyBounded t.totallyBounded d ht
  filter_upwards [(Filter.eventually_all_finite H).mpr fun x v=> Metric.tendsto_nhds.mp (p x) (ε/4) (by linarith), g] with i p q
  rw [dist_eq_norm]; apply lt_of_le_of_lt _ (half_lt_self e); apply skimEnvelope (by positivity); intro x h'; have t':L x∈ K:= m ⟨x,mem_closedBall_zero_iff.mpr h'.le,rfl⟩
  obtain ⟨y,v,w⟩:= (show ∃ y∈ S,L x∈ ball y d from by simpa using k t')
  have H':‖A i‖ ≤ c:=q.trans (le_max_right ..)
  have p₁: ‖A i (L x)- A i y‖ ≤ c*d:=by
    have hv:‖L x-y‖ ≤ d:=(dist_eq_norm (L x) y) ▸ (mem_ball.mp w).le; rw [←map_sub]; exact (A i|>.le_opNorm _).trans (mul_le_mul H' hv (norm_nonneg _) hh.le)
  have p₂: ‖a (L x)-a y‖ ≤ ‖a‖*d:=by rw [←map_sub]; apply (a.le_opNorm _).trans; apply mul_le_mul_of_nonneg_left _ (norm_nonneg a); rw [←dist_eq_norm]; exact (mem_ball.mp w).le
  change ‖A i (L x)- a (L x)‖≤ _; have he : d*(c+‖a‖)=ε/4:= div_mul_cancel₀ _ (by positivity)
  rw [←dist_eq_norm]; rw [←dist_eq_norm] at p₁ p₂; apply (dist_triangle _ (A i y) _).trans; linarith [p y v,dist_triangle_right (A i y) (a (L x)) (a y)]
-- apply composition lemma to moving maps
lemma concert {V:Type*}{v:Filter V}{A:V→ Y→L[ℂ]Z}{a:Y→L[ℂ]Z} {F:V→X→L[ℂ]Y}{L:X→L[ℂ]Y}(t:Tendsto F v (𝓝 L))(h:IsCompactOperator L){C:ℝ}(g:∀ᶠ i in v, ‖A i‖ ≤ C)(p:∀ x,Tendsto (fun i=> A i x) v (𝓝 (a x))): Tendsto (fun i=> (A i).comp (F i)) v (𝓝 (a.comp L)):=by
  suffices H : Tendsto (fun i=> (A i).comp (F i) - (A i).comp L) v (𝓝 0) by simpa using H.add (concertFort L h g p)
  apply steam (X:=X→L[ℂ]Z) (g:=fun i=> C*‖F i-L‖)
  · simpa using ((t.sub_const L).norm.const_mul C)
  exact g.mono fun i v'=> by rw [sub_zero,←comp_sub]; exact ((A i).opNorm_comp_le (F i-L)).trans (mul_le_mul_of_nonneg_right v' (norm_nonneg _))
lemma pitch_comp {V:Type*}{v:Filter V}{A:V→ Y →L[ℂ] Z}{a:Y→L[ℂ]Z}{F:V→X→L[ℂ]Y}{L:X→L[ℂ]Y}(p:Tendsto F v (𝓝 L))(t:Tendsto A v (𝓝 a)): Tendsto (fun i=> (A i).comp (F i)) v (𝓝 (a.comp L)):= Exhibition.bilTend (A:=Y→L[ℂ]Z) (A':=X→L[ℂ]Y) (R:=X→L[ℂ]Z) (ContinuousLinearMap.compL ℂ X Y Z) t p
end

lemma ward_concert (N M:Side){A:ℕ→Ward M→L[ℂ]ℂ}{a:Ward M→L[ℂ]ℂ}{F:ℕ→Ward N→L[ℂ]Ward M}{L:Ward N→L[ℂ] Ward M}{C:ℝ}(t:Tendsto F atTop (𝓝 L))(h:IsCompactOperator L)(g:∀ i, ‖A i‖ ≤ C)(p:∀ x,Tendsto (fun i=> A i x) atTop (𝓝 (a x))) : Tendsto (fun i=> (A i).comp (F i)) atTop (𝓝 (a.comp L)):= concert (X:=Ward N) (Y:= Ward M) (Z:=ℂ) t h (Eventually.of_forall g) p
lemma pitch_sw (S:Finset Cover)(N:Side){A:ℕ→Ward N→L[ℂ]ℂ}{a:Ward N→L[ℂ]ℂ}{F:ℕ→ Swatch S→L[ℂ]Ward N}{L:Swatch S→L[ℂ] Ward N}(p:Tendsto F atTop (𝓝 L))(t:Tendsto A atTop (𝓝 a)): Tendsto (fun i=> (A i).comp (F i)) atTop (𝓝 (a.comp L)):= pitch_comp (X:=Swatch S) (Y:= Ward N) (Z:=ℂ) p t


/-!
# ALL rows cutoff limit at fixed period

Row Ward price is in terms of `sites`, used here for a fixed volume and NOT
sufficient for passing to the cofinal periods. That step uses `parallel`, `IR`,
and the specialty `followStage` passage already built. Both can use this bridge.
No claim of an exact cross-period schedule on unelected periods.
-/
set_option quotPrecheck false
section
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable (s i k:ℕ)(S:Finset Cover)
local notation "Ω" i:max s:max => side Y i s
local notation "μ"=> side Y i s
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→ Tariff}
local notation "Xlocal" k:max=> savings Y s i k
local notation "K"=> tent Y H
namespace Exhibition
variable (D:Exhibition Y H a b I E L B)
-- unit price all rows. can be small peri. don't require 𝕌 calibration of printed data
include D
lemma innerPrices (x:Swatch S): Tendsto (fun k=> (Xlocal (b k)) (wearStep Y H S s i x)) atTop (𝓝 (I s (render S K x) i)):= (pointRow Y H S s i D x).congr fun k=>by rw [←swatchSavings,ContinuousLinearMap.comp_apply]
lemma wardValue (x: Ward (side Y i s)): ∃ z:ℂ, Tendsto (fun k=>(Xlocal (b k)) x) atTop (𝓝 z):= by
  obtain ⟨y,rfl⟩:= wardrobeRange Y H s i x; exact ⟨_,innerPrices Y H s i _ D y⟩
local notation "ζ"=> wardValue Y H s i D
def refreshmentsₗ : Ward (side Y i s)→ₗ[ℂ]ℂ where
  toFun x:= (ζ x).choose
  map_add' x y:= tendsto_nhds_unique (ζ (x+y)).choose_spec (((ζ x).choose_spec.add (ζ y).choose_spec).congr fun k=> (map_add ..).symm)
  map_smul' z x:= tendsto_nhds_unique (ζ (z • x)).choose_spec (((ζ x).choose_spec.const_smul z).congr fun k=> (map_smul (Xlocal (b k)) z x).symm)
def refreshments : Ward (side Y i s)→L[ℂ]ℂ := (D.refreshmentsₗ Y H s i).mkContinuous (torCost Y s i) fun x=> le_of_tendsto (ζ x).choose_spec.norm (Eventually.of_forall fun k:ℕ=> (Xlocal (b k)).le_of_opNorm_le (savingsOp Y s i (b k)) x)
local notation "Ξ"=> refreshments Y H s i D
lemma borrowing (x:Ward (side Y i s)): Tendsto (fun k=>savings Y s i (b k) x) atTop (𝓝 (refreshments Y H s i D x)):= (ζ x).choose_spec
lemma bonusBalance: (Ξ).comp (wearStep Y H S s i)= D.rowsRead Y H S s i:= ContinuousLinearMap.ext fun x=> tendsto_nhds_unique (D.borrowing Y H s i (wearStep Y H S s i x)) (D.innerPrices Y H s i S x)
lemma savingsUnit : Ξ 1=1:= tendsto_nhds_unique_of_eventuallyEq (borrowing Y H s i D 1) tendsto_const_nhds ((D.sharper Y H s i).mono fun k h=>whereSavings Y s i (b k) h)
end Exhibition
namespace Fashion
variable (D:Fashion Y H a b I E L B T t)
include D
local notation "υ"=> D.toExhibition
lemma performUV: Tendsto (fun k:ℕ=> music Y s i (b k)) atTop (𝓝 (rhythm Y s i (T s i))):= (streaming Y s i).continuousAt.tendsto.comp (D.stripe s i)
lemma performance : Tendsto (fun k:ℕ=>(savings Y (s+1) i (b k)).comp (music Y s i (b k))) atTop
    (𝓝 (((υ).refreshments Y H (s+1) i).comp (rhythm Y s i (T s i)))):=
   ward_concert (side Y i s) (side Y i (s+1)) (F:=fun k=> music Y s i (b k)) (D.performUV Y H s i) (compact_tone Y s i _) (g:=fun k :ℕ=> savingsOp Y (s+1) i (b k)) (p:=fun x=> (υ).borrowing Y H (s+1) i x)
lemma acceptCut : Tendsto (fun k:ℕ=> savings Y s i (b k)) atTop (𝓝 (((υ).refreshments Y H (s+1) i).comp (rhythm Y s i (T s i)))):=
  (D.performance Y H s i).congr' ((D.univ_.pick.grow_k.tendsto_atTop.eventually (eventualPairIdx Y s i)).mono fun i' h=> conserve_exact Y s i (b i') h)
lemma rhythmRow : ((υ).refreshments Y H (s+1) i).comp (rhythm Y s i (T s i))= (υ).refreshments Y H s i := ContinuousLinearMap.ext fun x=> tendsto_nhds_unique (cn_apply (X:=Ward (side Y i s)) (Y:=ℂ) (D.acceptCut Y H s i) (tendsto_const_nhds (x:=x) (f:=atTop))) ((υ).borrowing Y H s i x)
lemma uv_strength : Tendsto (fun k:ℕ=> savings Y s i (b k)) atTop (𝓝 ((υ).refreshments Y H s i)):= by rw [←D.rhythmRow Y H s i]; exact D.acceptCut Y H s i
lemma follow_wear (q:Matinee Y S s i):
   (wearStep Y H (followBox (Λ:=Λ) (l:=l) S) (s+1) i).comp (L S s i) = (rhythm Y s i (T s i)).comp (wearStep Y H S s i):=by
  let G:= followBox (Λ:=Λ) (l:=l) S
  apply tendsto_nhds_unique_of_eventuallyEq (pitch_comp (X:= Swatch S) (Y:=Swatch G) (Z:=Ward (side Y i (s+1))) (A:=fun _=> wearStep Y H G (s+1) i) (a:=(wearStep Y H G (s+1) i)) (D.inner S s i) tendsto_const_nhds)
      (pitch_comp (X:=Swatch S) (Y:= Ward (side Y i s)) (Z:=Ward (side Y i (s+1))) (L:=wearStep Y H S s i) (F:=fun _=>wearStep Y H S s i) tendsto_const_nhds (D.performUV Y H s i))
  exact ((υ).matineeRow Y H S s i q).mono fun j p=> compatibility_boutique Y H S s i (b j) p
lemma uv_allSwatch : Tendsto (fun k=> tapReader Y H S s i (b k)) atTop (𝓝 ((υ).rowsRead Y H S s i)):=by
  simp_rw [←swatchSavings, ←Exhibition.bonusBalance Y H s i S (υ)]; exact pitch_sw S (side Y i s) (L:=wearStep Y H S s i) (F:=fun _=>wearStep Y H S s i) tendsto_const_nhds (D.uv_strength Y H s i)
end Fashion
end
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.uv_strength
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.follow_wear
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.uv_allSwatch

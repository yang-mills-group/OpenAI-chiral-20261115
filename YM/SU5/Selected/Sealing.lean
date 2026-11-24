import YM.SU5.Selected.Survives
/-! # Norm prices vs coordinate of insertion on ANY resident
Fixed support → can choose same box width and offset; cap chart even
before electing a phase. No estimate uniform across moving supports. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 720000
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
open Tapestry (Swatch render renderLe spread texture)
open Set
variable (S:Finset Cover) (s:ℕ)
local notation "rx"=>render S K
local notation "φ"=> hues Y H strict S
local notation "T₀"=> catalog Y H V G j strict C

noncomputable def chartFamily (f:φ) : observable K strict:= ⟨rx f.val,aux_test (texture S K f.val),f.property⟩
local notation "F"=>chartFamily Y H strict S
noncomputable def sealMap : (φ) →ₗ[ℂ] (catalog Y H V G j strict C) where
 toFun f:= seal₀ Y H V G j strict C s (F f)
 map_add' f g:= Subtype.ext (cap_add Y H V G j strict C s _ _ _ (map_add rx f.val g.val))
 map_smul' r f:= Subtype.ext (cap_scale Y H V G j strict C s _ _ r (map_smul rx r f.val))
local notation "LM"=> sealMap Y H V G j strict C S s

lemma postdates : ∀ᶠ t:ℤ in atTop,∀ᶠ v:ℕ in atTop,
    Between (tent Y H) j 0 (ruler Λ.block*v) (SlabMark.plow K j t S):=by
  have hr:ruler Λ.block > 0:= ruler_gene ..
  obtain ⟨v,d⟩:= Tower.sizes S
  obtain ⟨p,z⟩:= d j
  let X:ℤ→ℤ:=fun x=>p+ruler Λ.block*x
  have ht:Tendsto X atTop atTop:= tendsto_atTop_add_const_left _ p (Tendsto.const_mul_atTop' hr tendsto_id) -- name
  filter_upwards [ht.eventually_ge_atTop ((K).ℓ:ℤ)] with c hc
  let k:= p+v+ruler Λ.block * c+ (K).ℓ
  filter_upwards [eventually_ge_atTop k.toNat] with i u x t
  obtain ⟨y,ty,rfl⟩:= plow_stays K j c S t
  specialize z y ty; change (_ + _≤ _ ∧ _ ≤ _)
  simp only [moves,↓reduceIte]; unfold X at hc
  have he: k ≤ (i:ℤ):=by omega
  have hp: (i:ℤ)≤ruler Λ.block * i:=by
    have he:1 ≤ ruler Λ.block := hr; nlinarith only [mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α:=ℤ) i)]
  unfold k at he
  change _ + _≤ y j + ruler Λ.block * c ∧ _ ≤ _; change _+_≤ y j + _ ∧ y j + ruler Λ.block*c + _ ≤ ruler Λ.block*i --
  constructor <;> linarith

noncomputable def finance (f:φ)(x:ℤ)(u:ℕ)(h:Between K j 0 (ruler Λ.block*u) (plow K j x S)): Entry Y H s j strict u:=
  let e:=flow_port K j (gaugeT K x) (texture S K f.val)
  ⟨⟨relocate K j x (F f).val,(purpose_ok ..).2 ⟨⟨plow K j x S,e,(by rw [area0]; intro v p; exact (h v p).1)⟩,fun p=> chime_cov K j (gaugeT K x) (texture S K f.val) (f.property p)⟩⟩,plow K j x S,e,h⟩
lemma seal_cost : ∃ r:ℝ,∀ f:φ,‖LM f‖≤ r*‖f‖ := by
  obtain ⟨x,t⟩ := (postdates Y H j S).exists
  obtain ⟨u,h,p⟩:= (t.and (eventually_gt_atTop (0:ℕ))).exists
  let D:= boxCLM Y H V G j strict C (plow K j x S) s u h p
  refine ⟨‖D‖*spread S,fun f=>?_⟩
  let a:=finance Y H j strict S s f x u h; let b:= B s a p
  have ha: InTest K true (plow K j x S) false a.val.val:= flow_port K j _ (texture S K f.val)
  have hb: pay a.val.val (spread S*‖f.val‖):=chime_pay K j _ _ (rendered_price Y H S _)
  have he: ‖b‖≤ ‖D‖*(spread S*‖f.val‖):= prices_box Y H V G j strict C _ s _ h p a ha hb
  change ‖(P s) (F f)‖≤ _ * ‖(f.val:Swatch S)‖; rw [cap_moved_entry Y H V G j strict C s u a (F f) p x rfl]
  refine le_trans (b:=‖b‖) ?_ (he.trans_eq (mul_assoc ..).symm)
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc _ ≤ 1*(‖b‖ * 1) := mul_le_mul (Submodule.orthogonalProjectionOnto_norm_le _) ((ContinuousLinearMap.opNorm_comp_le b (ι₀)).trans (mul_le_mul_of_nonneg_left (Submodule.norm_subtypeL_le _) (norm_nonneg b))) (norm_nonneg _) zero_le_one
       _ = _ := by ring

noncomputable def supportCap : (φ) →L[ℂ] (catalog Y H V G j strict C) :=
  (LM).mkContinuous _ (seal_cost Y H V G j strict C S s).choose_spec
-- for false, all Swatch
variable (a : Axis) (R : Arena Y H G.history.circuit j 0 false)
noncomputable def allHues : Swatch S →L[ℂ] (hues Y H false S) := (ContinuousLinearMap.id ℂ (Swatch S)).codRestrict (hues Y H false S) (fun _ v=> by contradiction)
local notation "Fₐ"=>seal₀ Y H V G j false R s
noncomputable def allCap : Swatch S →L[ℂ] (catalog Y H V G j false R) :=
  (supportCap Y H V G j false R S s).comp (allHues Y H S)
lemma capₐ (f:Swatch S)(y:observable K false)(t:y.val=rx f) : allCap Y H V G j S s R f= (Fₐ y):= congrArg Fₐ (Subtype.ext (show rx f=y.val from t.symm) : chartFamily Y H false S (allHues Y H S f)=y)
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.capₐ

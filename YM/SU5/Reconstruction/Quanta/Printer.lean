import YM.SU5.Reconstruction.Quanta.Bud
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
set_option linter.unusedVariables false -- h₁, V etc
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
open WindRose
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)

-- $Vane on BOTH grades, and on this very needle. Use Level.s, $Region.S$. Physical unit s resolution.
open PhaseChoice
noncomputable def price (s:ℕ)(b:Bool)(f:Family (tent Y H)):ℂ:= if b then 0 else PhaseChoice.evaluate Y H V G j C (PhaseChoice.SameCharacter.resident Y H V G j false (C j) χ) s f
local notation "Pₓ" => price Y H V G C j χ
local notation "Ω"=> oneAt Y H V G j (C j) χ
variable (s:ℕ)
variable {b t:Bool}{f g:Family (tent Y H)} {S S':Finset Cover}
lemma price_oneAt (F:Dome (tent Y H)): Pₓ s false F.val= Ω s F:= audition_here Y H V G j C χ s ▸ rfl -- orientation tune
lemma price_oneAt' (F:Dome (tent Y H))(h:F.val=f): Pₓ s false f= Ω s F:= h ▸ price_oneAt Y H V G C j χ s F
lemma price_across (k:Axis) (p:InTest (tent Y H) true S b f) : price Y H V G C k (displacement Y H V G.history G.clipped j false (C j) χ k (C k)) s b f=Pₓ s b f:=by
 cases b; swap; · rfl
 let F:Dome (tent Y H):= ⟨f,aux_test p⟩; rw [price_oneAt' Y H V _ _ k _ _ F rfl,price_oneAt' Y H V _ _ j _ _ F rfl,acrossOne]
lemma context_lift {q s':ℕ} (p:InTest (tent Y H) true S false f) : Pₓ (s'+q) false (stream Y H G.refine s' q f)= Pₓ s' false f:=by
 let F:Dome (tent Y H):= ⟨f,aux_test p⟩; rw [price_oneAt' Y H V G C j χ s' F rfl,price_oneAt' Y H V G C j χ (s'+q) (spreadTo Y H G s' (s'+q) F) (by rw [spreadTo_val,Nat.add_sub_cancel_left]),oneAt_spread Y H V G _ _ _ (by omega)]
lemma price_add (p:InTest K true S b f)(q:InTest K true S' b g): Pₓ s b (f+g)=Pₓ s b f+ Pₓ s b g:=by
 cases b; swap; · simp [price]
 have ht:= PhaseChoice.consistency Y H V G j C (PhaseChoice.SameCharacter.resident Y H V G j false (C j) χ) (S∪S') s
 exact ht.plus_v _ _ (p.mono Finset.subset_union_left) (q.mono Finset.subset_union_right)
lemma price_smul (p:InTest K true S b f)(z:ℂ): Pₓ s b (z • f)= z • Pₓ s b f:=by
 cases b; swap; · simp [price]
 have ht:= PhaseChoice.consistency Y H V G j C (PhaseChoice.SameCharacter.resident Y H V G j false (C j) χ) S s; exact ht.scale f p z
lemma price_rotation (u:Cover→ SU.E)(p:InTest K true S b f)(q:InTest K true S b g)(t: Tapestry.Circular S u f g): Pₓ s b g=Pₓ s b f:=by
 cases b; swap; · rfl
 exact (PhaseChoice.consistency Y H V G j C _ S s |>.gauge u f g p q t).symm -- infer resident?
lemma parity_funded (p:InTest (tent Y H) true S true f) {n k:ℕ}(h:Tapestry.Pay Y s n k): Pₓ s true f= sharp Y H s n k f:= (QuantaCore.sharp_parity Y H n k h p).symm
variable (j' : Axis) (z:ℤ)
section motion
variable (h:ℤ)
open Heat
-- CP1 even mesh, even matter pitch meaning on imported.Weld. Eupo positivity of THIS χ at translated powers.
private lemma chime_sum_ch {J:Calibration}{f:Family J} (p:InTest J true S b f): chime J j z (chime J j h f)=chime J j (z+h) f:=by
 rw [←moted J j (z+h) h z (flow_port J j h p) (by omega), show (chime J j h f)=mirror J j h (mirror J j 0 f) from rfl,reversal J j h (axial J j 0 p)]; rfl
private lemma chime_symm {J:Calibration}{f:Family J} (p:InTest J true S b f): chime J j z (mirror J j h f)=mirror J j h (chime J j (-z) f):=by
 rw [←moted J j (h+z) h z (axial J j h p) (by omega),←moted J j h (h+z) (-z) p (by omega),reversal J j h p,reversal J j h (axial J j (h+z) p)]
private lemma chime_plane {J:Calibration}{f:Family J} (p:InTest J true S b f): chime J j z (mirror J j h f)=mirror J j (h+2*z) (chime J j z f):=by
 rw [slidesPlane j p h,slidesPlane j (flow_port _ j z p)]; rw [← (show chime J j (-z) (mirror J j 0 f)=mirror J j 0 (chime J j z f) from by rw [chime_symm j _ _ p,neg_neg]),chime_sum_ch j z _ (axial _ j 0 p),chime_sum_ch j _ _ (axial _ j 0 p),show h+2*z+-z=z+h by omega]
lemma price_slide(p:InTest K true S b f): Pₓ s b (chime (tent Y H) j' (2*z) f)=Pₓ s b f:=by
 cases b; swap; · rfl
 exact PhaseChoice.elect_sold Y H V G j' s j C _ z (aux_test p) -- `_`
lemma price_flip (p:InTest K true S b f): Pₓ s b (mirror K j' (2*z) f)=star (Pₓ s b f):=by
 cases b; swap; · simp [price]
 exact PhaseChoice.elect_glassUp Y H V G j' s j C _ z (aux_test p)
local notation "Z"=> gaugeShift Λ.block z
local notation "pZ"=> poleForm K j' (Heat.gaugeShift Λ.block z) b
lemma price_aligned (p:InTest (tent Y H) true S b f)(h:Tower.region j' Z ((tent Y H).ℓ) S): 0 ≤ Pₓ s false (pZ f f):=by
 let c:ℤ:= -(Λ.block.val:ℤ)*z
 let q:= 2*c
 let y:= chime (tent Y H) j' q f
 have v:(Z)+2*q=0:= by unfold q c Heat.gaugeShift; ring
 have e: chime K j' q (pZ f f)= poleForm K j' 0 b y y:=by unfold poleForm y; rw [chime_scale,chime_product,chime_plane j' _ _ p,v]
 let W:=address j' q S; have t:InTest K true W b y:=flow_port K j' q p; have hw:Tower.region j' 0 ((tent Y H).ℓ) W:=by
    intro i dt; obtain ⟨i,hu,rfl⟩:= Finset.mem_image.mp dt; specialize h i hu; rw [SlabMark.moves,if_pos rfl]; linarith -- simp tune
 let F:Dome K:= ⟨poleForm K j' 0 b y y, aux_test (NorthTapes.statement j' 0 t t)⟩
 rw [←price_slide Y H V G C j χ s j' c (NorthTapes.statement j' Z p p),e,← price_across Y H V G C j χ s j' (NorthTapes.statement j' 0 t t), price_oneAt' Y H V _ _ _ _ _ F rfl]; exact station_happy Y H V G C j' _ t hw rfl
end motion
lemma price_normcap (d:Swatch S): Pₓ s false (render S K d)= χ (allCap Y H V G j S s (C j) d):=by
 let W:=observe (aux_test (texture S K d))
 rw [PhaseChoice.capₐ Y H V G j S s (C j) d W rfl]; change PhaseChoice.evaluate Y H V G j C _ _ W.val= _; rw [PhaseChoice.evaluates]; rfl
lemma price_limit {F:ℕ→Family (tent Y H)}(h:BQueue S F f): Tendsto (fun n=>Pₓ s false (F n)) atTop (𝓝 (Pₓ s false f)):=by
 obtain ⟨d,rfl⟩:= rendered S K h.landing; choose g u using fun n=> rendered S K (h.whereTo n)
 have hp:Tendsto g atTop (𝓝 d):=by
    apply Metric.tendsto_nhds.mpr; intro e he; filter_upwards [h.saved _ (half_pos he)] with i p
    rw [dist_eq_norm]; apply lt_of_le_of_lt (sample_price Y H S _ _) (half_lt_self he); rw [map_sub,u]; exact p
 rw [price_normcap]; have he: Continuous (fun x:Swatch S=> χ (allCap Y H V G j S s (C j) x)):= (show Continuous χ from (PhaseChoice.SameCharacter.resident Y H V G j false (C j) χ).val.continuous).comp (allCap Y H V G j S s (C j)).continuous
 exact ((he.tendsto d).comp hp).congr fun n=> (u n) ▸ (price_normcap Y H V G C j χ s (g n)).symm -- tune
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.price_add
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.price_rotation
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.price_aligned
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.price_limit

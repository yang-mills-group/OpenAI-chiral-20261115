import YM.SU5.Reconstruction.Anvil.Component
import YM.SU5.Reconstruction.Cashier.Honesty
import YM.SU5.Reconstruction.Cashier.Heritage
/-! # Settlement funds for Mink's Hearth -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget.Hearthbank
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry ConePrice Germ
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Anvil
open SelectionAnalysis
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open FirstWindows.Chambers
variable (j:Axis)(C:Arena Y H G.history.circuit j 0 false)
variable (χ:displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "D" => Domain Y H G false
local notation "Gt" => marks (timeMesh Λ)
local notation "R"=> indoor Y H V G.history G.clipped j false C χ
local notation "S"=> fort Y H V G.history G.clipped j false C χ
local notation "Θ"=> doorstep Y H V G.history G.clipped j false C χ
local notation "L"=> ride Y H V G.history G.clipped j false C χ
local notation "W"=>saunters Y H V G.history G.clipped j false C χ
local notation "P"=>(W).orthogonalProjectionOnto
local notation "Π₁"=>opCarries Y H V G j C χ
local notation "ρ" i:max=>FirstWindows.move (tent Y H) (eject j i)
variable {X Y':(indoor Y H V G.history G.clipped j false C χ).Op} -- expand
open TopologicalSpace
lemma separable : SeparableSpace (R:Type) := by
 haveI := drive_separable Y H V G.history G.clipped j false C
 exact (arrive_dense Y H V G.history G.clipped j false C χ).separableSpace (arrive_cont ..)

lemma padding {x: Sky K}{u v : Gt}(h: u ≤ v)(e:Follows Y H V G j C χ x u X): ∃ Z:(R).Op,Follows Y H V G j C χ x v Z∧ ‖Z‖≤‖X‖:=by
 let C':=v-u; let z:=eject j (C':Gt)
 let a:= (C':ℝ).toNNReal
 let B:=(L).E a; have hz:0 ≤ (z j).val:= by unfold z; simp; exact sub_nonneg.mpr h -- sub in marks
 have he:atEstate Y H V G.history G.clipped j false C χ z=B:=by
    have hh : (fun k:Trans j=> z k.val)=0:= funext fun k=> eject_away j _ _ k.property
    unfold atEstate; rw [show Real.toNNReal (↑(z j))=a from by unfold a; simp [z],hh,Germ.Alliance.raw_zero]; rfl
 refine ⟨X.comp B,⟨domain_mono Y H G (show Chambers.strip j (0:ℝ) u⊆ Chambers.strip j 0 v from fun i t=>⟨t.1,(t.2 : i j≤ _).trans h⟩) e.pose,fun t=>?_⟩,?_⟩
 · have Ht:= later_frame Y H V G j t.val z t.property hz; obtain ⟨p,heF,hx⟩:=e.graph ⟨FirstWindows.move _ z t.val,Ht⟩
   refine ⟨p,heF.trans ?_,hx.trans ?_⟩
   · apply congrArg (x * ·); change (ρ u) ((ρ C') t.val)=_; rw [move_sum, selectRay,show u+C'=v from by unfold C'; abel]
   change X (OSvector Y H V G j C χ ⟨_,_⟩)=_ -- tune
   rw [transported_ket Y H V G j C χ t.val t.property z hz,he]; rfl
 exact (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_of_le_one_right (norm_nonneg X) ((L).shrinks a))

lemma uplink (X:(indoor Y H V G.history G.clipped j false C χ).Op)(x y:S) : inner ℂ x ((Π₁ X) y)=inner ℂ (x.val:R) (X (y.val:R)) := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left ..
lemma weak_contour (x:(indoor Y H V G.history G.clipped j false C χ).Op):‖Π₁ x‖≤‖x‖:=by
 apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro p
 change ‖P (x (p.val : R))‖ ≤ ‖x‖ * ‖p‖; exact ((W).norm_orthogonalProjectionOnto_apply_le _).trans (x.le_opNorm _)
lemma projected {ι:Type*}{f:Filter ι}{X0:ι→(indoor Y H V G.history G.clipped j false C χ).Op}
 (h:Limited f X0 X) : Limited f (fun i=> Π₁ (X0 i)) (Π₁ X):=by
 obtain ⟨⟨e,p,g⟩,HX⟩:=h; refine ⟨⟨e,p,g.mono fun i h=> (weak_contour ..).trans h⟩,fun x y=>?_⟩
 simp_rw [uplink]; exact HX (x.val:R) (y.val:R)
lemma projected_units {v:ℝ}(h:‖X+1‖ ≤ v) : ‖Π₁ X+1‖ ≤ v:=by
 apply le_trans (b:=‖Π₁ (X+1)‖) _ ((weak_contour ..).trans h); apply le_of_eq; apply congrArg norm; ext1 x; change _=P ((X+1) (x.val:R)); rw [show (X+1) (x.val:R)=X x.val+(x.val:R) from rfl,map_add,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]; rfl
lemma skinny (w:ℕ) : Tendsto (fun s=>whenly (timeMesh Λ) s w) atTop (𝓝 0):=by simpa [whenly] using ((vanishes (timeMesh Λ)).const_mul (w:ℝ≥0))
lemma momentShrink {l₀:ℕ→ℕ} (w:ℕ) {Φ:ℕ→(indoor Y H V G.history G.clipped j false C χ).Op}
  (h:Tendsto l₀ atTop atTop)(q: ∀ n, ‖Φ n+(L).E (whenly (timeMesh Λ) (l₀ n) w)‖ ≤ 1/64) (v:Limited atTop Φ X):‖X+1‖≤1/64:=by
 let A(n):=(L).E (whenly (timeMesh Λ) (l₀ n) w)
 apply Limited.convertible atTop (by norm_num) (A:=fun n=>Φ n+A n) _ (Eventually.of_forall q)
 refine ⟨⟨_,by norm_num,Eventually.of_forall q⟩,fun x y=>?_⟩
 have hx:Tendsto (fun n=> inner ℂ x (A n y)) atTop (𝓝 (inner ℂ x y)):=by
    have ht:= ((L).continuousE y |>.tendsto 0).comp ((skinny (Λ:=Λ) w).comp h)
    rw [(L).eZero] at ht; exact tendsto_const_nhds.inner ht -- order
 simp_rw [_root_.ContinuousLinearMap.add_apply,inner_add_right]; exact (v.confirms x y).add hx

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget.Hearthbank
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget.Hearthbank.padding
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget.Hearthbank.momentShrink

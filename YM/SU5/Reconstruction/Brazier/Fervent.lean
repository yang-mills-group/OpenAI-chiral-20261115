import YM.SU5.Reconstruction.Brazier.Horizon
import YM.SU5.Reconstruction.Brazier.Command
/-! Purchase the χ vector at the Root before even shifting support outside, and have thermal matrix expenditures estimated uniformly. ALL at that rooted law. -/
set_option autoImplicit false
set_option synthInstance.maxSize 31000
set_option maxRecDepth 6200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry Altitude Exhibition Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
variable {L : Rack Λ l} {B : Clay Λ l} (Z : Exhibition Y H i k I E L B)
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "Gt" => marks (timeMesh Λ)
local notation "t₀" => insideAt Λ l (tent Y H)
local notation "D" => Domain Y H G
local notation "A"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "Π"=>Aurora Y H V G.history j false C
local notation "Kx" t:max=> vistaFinish Y H t Z
local notation "Px" => LightBudget.prepaid Y H V G j C
namespace Fervor
open Hearth Metric
local notation "σ"=> driveAlgebra Y H V G.history G.clipped j false C
local notation "Ω"=>groundRoom Y H V G.history j false C
local notation "H₀"=> advance Y H V G.history.circuit j 0 false C
local notation "Z₀"=> reduceToDisplay Y H V G.history G.clipped j false C
local notation "Ht"=> Hearth Y H G j
lemma applaud {S:Set (driveAlgebra Y H V G.history G.clipped j false C)} (p:IsCompact S) {δ:ℝ} (h:0<δ): ∃ x:Aurora Y H V G.history j false C, ‖x‖=1∧∀ a∈ S, ‖inner ℂ x.val ((a:σ).val x.val)-χ (Z₀ a)‖ ≤ δ:=by
 let Q:= (Z₀) '' S
 obtain ⟨t,b,g⟩:= Emplacement.compactAsk (H:=(Ω)) χ (p.image (Z₀).continuous) h (seat0 Y H V G.history j false C) (norm_one_vac Y H V G.history j false C)
 refine ⟨t,b,fun a ua=>?_⟩; specialize g (Z₀ a) (mem_image_of_mem (Z₀) ua)
 rw [reduce_val] at g; change ‖inner ℂ (t:Π) ((Π).orthogonalProjectionOnto (a.val t.val)) - _‖≤δ at g
 rwa [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] at g
-- Creating one gate with required APPROXIMATION. at wanted height R and pushing later. requirement r.
lemma canals (t:Aurora Y H V G.history j false C) (d:ℝ)(p:0<d) (R:MeshClock.marks (timeMesh Λ))(v:0<R)(T:ℕ) :∃ r:Hearth Y H G j, r.height=R ∧ T < r.roof ∧ ‖r.home Y H V G j C - t.val‖ ≤ d:=by
 obtain ⟨a,⟨x,p₁,e,w,rfl⟩,z⟩:= mem_closure_iff.mp (LightBudget.advance_dense Y H V G j C 0 t.val) d p
 have hx : Pub Y H j R x ∈ Domain Y H G true (flank j R):= by simpa only [zero_add] using pub_area Y H V G j (t:=R) x p₁
 obtain ⟨s,k,f,h,h'⟩:= ((eventually_gt_atTop T).and ((domain_eventually Y H G).1 hx)).exists
 refine ⟨⟨s,R,f,x,v,h,p₁,?aa⟩,rfl,k,?_⟩
 case aa=> exact h'.symm -- tune
 exact (dist_eq_norm (Px ⟨x,w⟩) t.val) ▸ (dist_comm ..|>.trans_lt z).le -- tune metavars

lemma ranges (B': Set (driveAlgebra Y H V G.history G.clipped j false C)) (p:IsCompact B') : ∃ b:ℝ, 1≤b ∧ ∀ x ∈ B', ‖(x:σ).val‖ ≤ b ∧ ‖χ (Z₀ x)‖ ≤ b:=by
 obtain ⟨a,h⟩:=(p.image (f:=(fun v=>‖(v:σ)‖)) continuous_norm).bddAbove
 obtain ⟨b,e⟩ := ( (p.image (Z₀).continuous).image (f:=(fun v=>‖v‖)) continuous_norm).bddAbove
 refine ⟨max 1 (max a b), le_max_left ..,fun x t=>?_⟩ -- trailing
 exact ⟨(h ⟨x,t,rfl⟩).trans ((le_max_left a b).trans (le_max_right ..)), (NonUnitalStarAlgHom.norm_apply_le χ (Z₀ x)).trans ((e ⟨Z₀ x,⟨x,t,rfl⟩,rfl⟩).trans ((le_max_right a b).trans (le_max_right ..)))⟩
private lemma downhill (a:Ark.Ht Y H G.history.circuit j 0 false C) (b:Aurora Y H V G.history j false C)
 (x:(Ark.Ht Y H G.history.circuit j 0 false C).Op)(u:‖b‖=1){k d:ℝ}(hk:1≤k)(hc: d≤1) (hy:‖x‖ ≤ k)(ha: ‖a-b.val‖ ≤ d)(s:ℝ≥0) : ‖inner ℂ (H₀ s a) (x (H₀ s a)) - inner ℂ b.val (x b.val)‖ ≤ d*(3*k):=by
 let c:= H₀ s a; have hw:0 ≤ k:=one_pos.le.trans hk
 have heev : ‖c - b.val‖ ≤ d:=by
   nth_rw 1 [←still Y H V G j C s b]; unfold c; rw [← map_sub]
   refine (ContinuousLinearMap.le_opNorm ..).trans ((_root_.mul_le_of_le_one_left (norm_nonneg _) (advance_small Y H V ..)).trans ha) -- tune
 have ht : ‖c‖≤ 2 := by
   have hx:= norm_add_le (c-b.val) b.val; rw [sub_add_cancel,show ‖b.val‖=1 from u] at hx; linarith
 have hi : inner ℂ c (x c)- inner ℂ b.val (x b.val)=inner ℂ (c-b.val) (x b.val)+inner ℂ c (x (c-b.val)):=by rw [map_sub (f:=x),inner_sub_left,inner_sub_right]; abel
 change ‖inner ℂ c (x c)-_‖≤_; rw [hi]
 refine (norm_add_le ..).trans ((add_le_add ?hf ?hg : _ ≤ d * k + 2*(k*d)).trans_eq (by ring))
 case hf => refine (norm_inner_le_norm ..).trans (mul_le_mul heev ?_ (norm_nonneg _) ((norm_nonneg _).trans heev)); refine (x.le_opNorm _).trans ?_; rw [show ‖b.val‖=1 from u,mul_one]; exact hy
 case hg=> exact (norm_inner_le_norm ..).trans (mul_le_mul ht ((x.le_opNorm _).trans (mul_le_mul hy heev (norm_nonneg _) hw)) (norm_nonneg _) (by norm_num))
-- full uniform expenditure of shape
lemma planting (U:Set (driveAlgebra Y H V G.history G.clipped j false C))(p:IsCompact U)
 (ε:ℝ)(e:0<ε)(d:MeshClock.marks (timeMesh Λ))(z:0<d)(s:ℕ): ∃ r:Hearth Y H G j,r.height=d ∧ s < r.roof∧ ∀ a∈ insert (1:driveAlgebra Y H V G.history G.clipped j false C) U, ∀ t:ℝ≥0, let b:= advance Y H V G.history.circuit j 0 false C t (r.home Y H V G j C); ‖inner ℂ b ((a:σ).val b)-χ (Z₀ a)‖≤ε:=by
 let S:= insert 1 U; obtain ⟨k,h,b⟩:=ranges Y H V G j C χ S (p.insert _); let g:=min 1 (ε/(6*k)); have hd:0<g:=lt_min one_pos (div_pos e (by linarith))
 obtain ⟨t,b₀,c⟩:= applaud Y H V G j C χ (p.insert 1) (half_pos e)
 obtain ⟨r,h',a,f⟩:= canals Y H V G j C t g hd d z s
 refine ⟨r,h',a,fun x u τ =>?_⟩; intro v
 have hy:= downhill Y H V G j C (r.home Y H V G j C) t x.val b₀ h (min_le_left 1 (ε/(6*k))) (b x u).1 f τ
 have he : g * (3*k) ≤ ε / 2:= by
    refine (mul_le_mul_of_nonneg_right (min_le_right ..) (by linarith)).trans_eq ?_
    field_simp
    -- positivity from 1≤k
    <;> nlinarith
 exact (norm_sub_le_norm_sub_add_norm_sub (inner ℂ v _) (inner ℂ t.val (x.val t.val)) (χ (Z₀ x))).trans ((add_le_add (hy.trans he) (c x u)).trans_eq (add_halves _)) -- lemma name
end Fervor
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier

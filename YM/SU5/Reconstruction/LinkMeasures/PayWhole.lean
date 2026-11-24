import YM.SU5.Reconstruction.LinkMeasures.Preferred
import YM.SU5.Reconstruction.FirstWindows.Value
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satori
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Tapestry
open Tower Tower.SatinVerification PaymentCamera
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    (V:Universal Y H i k I E)(G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (S:Finset Cover)(s:ℕ)(w:Evens S)
local notation "μS" => actual S Λ l
local notation "W" => wingspan Λ l S
local notation "Bx" => PhaseChoice.transfer Y H G S s
local notation "Tx" => singer S w
local notation "rᵢ" i1:max => i (G.rows i1)
local notation "rₖ" i1:max => k (G.columns i1)

open Tower.Vacancy Tower.Selected Tower.FirstWindows PaymentCamera
local notation "q★" => Satori.qty S Λ l
lemma ensemble (F:Swatch S): F= ∑ i:Evens S,singer S i (accession S (F i)):=by
 simp_rw [toneHere,known]; exact (Finset.univ_sum_single F).symm
lemma transfer_all (F:Swatch S): (Bx) F= ∑ x:Evens S,singleTicket Y H G S s x (accession S (F x)):=by
 nth_rw 1 [ensemble S F]; exact offerSum (T:=Swatch S) (U:=Swatch (W)) (Bx) (fun i:Evens S=> singer S i (accession S (F i)))
include V
/-- actual responses bounded in L1 input, no supremum over gauge fields -/
lemma weighIn: ∃ C:ℝ,0 ≤ C∧∀ f:Swatch S, ‖PhaseChoice.transfer Y H G S s f‖ ≤ C * qty S Λ l f:=by
 choose A v using fun w:Evens S=> offers_funds (E:=Swatch (W)) (actual S Λ l) (singleTicket Y H G S s w) (Council.reservation (E:=Swatch (W)) _ _ _ (crop_round Y H V G S s w))
 let c:=∑ i:Evens S,|A i|; refine ⟨c, Finset.sum_nonneg (fun _ _=> abs_nonneg _), fun f=> ?_⟩; rw [transfer_all]; refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun i=>c*bill (actual S Λ l) (accession S (f i))) ?_).trans_eq ?_); swap
 · unfold qty; rw [Finset.mul_sum]
 intro i _; exact (v i _).trans (mul_le_mul_of_nonneg_right ((le_abs_self (A i)).trans (single_le_sum (fun i _=>abs_nonneg (A i)) (mem_univ _))) (PaymentCamera.bill_nonneg μS _))
-- useful general $L1 feasible costs on any compact$ checkpoint
lemma royalties: ∃ C:ℝ,∀ f g:Swatch S, dist ((Bx) f) ((Bx) g) ≤ C * qty S Λ l (f-g):=by
 obtain ⟨A,b,h⟩:=weighIn Y H V G S s; refine ⟨A,fun f g=>?_⟩; rw [dist_eq_norm]; have ht:=h (f-g); rw [offerDiff (T:=Swatch S) (U:= Swatch W)] at ht; exact ht
lemma suggestions(x:Swatch S) (b:Bool)(p:b=true→Neutral K (render S K x)):
    ∃ f:ℕ→ Swatch S,(∀ i,f i∈ literal S∧ (b=true→Neutral K (render S K (f i)))) ∧ Tendsto (fun i=> PhaseChoice.transfer Y H G S s (f i)) atTop (𝓝 (PhaseChoice.transfer Y H G S s x)) ∧ Tendsto (fun i=> q★ (f i-x)) atTop (𝓝 0):=by
 obtain ⟨m,e⟩:= (Buffered.separates K S).exists; let δ(k:ℕ):ℝ:= 1 / ((k:ℝ)+1); have hd (k): 0<δ k:=by unfold δ; positivity
 have h(k:ℕ):∃ a:Swatch S, (a∈ literal S∧ (b=true→Neutral K (render S K a)))∧ qty S Λ l (a-x)≤ δ k:=by
    cases b;· obtain ⟨a,w,v⟩:= billable S Λ l x _ (hd k); exact ⟨a,⟨w,nofun⟩,v⟩
    obtain ⟨a,w,z,v⟩:= literal_neutral S K m ⟨e⟩ Λ l x (p rfl) _ (hd k); exact ⟨a,⟨w,fun _=> z⟩,v⟩
 choose f t g using h
 have hx:Tendsto (fun i=> q★ (f i-x)) atTop (𝓝 0):= squeeze_zero (fun n=>stays_nonneg ..) g (show Tendsto δ atTop (𝓝 0) from tendsto_one_div_add_atTop_nhds_zero_nat)
 obtain ⟨C,a⟩:= royalties Y H V G S s
 refine ⟨f,t, tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun n=> dist_nonneg) (fun n=> a _ _) ?_),hx⟩
 simpa only [mul_zero] using hx.const_mul C

omit V
lemma step_badge (x:Swatch S): spreadTo Y H G s (s+1) (badge K S x)= badge K (W) (Bx x):=by
 apply Subtype.ext; rw [spreadTo_val,domTag,domTag,show s+1-s=1 by omega,←PhaseChoice.transferred]; rfl
open Tower.SlabMark
include V
lemma E_lookup : Continuous (fun x:Swatch S=> E s (render S K x)):=by
 let L:= (beforeSelection Y H V s).comp (badge K S); let T:= L.mkContinuous (toll Y H s S *spread S) fun x=>by
    change ‖E s (render S K x)‖≤ _; rw [mul_assoc]; exact E_bound Y H V s S (texture S K x) (fun i x₀=> Tapestry.renderLe ..)
 exact T.continuous

variable (j:Axis) (C:Arena Y H G.history.circuit j 0 false)
variable (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
lemma X_lookup : Continuous (fun x:Swatch S => oneAt Y H V G j C χ s (badge (tent Y H) S x)):=by
 let L : Swatch S → (displayAlgebra Y H V G.history G.clipped j false C) := (fun x=> located Y H V s G.history G.clipped j false C (Selected.labelL Y H S x))
 exact (show Continuous χ from open CStarAlgebra in map_continuous χ).comp (show Continuous L from Continuous.subtype_mk (cap_fee Y H V s G.history G.clipped j C S) _)
lemma E_progress (x:Swatch S): E s (render S K x)= E (s+1) (render (W) K (Bx x)):=by
 have h:= before_spread Y H V G (Nat.le_succ s) (badge K S x); rw [step_badge] at h; exact h.symm
lemma X_progress (x: Swatch S): oneAt Y H V G j C χ s (badge (tent Y H) S x)=oneAt Y H V G j C χ (s+1) (badge (tent Y H) (W) (Bx x)):=by
 have h:= oneAt_spread Y H V G j C χ (Nat.le_succ s) (badge K S x); rw [step_badge] at h; exact h.symm
end YM.CF.Buffered.Afterglow.Satori
#print axioms YM.CF.Buffered.Afterglow.Satori.suggestions
#print axioms YM.CF.Buffered.Afterglow.Satori.X_lookup
#print axioms YM.CF.Buffered.Afterglow.Satori.X_progress

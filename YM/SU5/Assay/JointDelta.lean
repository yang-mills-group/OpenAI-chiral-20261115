import YM.SU5.Assay.SlotDelta
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-!
 Raw comparison stored for pairs, accepts two different widths and
 frames, either label reversed on each.
-/
lemma vacant_norm : ‖(Vac)‖=1:=P.norms_color ..
lemma vacant_pay (T:X): ‖inner ℂ (Vac) (T (Vac))‖≤ ‖T‖:=by
 apply (norm_inner_le_norm ..).trans
 refine (mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)).trans ?_
 rw [P.vacant_norm,one_mul,mul_one]
lemma vacant_diff (T M:X): ‖inner ℂ (Vac) (T (Vac))-inner ℂ (Vac) (M (Vac))‖≤‖T-M‖:=by
 rw [←inner_sub_right];exact P.vacant_pay j x (T-M)

private lemma multi_cost {T₁ T₂ M₁ M₂:X}{p q u v:ℝ}
 (h:‖T₁-M₁‖≤p)(e:‖T₂-M₂‖≤q)(k:‖M₁‖≤u)(i:‖T₂‖≤v): ‖T₁*T₂-M₁*M₂‖≤p*v+q*u:=by
 rw [show T₁*T₂-M₁*M₂=(T₁-M₁)*T₂+M₁*(T₂-M₂) by rw [_root_.sub_mul,mul_sub];abel,mul_comm q u]
 exact (norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul h i (norm_nonneg _) ((norm_nonneg _).trans h)))
   ((norm_mul_le ..).trans (mul_le_mul k e (norm_nonneg _) ((norm_nonneg _).trans k))))
variable {P j x}{Z Z':Ballad.Lead.Clan}
local notation "σ"=>P.rawSlot j
local notation "ι"=>P.walk j
open Glaze
lemma joint_negligible (R₁:P.Reel j Z)(R₂:P.Reel j Z'){A A':ℕ→P.Glaze}(F G:SampleDose)(h:Grows j A)(w:Grows j A'):
 ∃d, Tapers d∧∀{a b c e s} t m n z,Walled j F a b ((serial (R₁.wrapMix A) s).realWidth P j)→
   Walled j G c e ((serial (R₂.wrapMix A') s).realWidth P j)→
   ‖(σ z t (ι m (serial (R₁.wrapMix A) s)) a b F)*(σ z t (ι n (serial (R₂.wrapMix A') s)) c e G)-
     (σ z t (ι m (serial A s)) a b F)*(σ z t (ι n (serial A' s)) c e G)‖≤d s:=by
 obtain ⟨p,i₁,w₁⟩:= R₁.negligible F h
 obtain ⟨q,i₂,w₂⟩:= R₂.negligible G w
 obtain ⟨u,j₁,z₁⟩:= rolling_slot F h
 obtain ⟨v,j₂,z₂⟩:= rolling_slot G (R₂.stays_paid w)
 refine ⟨_,(i₁.product j₂).add (i₂.product j₁),?_⟩
 intro a b c e s t m n x h₁ h₂
 exact P.multi_cost j x (w₁ t m x h₁) (w₂ t n x h₂) (z₁ a b s t m x) (z₂ c e s t n x)

-- Consequence for holders: any grid convergence in our rehearsal
-- sense has its SAME reading after wrapping. Here it suffices to
-- state one fixed orientation; permanent cost above even varying both.
lemma Reel.wrap_rehearses (r:P.Reel j Z){A:ℕ→P.Glaze}{F:SampleDose}(v:Tiny A)(h:Grows j A){a b:ℝ}(q:Walled j F a b 0)
 {I:Type*}{l:Filter I}{s t:I→ℕ}{m:Bool}{T:(P.ManyF j x).Op}(k:Tendsto s l atTop)
 (p:P.Rehearses j x (fun i=>σ x (t i) (ι m (serial A (s i))) a b F) l T):
 P.Rehearses j x (fun i=>σ x (t i) (ι m (serial (r.wrapMix A) (s i))) a b F) l T:=by
 obtain ⟨d,w,e⟩:=r.negligible F h
 exact p.squeeze' (w.off.comp k) ((k.eventually ((r.stays_tiny v).fades.room q)).mono fun i n=> e _ _ _ n)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

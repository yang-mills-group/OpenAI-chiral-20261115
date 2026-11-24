import YM.SU5.FiniteGaugeData.Tower.BoxWorks
import YM.SatinExist.Mast
-- Strengthened op pricing. Cp8.a. Follow PowerCap/EndTrain/StationRide, but get the NEW constant for actual mosaic pricing.
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5900
set_option maxHeartbeats 390000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
section queue
open Analysis
variable {Kp:Calibration}{A B:ℕ→Family Kp}{F G:Family Kp}{S T:Finset Cover}
lemma BQueue.again (p:BQueue S A F) (u:BQueue T B G) : BQueue (S∪T) (fun i=>A i+B i) (F+G):=by
 obtain ⟨t,h,⟨C,f,a,b'⟩,e⟩:=p; obtain ⟨q,h',⟨D,g,c,d⟩,e'⟩:=u
 have ad{F G:Family Kp}{a b:ℝ}(p:pay F a)(u:pay G b): pay (F+G) (a+b):=fun i w=> (norm_add_le ..).trans (add_le_add (p ..) (u ..))
 refine ⟨fun i=> ((t i).mono subset_union_left).add ((q i).mono subset_union_right), (h.mono subset_union_left).add (h'.mono subset_union_right),⟨C+D,by positivity,ad a c,(b'.and d).mono fun i ⟨p,q⟩=>ad p q⟩,fun i v=>?_⟩
 filter_upwards [e (i/2) (half_pos v),e' (i/2) (half_pos v)] with n w f'; rw [show A n+B n-(F+G)=(A n-F)+(B n-G) from by abel]; have h:=ad w f'; rwa [add_halves] at h
lemma BQueue.enroute {z:ℕ→ℂ}{b:ℂ}(e:Tendsto z atTop (𝓝 b))(p:BQueue S A F):BQueue S (fun i=>z i • A i) (b • F):=by
 obtain ⟨t,h,⟨C,f,a,b'⟩,d⟩:=p; let c:=‖b‖+1; have hp:‖b‖<c:= lt_add_of_pos_right _ (by norm_num); have hv:0<c:=(norm_nonneg _).trans_lt hp
 have sc{F:Family Kp}{z:ℂ}{x y:ℝ}(h:pay F y)(p:‖z‖≤x): pay (z•F) (x*y):=fun n w=> (pay_scale h z n w).trans (mul_le_mul_of_nonneg_right p (pay_nonneg h))
 let hz:=e.norm.eventually (ge_mem_nhds hp)
 refine ⟨fun i=>InTest.smul _ (t i),InTest.smul _ h,⟨c*C,mul_pos hv f,sc a hp.le,(b'.and hz).mono fun i h=>sc h.1 h.2⟩,fun i v=>?_⟩
 let ε:= i/(c+C); have h0:0<ε:=div_pos v (by positivity)
 let E:= (Metric.tendsto_nhds.mp e) ε h0
 filter_upwards [hz,E,d ε h0] with n p e g
 rw [show z n • A n - b • F= z n • (A n-F)+(z n-b)•F from (by module)]
 rw [dist_eq_norm] at e
 intro j x; refine ((norm_add_le ..).trans (add_le_add (sc g p j x) (sc a (show ‖z n-b‖ ≤ ε from e.le) j x))).trans_eq ?_; change c*ε+ε*C=i; have he: ε*(c+C)=i:=div_mul_cancel₀ _ (by positivity); nlinarith
variable {τ:ℕ→ℕ} (q:StrictMono τ)
include Q q
lemma gleam_path : Coherent (i:=i) (k:=k) (E:=E) Y H D (a∘τ) (b∘τ):=by
 refine ⟨Q.circuit,Q.growsA.comp q,Q.growsB.comp q,fun i=> Q.gate _,fun s=> q.tendsto_atTop.eventually (Q.finance s),fun s S=>?_⟩
 obtain ⟨C,h,p⟩:= Q.implements s S; exact ⟨C,h,fun e v=> q.tendsto_atTop.eventually (p e v)⟩
-- box norms transfers proof irrelevance even path refinements. test by itinerary
lemma lift_box_glimmer (V:Universal Y H i k I E)(Qt:Clipped Y H (i∘a) (k∘b))(j:Axis)(C:Arena Y H Q.circuit j 0 false)(w:ℕ)(p:0<w)(h:Entry Y H s j false w): boxOp Y H V s (gleam_path Y H Q q) (show Clipped Y H _ _ from fun s=> q.tendsto_atTop.eventually (Qt s)) j false C w h p=boxOp Y H V s Q Qt j false C w h p:=by
 apply test_high Y H V s Q j false C -- check
 intro i l z; simp only [snatch Y H V s _ _ _ _ _ _ _ _ l z]
 exact congrArg (fun u=> (actor Y H i Q.circuit j 0 false C) (slabT Y H i j false _ u z)) rfl -- defeq? furn uses q, proof P?
end queue
end YM.CF.Buffered.Afterglow.Tower.SlabMark

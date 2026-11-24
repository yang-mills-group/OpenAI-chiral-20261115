import YM.SU5.Reconstruction.Cashier.Save
/-! Move-to-target and warm grant. (port of useful lemma from Baggage) -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
section drives
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (j:Axis)(w:ℕ)(f:Family (tent Y H))(S:Finset Cover)(t:InTest (tent Y H) true S false f)(hB:Between (tent Y H) j 0 (ruler Λ.block*w) S)
local notation "π" r:max=>i (a r)
local notation "ζ" r:max=> k (b r)
local notation "Z" u:max r:max=> train Y H s u (π r) (ζ r) S f
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> (L₀^t*w)
local notation "b₀"=>ruler Λ.block
variable (Qt : Clipped Y H (i∘a) (k∘b))(hw:0 < w)
include V Q
lemma hot_skim (ψ:ℕ→ℕ) (vψ:Tendsto ψ atTop atTop) {F:ℕ→Family K}(p:BQueue S F f): Tendsto (fun i=>hot Y H s (π (ψ i)) (ζ (ψ i)) (F i)) atTop (𝓝 (E s f)):=by
 obtain ⟨g,h,_,x⟩:=p; let u:=heatwave Y H V s Q (aux_test h)
 obtain ⟨d,v⟩:=Tower.sizes S
 let D':=Grip Y H s d; have ht:0≤ D':= (Real.exp_pos _).le
 refine Metric.tendsto_nhds.mpr fun ε e=>?_
 let C:=ε/(2*(D'+1)); have hC:0<C:=div_pos e (by positivity)
 have hx:D'*C<ε/2:=by have hp:C*(2*(D'+1))=ε:=div_mul_cancel₀ _ (by positivity); nlinarith
 filter_upwards [x C hC, vψ.eventually (V.pick.grow_i.tendsto_atTop.comp Q.growsA.tendsto_atTop|>.eventually (tandem Y H s d)), vψ.eventually (Q.finance s),Metric.tendsto_nhds.mp (u.comp vψ) (ε/2) (by positivity)] with i hp hq p t
 let I0:=F i-f
 have he: ‖hot Y H s (π (ψ i)) (ζ (ψ i)) I0‖ ≤D'*C:=by
    have ht':CompactArc ∅ d:=fun i=>⟨0,by simp⟩; have hw:= hq (ζ (ψ i)) p (InTest.subOp (g i) h) (show InTest K true ∅ false 1 from InTest.one) v ht' C 1 hp (fun _ _=>by exact norm_one.le)
    simpa only [mul_one,I0,D',Function.comp_apply] using hw
 rw [show hot Y H s (π (ψ i)) (ζ (ψ i)) I0= hot Y H s (π (ψ i)) (ζ (ψ i)) (F i)-hot Y H s (π (ψ i)) (ζ (ψ i)) f from ?_] at he
 · exact lt_of_le_of_lt (dist_triangle _ (hot Y H s (π (ψ i)) (ζ (ψ i)) f) _) (by rw [dist_eq_norm]; simp only [Function.comp_apply] at t; linarith)
 unfold I0; rw [sub_eq_add_neg,← neg_one_smul ℂ f, hot_add Y H s (aux_test (g i)) ((aux_test h).scale _) p,hot_mul Y H s _ p]; simp [sub_eq_add_neg]
omit V Q

open Tapestry
open SatinVerification
variable {F: Swatch (wingspan Λ l S)}{ψ:ℕ→ℕ}(G:GroundExtension (i:=i) (k:=k) (E:=E) Y H) (u:ℕ→ Swatch S)
 (vψ: Tendsto ψ atTop atTop) (p: Tendsto (fun i=> PhaseChoice.transfer Y H G S s (u (ψ i))) atTop (𝓝 F))
local notation "Rx"=>render S (tent Y H)
local notation "Ry"=>render (wingspan Λ l S) (tent Y H)
local notation "W₁" i:max=> PhaseChoice.transfer Y H G S s (u i)
local notation "I₁" r:max=>i (G.rows r)
local notation "I₂" r:max=>k (G.columns r)
local notation "Zh" u:max r:max f:max=> train Y H s u (I₁ r) (I₂ r) S f
variable (a₀:ℝ)(h₀:0<a₀)(hA:∀i, pay (render S (tent Y H) (u i)) a₀)
/-- Keep progress on NEXT LEVEL's TARGET too, rather than assume approximating f converges. -/
def goal (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)(r:ℕ)(F: Swatch (wingspan Λ l S)) := stream Y H G.refine (s+1) r ((Ry) F)
include p vψ hA h₀
lemma sponsored (r:ℕ): BQueue (W (r+1)) (fun i=>Zh (r+1) (ψ i) ((Rx) (u (ψ i)))) (goal Y H s S G r F) :=by
 let x(i):=(Rx) (u (ψ i)); let K₁:= goal Y H s S G r F
 obtain ⟨C,a,b⟩:= fares Y H s G.history S (r+1)
 obtain ⟨D,a',b'⟩:=fares Y H (s+1) G.history (wingspan Λ l S) r
 have he:InTest K true (W (r+1)) false K₁:=by rw [around_succ]; exact (proceeds Y H G.history.circuit (s+1) r (texture (wingspan Λ l S) K F)).1
 refine ⟨fun i=> prepared_train Y H s S _ _ _ (texture ..),he,?_,?_⟩
 · obtain ⟨a₁,h0⟩:=valuation Y H he
   refine ⟨max (C*a₀) a₁,lt_max_of_lt_left (by positivity),fun i x=>(h0 i x).trans (le_max_right ..),?_⟩
   exact (vψ.eventually (b 1 zero_lt_one)).mono fun i h n x=> ((h _ (texture _ K (u (ψ i))) a₀ (hA (ψ i))).2.1 n x).trans (le_max_left ..)
 intro ε e
 let B':ℝ:= spread (wingspan Λ l S)
 have hp:0≤B':=Nat.cast_nonneg _
 have hx:0< B'+1:=by positivity
 filter_upwards [vψ.eventually (b (ε/(2*a₀)) (by positivity)), Metric.tendsto_nhds.mp p (ε/(2*(D*(B'+1)))) (by positivity), b' 1 zero_lt_one] with i c t h
 let Z':= Zh (r+1) (ψ i) (x i)
 let L:= stream Y H G.refine s (r+1) (x i)
 let f':=W₁ (ψ i)
 have hL:L=goal Y H s S G r f' := by unfold L goal; rw [upstairs,show G.refine s (x i)=(Ry) f' from PhaseChoice.transferred ..]
 have hf:pay (L-K₁) (ε/2):=by
    rw [hL]; have H₂ : goal Y H s S G r f'-K₁=goal Y H s S G r (f'-F):=by
       unfold K₁ goal; rw [map_sub]; rw [sub_eq_add_neg ((Ry) f'),← neg_one_smul ℂ ((Ry) F), woven_add Y H G.history.circuit (s+1) _ (aux_test (texture ..)) ((aux_test (texture _ K F)).scale _),woven_smul Y H G.history.circuit _ _ (aux_test (texture ..)),neg_one_smul]; rfl -- sub form
    rw [H₂]; intro n g
    rw [dist_eq_norm] at t; have ht:‖f'-F‖<ε/(2*(D*(B'+1))):=t
    have hy:0≤‖f'-F‖:=norm_nonneg _
    refine ((h ((Ry) (f'-F)) (texture ..) _ (PhaseChoice.rendered_price Y H (wingspan Λ l S) (f'-F))).1 n g).trans ?_
    change D*(B'*‖f'-F‖) ≤ ε/2
    have x:=mul_lt_mul_of_pos_left ht (by positivity:0<2*(D*(B'+1))); rw [mul_div_cancel₀ _ (by positivity:2*(D*(B'+1)) ≠ 0)] at x
    nlinarith
 have hk:=pay_add ((c _ (texture ..) a₀ (hA (ψ i))).2.2.1) hf
 change pay (Z'-K₁) ε
 have h: (ε/(2*a₀)*a₀+ε/2)=ε:=by field_simp; ring
 rw [h,show Z'-L+(L-K₁)=Z'-K₁ from by abel] at hk; exact hk

include V hw hB
variable (wage: Rolls Y H s G (fun i => render S (tent Y H) (u i)) w)
include wage
-- cost at the NEXT frame with thickening EXACT one step, at each further height.
lemma landed : ∀ (r d:ℕ)(T:Finset Cover)(A:ℤ)(h:0≤A)(x:Family (tent Y H)),InTest K true T false x→Between (tent Y H) j (2*(ruler Λ.block*((L₀:ℤ)^r*(L₀*w:ℕ)))) A T→ CompactArc T d→∀ C:ℝ,0<C→pay x C→
 ∀ n:ℕ, ‖E (s+1+r) (chambers j ((L₀:ℤ)^r*(L₀*w:ℕ)) 0 (goal Y H s S G r F) x n)‖≤ wages K (duetCharge Y (s+1+r)) d A C * rate^n:=by
 intro r d T A h x hx ha ht C c y n
 obtain ⟨w₁,hT⟩:= BQueue.chambersS j (uM (r+1)) n 0 (sponsored Y H s S G u vψ p a₀ h₀ hA r) (BQueue.stay hx c y)
 have hh:= (hot_skim Y H V (s+(r+1)) G.history _ w₁ ψ vψ hT).norm
 have he : (L₀:ℤ)^r*(L₀*w:ℕ)=uM (r+1):=by push_cast; rw [pow_succ]; ring
 rw [he] at ha ⊢; rw [show s+1+r=s+(r+1) from by omega]
 apply le_of_tendsto hh; exact (vψ.eventually (gets Y H V s G j w _ S (fun i=>texture S K (u i)) hB a₀ hA wage hw _ n d _ C h)).mono fun i t=> t n le_rfl x T hx ha ht y
end drives
end YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll.landed

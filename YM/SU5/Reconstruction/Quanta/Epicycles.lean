import YM.SU5.Reconstruction.Quanta.Garret
import YM.SU5.FiniteGaugeData.Tower.Performed
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)

/-! # Lift the actual POS witnesses even odd. Resolution keeps parity upon transfer. -/
open QuantaCore NorthTapes
namespace Garret
variable {g₀:Bool}{S Z:Finset Cover}{f g:Family (tent Y H)}
local notation "W" =>wingspan Λ l
local notation "B" => Λ.block
local notation "L"=>Λ.R.L.val

variable (a:Axis)(z:ℤ)
local notation "W₀" t:max=> volumeAround Λ l t
include Y H in
lemma parades (p:region a z (reserve Λ l) S)(n:ℕ): region a ((Λ.R.L.val:ℤ)^n*z) (reserve Λ l) ((W₀ n) S):=by
 -- Y needed
 induction n with
 | zero=>simpa [volumeAround] using p
 | succ n ih=> rw [pow_succ',mul_assoc,volumeAround]; exact wingspan_region Y H _ a _ ih
variable (ν w:ℕ)
-- shipping repeated, at every epoch n independently for the Fock test inputs; keep qualifications.
def quarry (g₀:Bool)(S:Finset Cover)(f:Family (tent Y H))(r:ℕ): Family (tent Y H) := Nat.rec f (fun t x=> pick Y H (s+t) ν w g₀ ((W₀ t) S) x) r
local notation "v₀" q:max =>((Λ.R.L.val:ℤ)^q*z)
local notation "Pm" z:max => poleForm K a z
variable {a₀ b:ℕ→ℕ}{D:ℕ→Family (tent Y H)→Family (tent Y H)}(Q: Coherent (i:=i) (k:=k) (E:=E) Y H D a₀ b)
local notation "π₀" r:max=>i (a₀ r)
local notation "κ" r:max=>k (b r)
local notation "tr" r:max t:max S:max F:max=> train Y H s t (π₀ r) (κ r) S F
local notation "Qr" r:max g:max S:max f:max t:max=> quarry Y H s (π₀ r) (κ r) g S f t
local notation "Ft" k:max S:max g:max p:max=> InTest K true ((W₀ k) S) g p
local notation "hv" t:max m:max => ((tent Y H).c (momentm Y m t))
lemma pollsAt {f:Family (tent Y H)}{e':ℕ}(h:Tivoli (wingspan Λ l S) ((tent Y H).c (momentm Y ν ((s+e')+1))))(v: legalAt Y (s+e') ν w)
   (r:InTest K true S g₀ f): InTest K true (wingspan Λ l S) g₀ (pick Y H (s+e') ν w g₀ S f) ∧ distribute Y H ((s+e')+1) ν (pick Y H (s+e') ν w g₀ S f)= aboveD Y H (s+e') ν w f:=lamp_jump Y H (s+e') ν w v r h
-- statement INCLUDES use of the real advance on all epochs
include V Q
variable (S)
lemma certified (t:ℕ):∀ᶠ r in atTop,∀ u:ℕ, u<t→∀ (g₀:Bool)(f:Family (tent Y H)), InTest K true ((W₀ u) S) g₀ f→
 let x:=pick Y H (s+u) (π₀ r) (κ r) g₀ ((W₀ u) S) f;
 legalAt Y (s+u) (π₀ r) (κ r) ∧ Ft (u+1) S g₀ x∧distribute Y H ((s+u)+1) (π₀ r) x= aboveD Y H (s+u) (π₀ r) (κ r) f:=by
 suffices h:∀ᶠ r in atTop, ∀ u∈ Finset.range t, Tivoli ((W₀ (u+1)) S) (hv ((s+u)+1) (π₀ r)) ∧ Ferry Y (s+u+1) (π₀ r) (κ r) by
    filter_upwards [h] with r v u g b' f z; obtain ⟨e,T⟩:= v u (Finset.mem_range.mpr g); let h':legalAt Y (s+u) (π₀ r) (κ r):= ⟨T.depth,T.enters⟩; exact ⟨h',pollsAt Y H s _ _ e h' z ⟩
 rw [Finset.eventually_all]; intro u _; exact (((V.pick.grow_i.comp Q.growsA).tendsto_atTop).eventually (turning Y H ((s+u)+1) ((W₀ (u+1)) S))).and (Q.finance _)
lemma living (t:ℕ):∀ᶠ r in atTop,∀ (u:ℕ),u≤ t→∀ (f:Family (tent Y H)) (g₀:Bool), InTest K true S g₀ f → Ft u S g₀ (Qr r g₀ S f u):=by
 filter_upwards [certified Y H V s S Q t] with r v u u' f b h
 induction u with
 | zero=>exact h
 | succ u ih=> exact (v u (by omega) b _ (ih (by omega))).2.1 -- uh x reduc
local notation "Zx" t:max=> reflectedBox a (v₀ t) ((W₀ t) S)
local notation "Cr"=> (2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l))
lemma increment {t:ℕ} (Z:Finset Cover)(u:region a z (reserve Λ l) S) : ∀ᶠ r in atTop, ∀ k' : ℕ, legalAt Y (s+t) (π₀ r) k'→∀ (F F':Family (tent Y H))(g₀:Bool), Ft t S g₀ F→ Ft t S g₀ F'→ InTest K true Z false ((Pm (v₀ t)) g₀ F F')→
 block Y H (s+t) (π₀ r) k' Z ((Pm (v₀ t)) g₀ F F')= (Pm (v₀ (t+1))) g₀ (pick Y H (s+t) (π₀ r) k' g₀ ((W₀ t) S) F) (pick Y H (s+t) (π₀ r) k' g₀ ((W₀ t) S) F'):=by
 let H': Tendsto (fun r=>(π₀ r)) atTop atTop:= (V.pick.grow_i.comp Q.growsA).tendsto_atTop
 let s₀:=s+t; let S₁:=(W₀ t) S; let S₂:=volumeAround Λ l (t+1) S; have ht:=parades Y H a z u t
 have he:v₀ (t+1)= (Λ.R.L.val:ℤ)*(v₀ t):=by rw [pow_succ',mul_assoc]
 filter_upwards [H'.eventually ((momentum Y (s+t)).eventually (wrapped_far (tent Y H) Cr (Zx t) S₁ ((mirror_detached Λ l ht ht).act Λ l))), H'.eventually (turning Y H ((s+t)+1) S₂),H'.eventually (turning Y H ((s+t)+1) (wingspan Λ l Z)), H'.eventually (turning Y H ((s+t)+1) (wingspan Λ l Z ∪(Zx (t+1)∪ S₂)))] with r w p z' e k' t F G g₀ f g z -- tune var t conflict
 rw [he] at e ⊢; exact consumes Y H _ _ _ t a _ f g z w p z' e
lemma reaches (Z:Finset Cover)(t:ℕ)(u: region a z (reserve Λ l) S) :∀ᶠ r in atTop,∀ (g₀:Bool)(F F':Family (tent Y H)),InTest K true S g₀ F→InTest K true S g₀ F'→ InTest K true Z false ((Pm z) g₀ F F') →
 train Y H s t (π₀ r) (κ r) Z ((Pm z) g₀ F F') = (Pm (v₀ t)) g₀ (Qr r g₀ S F t) (Qr r g₀ S F' t):=by
 induction t with
 | zero=>exact Eventually.of_forall fun _ _ F F' _ _ _=>by simp only [train,quarry,pow_zero,one_mul,Nat.rec_zero]
 | succ t ih=>
   filter_upwards [ih,increment Y H V s S a z Q (t:=t) ((W₀ t) Z) u,living Y H V s S Q t, Q.finance (s+t+1)] with r e u v w b' f g hf hg hp
   let f₀:= Qr r b' S f t; let g₁:= Qr r b' S g t; have ht: InTest K true ((W₀ t) Z) false ((Pm (v₀ t)) b' f₀ g₁) := by rw [← e b' f g hf hg hp]; exact prepared_train Y H s Z t _ _ hp
   rw [train_step,e b' f g hf hg hp]; exact u (κ r) ⟨w.depth,w.enters⟩ f₀ g₁ b' (v t le_rfl f _ hf) (v t le_rfl g _ hg) ht
-- need also even privileges if f/g require gauge.Cp next
end Garret
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.certified
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.living
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.reaches

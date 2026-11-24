import YM.SU5.Reconstruction.Oblique.Consulting
import YM.SU5.Reconstruction.Oblique.TiltAxis
import YM.SU5.Selected.Recolor
/-! # accounting through the coherence costs of this law. It REALLY buys invariance under cusp of the tower operation, not assuming approximate artifacts from different election. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Tilted
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance
  Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin SatinVerification
open Wilson FullBill Tapestry Tapestry.Altitude Spark
variable {Λ:Preparation}{l:ℕ}(Y: Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
variable {i k: ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V: Universal Y H i k I E)
variable (G: GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (P:Ramp)(s:ℕ)
local notation "K" => tent Y H
local notation "Ψ" => P.cuspF (tent Y H)
local notation "u" => i ∘ G.rows
local notation "w" => k ∘ G.columns
variable {S:Finset Cover}
private lemma distributes (m:ℕ) (f:Family K): distribute Y H s m (Ψ f)= P.bill (distribute Y H s m f):= by rw [Selected.display_eq_exhibit,Selected.display_eq_exhibit]; exact exhibits ..
private lemma above_tilt (m n:ℕ)(p:legalAt Y s m n){f:Family (tent Y H)}(x:InTest K true S false f): aboveD Y H s m n (Ψ f)=P.bill (aboveD Y H s m n f):=by
 change ascender Y s m n (distribute Y H s m (Ψ f))=_; rw [distributes]; exact ascends Y P m n s p ((stationed Y H s S m x).mono (Finset.subset_univ _))
include V
lemma level_price {f:Family (tent Y H)}(x: TestFamily K true f) : P.cuspF (tent Y H) (G.refine s f)=G.refine s (P.cuspF (tent Y H) f):=by
 obtain ⟨S,X⟩:= x.paid
 let W:=P.survey S; let X':=P.faces K X; let R(T:Finset Cover):= wingspan Λ l T; let T':= R W ∪ P.survey (R S)
 let Y₁(r:ℕ):= block Y H s (u r) (w r) S f; let Y₂(r:ℕ):=block Y H s (u r) (w r) W (Ψ f) -- notation prec expansion issue
 have he(A:Finset Cover):∀ᶠ r:ℕ in atTop,Tivoli A ((K).c (momentm Y ((u) r) (s+1))) := (V.pick.grow_i.comp G.history.growsA).tendsto_atTop.eventually (turning Y H (s+1) A)
 have hv :∀ᶠ r:ℕ in atTop,Y₂ r=Ψ (Y₁ r):=by
    filter_upwards [he (R W),he (R S),he T',G.history.finance (s+1)] with r a b p q
    have h:legalAt Y s (u r) (w r):=⟨q.depth,q.enters⟩
    refine stationary_ext Y H _ T' _ p.hosp ((booked Y H ..).mono (show R W⊆ T' from Finset.subset_union_left)) ((P.faces K (booked Y H ..)).mono (Finset.subset_union_right)) ?_
    unfold Y₁ Y₂; rw [distributes,reserved Y H s _ (u r) (w r) h X' a,reserved Y H s _ (u r) (w r) h X b]; exact above_tilt Y H P s _ _ h X
 funext m f'; let G₀: Fields _ := P.both ((tent Y H).c m) f'
 have E₁:= ((theta_cont (P.vehicle _)).continuousAt.tendsto.comp (Selected.recollects Y H s G.history X m G₀)); have E₂:=Selected.recollects Y H s G.history X' m f'
 exact tendsto_nhds_unique_of_eventuallyEq E₁ E₂ (hv.mono (fun r p=> (congrFun (congrFun p m) f').symm))
lemma every_price {f:Family (tent Y H)}(p:TestFamily K true f)(n:ℕ):stream Y H G.refine s n (P.cuspF (tent Y H) f)=P.cuspF (tent Y H) (stream Y H G.refine s n f):=by
 induction n with
 | zero=> rfl
 | succ n ih=>rw [stream_step,ih,stream_step,level_price Y H V G P _ (streams_test Y H G.history.circuit _ _ p)]
end YM.CF.Buffered.Afterglow.Tower.Tilted

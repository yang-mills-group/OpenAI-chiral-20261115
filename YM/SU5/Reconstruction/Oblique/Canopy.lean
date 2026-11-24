import YM.SU5.Reconstruction.Oblique.Approved
import YM.SU5.Reconstruction.Oblique.SupportRose
/-!
# Spin reading for the physical probes of this program. Weyl labels at each observing resolution.

Two maps to check (and keep distinct!): at each *height*, Spin is concrete Field Eu on the relevant insertion at that regulator.Odd physical spin convention in CP1; and on Dome.Follows/Observer Plab budget. Not conflating with assertion of continuum operator-valued Weyl fields. One can transport price of every inquiry of LinkCheck etc. including NoDecompose, being careful to FORM the product claims before using coherent lifts. Here using all same Y & orientations.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "wk" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (wk i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (wk i)
local notation "U₀" i:max=> mainsea Y H V G.history G.clipped i false (C i) (wk i)
local notation "A₀" i:max=> ride Y H V G.history G.clipped i false (C i) (wk i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (wk i)
local notation "Os" i:max=> OSvector Y H V G i (C i) (wk i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "ℜ" t:max=> Real.toNNReal (t:ℝ)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C a χ
local notation "au"=>move K
open LightBudget Chambers -- provide BootBacking later
local notation "Fs" i:max=> fort Y H V G.history G.clipped i false (C i) (wk i)
local notation "N" i:max=>Domain Y H G false (flank i 0)
local notation "V₀" i:max=>coreOs Y H V G i (C i) (wk i)
local notation "X₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (wk i)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (wk i)
local notation "℘" i:max=>Picket.trans (S₀ i)
local notation "Qv" i:max=> Follows Y H V G i (C i) (wk i)
local notation "π" i:max=> opCarries Y H V G i (C i) (wk i)
variable (P:Tilted.Ramp)
local notation "R₁"=> P.s * Signed.mirror P.a

-- explicitly use scale s Field test (before lifting into Domain). Reader. Genuine Spin portion and orientation in resolution. AxiSign. Keep appointments of slots, budgets true.Altitude. -/
noncomputable def clockwise(J: Calibration)(P:Tilted.Ramp)(x:Family J): Family J := P.cuspF J (mirror J P.a 0 x)
-- spin ratio in microscopic field convention `frame on Site,Pin on Single,unchanged Slots`. shape argument is passive R^-1 (sup moves by R).
open Fock Lat Mir Spire Rush Lifted Nacre Tulip -- avoid Domains
noncomputable def framePass (P:Tilted.Ramp) := joinX (plane P.a 0) P.plan
noncomputable def spinTurns (P:Tilted.Ramp): UNI SpinIdx:= P.reel*pinLift P.a
lemma spinUses: JetS (framePass P).s false false (spinTurns P):= jet_add false true true (Signed.mirror P.a) P.s (pinLift P.a) P.reel (mirrorX P.a) P.jet
lemma passiveUse (x:Cover): (framePass P).motion x= (P.s * Signed.mirror P.a)⁻¹.act x :=by
 unfold framePass; rw [palm,P.mode_motion, mul_inv_rev,Signed.act_mul]; simp [plane,Shape.motion,Tilted.Ramp.s_inv]
-- formulas at AP cut ($origin point or another height, ν$), all fermion slots are fixed (prep includes shifted basis with those slots by definition `inert`). Show in Frame basis.JetS proof. Paired matter from flop already checked in Bows. Rot viewpoint: $θ\theta$ includes extra square minus sign.
variable (J:Calibration)
noncomputable def particle(m: Side) (x:Ket (Single m)):= - CF.acts (prepU (framePass P) (spinTurns P) inert m).val x
private lemma lot_transform {I:Type*}[LinearOrder I][Fintype I](A B:UNI I)(x:Ket I): Fock.theta A (Fock.theta B (create x))= create (- CF.acts (A*B).val x):= by rw[theta_upV,theta_smul,theta_downV,← act_mul]; simp [smul_smul]
lemma atCreate(x:Cover)(a:SpinIdx)(b: SU.Slot)(m:Side)(u:Fields (J.c m)): clockwise J P (creation J x a b) m u= create (particle P (J.c m) (basisC (J.c m) x a b)) := by
 change Fock.theta (P.vehicle _) (Fock.theta (carR P.a 0 _) (create _))= _; rw [lot_transform]; unfold Tilted.Ramp.vehicle carR; rw [kio]; rfl
lemma atRemove(x:Cover)(a:SpinIdx)(b: SU.Slot)(m:Side)(u:Fields (J.c m)): clockwise J P (removal J x a b) m u = Fock.remove (particle P (J.c m) (basisC (J.c m) x a b)):= by
 change Fock.theta (P.vehicle _) (Fock.theta (carR P.a 0 _) (star (create _)))= _; rw [theta_star,theta_star]; exact congrArg star (atCreate P J x a b m u)
abbrev epoch (J:Calibration)(P:Tilted.Ramp)(f:Dome J):= (windTilt P J) (aureole J P.a 0 f)
lemma clockwise_epoch (f:Dome J): (epoch J P f).val= clockwise J P f.val:= rfl
include V
lemma epochSupport (s:ℕ)(T:Set RSpace)(q:Bool)(f:Dome K)(p:f∈insideAt Λ l K q T s): epoch (tent Y H) P f∈ insideAt Λ l K q ((P.s * Signed.mirror P.a).act '' T) s:= by
   have h:=protects P s _ _ _ (mirror_inside Y H P.a f s p); rw [wind_pin,image_image] at h; refine (show ((P.s*Signed.mirror P.a).act (R:=ℝ) = fun x:RSpace =>_) from funext (Signed.act_mul P.s (Signed.mirror P.a))) ▸ h -- eq orient
lemma keeps_epoch (s:ℕ)(f:Dome (tent Y H)): gust P K ((θ (P.a)) (ticket Y H G s f)) = ticket Y H G s (epoch K P f):=by rw [flipMark_ticket,gust_ticket Y H V]
variable (e:RPos Y H V G P C a χ)
include e
-- monetary valuations on any height-local Mark. Including any separated & combined Wick probes therein (see Authentication Ph.Point$) at Loose and Gauge. Exact distinction to unselected there via CP15.
lemma readsHere (s:ℕ)(f:Dome (tent Y H))(j z:Axis): sameRead Y H V G j (C j) (wk j) s f=sameRead Y H V G z (C z) (wk z) s (epoch K P f):= by
 unfold sameRead; rw [← whiff_turn Y H V G C a χ j,← whiff_turn Y H V G C a χ z]; have h:= (SpinOn Y H V G C a χ P e).fuel (ticket Y H G s f) (ticket_loose ..); rw [SpinsOn,keeps_epoch Y H V] at h; exact h.symm
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose

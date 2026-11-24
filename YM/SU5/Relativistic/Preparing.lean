import YM.SU5.Relativistic.BankSandwich
/-! # Preparation of every specified component by distant physical observations. -/
set_option autoImplicit false
set_option maxHeartbeats 470000
set_option maxRecDepth 6000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Scree Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark PhaseChoice Push.SectorMeasure
open Tapestry Tapestry.Altitude Tapestry.Exhibition MeshClock
open Tower.Selected Vacancy
open Journey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra

lemma near_inner {X:Hilbert} (w:X.Op)(x y:X)(u v:ℝ)(p:‖y‖ ≤ u)(q:‖x-y‖ ≤ v):
    ‖inner ℂ x (w x)-inner ℂ y (w y)‖ ≤ v*‖w‖*(u+v) + u*‖w‖*v := by
  have hx: ‖x‖ ≤ u+v := calc
   _ = ‖(x-y)+y‖ := by rw [sub_add_cancel]
   _ ≤ ‖x-y‖+‖y‖:= norm_add_le ..
   _ ≤ v+u := add_le_add q p
   _ = _:= add_comm ..
  rw [show inner ℂ x (w x)-inner ℂ y (w y) = inner ℂ (x-y) (w x)+ inner ℂ y (w (x-y)) from by rw [map_sub,inner_sub_left,inner_sub_right]; abel]; apply (norm_add_le ..).trans; rw [mul_assoc, mul_assoc u]; exact add_le_add ((norm_inner_le_norm ..).trans (mul_le_mul q ((w.le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))) (norm_nonneg _) ((norm_nonneg _).trans q))) ((norm_inner_le_norm ..).trans (mul_le_mul p ((w.le_opNorm _).trans (mul_le_mul_of_nonneg_left q (norm_nonneg _))) (norm_nonneg _) ((norm_nonneg _).trans p)))

lemma transfer_price {f g:ℕ→ℂ}{x:ℂ} (v:ℕ→ℝ)(h:Tendsto v atTop (𝓝 0))(t:Tendsto f atTop (𝓝 x))(p:∀ᶠ i in atTop, ‖g i-f i‖ ≤ v i): Tendsto g atTop (𝓝 x):=by
 apply tendsto_of_tendsto_of_dist t
 apply squeeze_zero' (Eventually.of_forall fun i=>dist_nonneg) _ h
 apply p.mono; intro i t; rw [dist_comm,dist_eq_norm]; exact t

section precursor
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    {L:Rack Λ l}{Θ:Clay Λ l} (D : Exhibition Y H i k I E L Θ)
local notation "V"=> D.univ_
variable (G:SatinVerification.GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j:Axis) (T : ∀ j:Axis,Arena Y H G.history.circuit j 0 false)
local notation "C"=> T j
local notation "ω"=> floorV Y H G.history.circuit j 0 false C
local notation "Φₛ" s:max=> Tower.Field Y H s j 0 false
local notation "κ" s:max=> actor Y H s G.history.circuit j 0 false C
local notation "Ω"=> groundRoom Y H V G.history j false C
local notation "ω₀"=> seat0 Y H V G.history j false C
local notation "A"=> displayAlgebra Y H V G.history G.clipped j false C
local notation "Λ₀"=> timeMesh Λ
local notation "L₀"=> Λ.R.L.val
local notation "H₀"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "B" n:max w:max z:max h:max=> boxOp Y H V n G.history G.clipped j false C w z h
variable (M:Panel Y H D.univ_ G.history G.clipped j false (T j)) (p:Issued Y H D.univ_ G.history G.clipped j false (T j) M)
variable (x : M.X)
local notation "χ"=> M.character x
local notation "R"=> SameCharacter.resident Y H V G j false C χ
local notation "Q"=> onDrawing Y H V G D j T R
local notation "Γ"=> Dome (tent Y H)
local notation "𝒞"=> Cloud (Dome (tent Y H))
local notation "U" x:max=> relocate K j x

structure Subscriber (x : M.X)(c : ∀ n:ℕ,Future Y H j n) : Prop where
  focus (v:Cloud (Dome (tent Y H)))(hp:v∈ FiniteGaugeDataPoly (tent Y H)):
    Tendsto (fun i=> vistaTake Y H D (v*Future.boundary Y H j (c i))) atTop
      (𝓝 (onDrawing Y H D.univ_ G D j T (SameCharacter.resident Y H D.univ_ G j false (T j) (M.character x)) v))
include p
lemma prepares : ∃ c : ∀ n:ℕ, Future Y H j n, Subscriber Y H D G j T M x c := by
  obtain ⟨f,h,t,e⟩:= OS.Ground.Panes.Shines.chosen_at ((A).subtype) (ω₀:Ω) p x
  let Y'(i:ℕ):groundRoom Y H V G.history j false C:= (f i).val ω₀
  let ε := propeller
  choose F z using fun i:ℕ=>Future.record Y H V G j C (Y' i) i (ε:=ε i) (by unfold ε propeller; positivity)
  refine ⟨F,⟨fun v p=>?_⟩⟩
  obtain ⟨s,y⟩:=Altitude.curve.mp p; let u:=vistaFinish Y H s D v; let o:=PhaseChoice.observe (show TestFamily K true u.val from u.property)
  obtain ⟨w,r,a,u'⟩:= buys_at Y H D j v s
  let X : (H₀).Op:= B s (w+w) a (by omega)
  let g: displayAlgebra Y H V G.history G.clipped j false C := Selected.located Y H V s G.history G.clipped j false C o
  let f'(i):= inner ℂ (Y' i) (g.val (Y' i))
  have hx : Q v=χ g := by
     rw [drawAt Y H V G D j T (SameCharacter.resident Y H V G j false C χ) y]; exact (evaluates Y H V G j T R s o).trans (SameCharacter.sameReading ..)
  have hf:Tendsto f' atTop (𝓝 (Q v)):= hx.symm ▸ e g
  let Z:= fun i=> ε i*‖X‖*(1+ε i) + 1*‖X‖*ε i
  have h': Tendsto ε atTop (𝓝 0):= propeller_fades
  have hq:Tendsto Z atTop (𝓝 0):=by simpa only [zero_mul,zero_add,mul_zero] using (((h'.mul_const ‖X‖).mul (h'.const_add 1)).add (h'.const_mul (1*‖X‖)))
  refine transfer_price Z hq hf ?_
  filter_upwards [eventually_ge_atTop w,eventually_ge_atTop s] with i b c
  let m:= Future.wait Y H j (F i)-L₀^((F i).t-s)*w
  let E':H₀:= actor Y H (F i).t G.history.circuit j 0 false C ((F i).irradiant Y H j m)
  let A':H₀:=(Y' i).val
  have hv: f' i= inner ℂ A' (X A'):= symmetric_box Y H D G j v s w r a u' C (Y' i)
  have hk: vistaTake Y H D (v*Future.boundary Y H j (F i))=inner ℂ E' (X E'):= Future.actualE Y H D G j (F i) C r y a u' c b
  rw [hk,hv]; exact near_inner X E' A' 1 (ε i) (h i).le ((F i).attends Y H V G j C (Y' i) (z i) m)
end precursor
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.prepares

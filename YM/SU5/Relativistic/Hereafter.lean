import YM.SU5.Relativistic.Preparing
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

-- a boundary solution may be pushed further; measure the marks after payment too
noncomputable def Future.reach {n:ℕ}(c:Future Y H j n)(u:ℕ) : Future Y H j n where
 t:=c.t
 arrival:=c.arrival
 mark:=Future.irradiant Y H j c u
 singlet:=by unfold Future.irradiant; rw [timed_apply]; exact chime_cov _ _ _ c.safe c.singlet
 S:= plow K j u c.S
 safe:=by unfold Future.irradiant; rw [timed_apply]; exact flow_port _ _ _ c.safe
 forward:=by
    intro i t; obtain ⟨i,v,rfl⟩:=plow_stays K j _ _ t
    rw [moves,if_pos rfl]; refine le_trans (c.forward i v) ?_; have he:0≤ ruler Λ.block*(u:ℤ):=mul_nonneg (ruler_gene _).le (by positivity); change i j ≤ i j+ruler Λ.block*(u:ℤ); linarith
lemma Future.at_zero {n:ℕ}(c:Future Y H j n) : (Future.reach Y H j c 0).mark = c.mark := tick_seed Y H c.t j 0 false c.mark
lemma Future.reach_dub {n:ℕ}(c:Future Y H j n)(u:ℕ) : Future.emit Y H j (c.reach Y H j u) = tick Y H c.t j 0 false (2*u) (Future.emit Y H j c):=by
 change tick Y H c.t j 0 false (2*Future.wait Y H j c) (tick Y H c.t j 0 false (2*u) c.mark)=_
 unfold Future.emit Future.irradiant
 rw [tick_tock,tick_tock,add_comm]
include p
lemma pushes_go : ∃ c : ∀ n:ℕ, Future Y H j n, Subscriber Y H D G j T M x c ∧ ∀ e:ℕ→ℕ, Subscriber Y H D G j T M x (fun n=>Future.reach Y H j (c n) (e n)) := by
  obtain ⟨f,h,t,e⟩:= OS.Ground.Panes.Shines.chosen_at ((A).subtype) (ω₀:Ω) p x
  let Y'(i:ℕ):groundRoom Y H V G.history j false C:= (f i).val ω₀
  let ε := propeller
  choose Xa Za using fun i:ℕ=>Future.record Y H V G j C (Y' i) i (ε:=ε i) (by unfold ε propeller; positivity)
  suffices hp : ∀ (F : ∀ n:ℕ, Future Y H j n), (∀ n:ℕ, ‖Future.root Y H G j C (F n) - ((Y' n).val:H₀)‖ ≤ ε n) → Subscriber Y H D G j T M x F from
    ⟨Xa,hp Xa Za,fun t=> hp _ (fun n=> Future.attends Y H V G j C (Xa n) (Y' n) (Za n) _)⟩
  intro F z; refine ⟨fun v p=>?_⟩
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
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.pushes_go

import YM.SU5.Reconstruction.Cross.Aperture
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set OS.Semigroup MeshClock Germ
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
local notation "Μ" => timeMesh Λ
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  {D : ℕ→Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i:=i) (k:=k) (E:=E) Y H D a b) (Qt : Clipped Y H (i∘a) (k∘b))
  (s : ℕ) (j : Axis) (C : Arena Y H Q.circuit j 0 false) -- aim all even incl characters extension
variable (c : (displayAlgebra Y H V Q Qt j false C) →⋆ₐ[ℂ] ℂ)
local notation "𝔄" => driveAlgebra Y H V Q Qt j false C
local notation "ρ" => indoor Y H V Q Qt j false C c
local notation "Ρ" => procession Y H V Q Qt j false C c
local notation "Ω" => doorstep Y H V Q Qt j false C c
local notation "Eχ" s:max => Selected.response Y H V s Q Qt j false C c
local notation "Ex" => ride Y H V Q Qt j false C c
local notation "Φ" t:max => Tower.Field Y H t j 0 false
local notation "T" n:max => Selected.bud Y H V n Q Qt j false C c
-- Γ-to-high-rung actual steps
noncomputable abbrev ambient {M:Mesh} {H:Hilbert} {j:Axis} (S:Germ.Alliance (Trans j) (marks M) H)
    (u:seeMesh M) : H.Op := S.raw (look j) (fun i=> u i.val)
noncomputable abbrev street (x : Cover) (j : Axis) : Trans j → ℤ := fun i=> x i.val
local notation "U" x:max => ambient (M:=timeMesh Λ) (turnstile Y H V Q Qt j false C c) x
local notation "Β" f:max h:max => entrance Y H V s Q Qt j false C f h
local notation "Π" x:max => (Ρ x)
local notation "r" v:max => SlabMark.relocate K j v
local notation "π" v:max => cad K (spare j (look j)) v
local notation "G" v:max f:max => Vacancy.chart K v f
local notation "Ξ" f:max v:max => relocateWorld Y H false v f
local notation "g₀" s:max v:max => grid Μ s v
local notation "GU" s:max v:max => toR (M:=Μ) (grid Μ s v)
local notation "δ" f:max t:max => upGrade Y H s Q false f t
local notation "MG" q:max i:max => MeshClock.acts (timeMesh Λ) s q i
local notation "σ" t:max b:max=>castor (timeMesh Λ) s t b

private lemma world_trans {X:Calibration} (j : Axis) (v : Cover) (m n a u w W h Hs : ℤ) {f z: Family X}
    (Yf: TestFamily X true f) (p: TestFamily X true z)
    (hc : Hs=v j+h-m) (hs : Hs=u) (hw : u+w+n=W) (ha : a= -m) :
    SlabMark.relocate X j u (cad X (spare j (look j)) v (f * (SlabMark.relocate X j w (cad X (spare j (look j)) (-v) (SlabMark.relocate X j n z))))) =
       (SlabMark.relocate X j a (Vacancy.chart X v (SlabMark.relocate X j h f)))* SlabMark.relocate X j W z:=by
 let R:= SlabMark.relocate X j
 let J:= spare j (look j)
 have t:cad X J v (SlabMark.relocate X j w (cad X J (-v) (SlabMark.relocate X j n z)))=
     R w (R n z):=by rw [cad_movement X j J (cad_paid X J (move_ok X j n p) (-v)),cad_plus X J (move_ok X j n p),add_neg_cancel,cad_zero X J (move_ok X j n p)]
 rw [cad_prod,t,relocate_mul]; unfold R;
 have hf:TestFamily X true (cad X J v f):= cad_paid X J Yf v
 rw [chart_piece X j v (move_ok X j h Yf),cad_movement X j J Yf, relocate_sums X j _ _ (move_ok X j n p),relocate_sums X j _ _ p,relocate_sums X j _ _ hf,relocate_sums X j _ _ hf,
     hw, show a+(v j+h)=u by omega]

include V Q C in
lemma actor_layout (t : ℕ) (z : Φ t) (u:Cover) :
    (transport Y H t j false (look j) (street u j) z).val=(π u) z.val := by
  rw [transport_c Y H V t Q j false C]; exact (transverse_eq K j (look j) u (street u j) (fun _=>rfl)).symm

variable {f : Marks (tent Y H) false} (g : Gate Y H s j f)
noncomputable def indoorOp (y : seeMesh (timeMesh Λ)) : (indoor Y H V Q Qt j false C c).Op :=
    let v := toR (M:=timeMesh Λ) y
    (Ex).E (g.left v).toNNReal*(U y)*Π (Β g.entry g.pos) *(U (-y))*(Ex).E (g.right v).toNNReal
local notation "O₀" g:max=> indoorOp Y H V Q Qt s j C c g
include V in
lemma lifted (t : ℕ) (e:s≤t) : ((δ f t):Marks K false).val=
    SlabMark.relocate K j (σ t g.base) (furnished Y H s Q j false g.width g.entry t e).val.val:=by
  change stream Y H D _ _ f.val= _
  have he:= test_entry Y H s j false g.entry
  rw [g.price]; unfold relocate gaugeT; rw [show (K).B=Λ.block from rfl,chime_X Y H V s j (2*g.base) Q.circuit he]
  change chime K j (Heat.gaugeShift _ (_*(2*_))) _= chime K j (Heat.gaugeShift _ _) _
  unfold castor; rw [show (timeMesh Λ).L=Λ.R.L.val from rfl,mul_left_comm _ (2:ℤ)]; rfl -- syntax

/-- The window factor on the unprojected Hilbert. Literally on a high level, with full
slab shift, width consumed. This doesn't itself declare an Entry for this output. -/
lemma gate_bud (t : ℕ) (e:s≤t) (v:Cover) (y : Φ t) (h : g.admits (GU t v)) :
    ∃ z : Tower.Field Y H t j 0 false,
      ((O₀ g) (g₀ t v)) ((T t) y) = (T t) z ∧
       z.val=SlabMark.relocate K j (-castor (timeMesh Λ) s t g.start) (relocateWorld Y H false v (upGrade Y H s Q false f t)).val * SlabMark.relocate K j (MeshClock.acts (timeMesh Λ) s t g.full) y.val := by
  obtain ⟨r₁,r₂,A,B,k,p⟩:= Gate.fees g e v h
  unfold indoorOp; simp only [ContinuousLinearMap.mul_apply, A,B,Real.toNNReal_coe,(grid_neg Μ t v), ride_ticks Y H V t Q Qt j false C c]
  let I v x:=transport Y H t j false (look j) (street v j) x
  let Kt(w:ℕ) := tick Y H t j 0 false (2*w)
  let g' := furnished Y H s Q j false g.width g.entry t e
  -- use concise ambient evaluations, align trans shifts
  have t0(v:Cover) (x:Φ t) : (U (g₀ t v)) ((T t) x) = (T t) (I v x):=roving Y H V t Q Qt j false C c (look j) x (street v j)
  rw [t0,slot_high Y H V s Q Qt j false C c g.entry g.pos t e,t0, ride_ticks]
  let z:= Kt r₁ (I v (slabT _ _ _ _ _ (MG t g.width) g' (I (-v) (Kt r₂ y))))
  refine ⟨z,rfl,?_⟩
  unfold z I Kt; rw [timed_apply,actor_layout Y H V Q j C,slab_eq,actor_layout Y H V Q j C,timed_apply,world_val,lifted Y H V Q s j g t e]
  unfold Gate.full; rw [widths_up];
  have T₀: MG t g.width= L₀^(t-s)*g.width:= rfl
  have h0: (r₁:ℤ)+(L₀^(t-s)*g.width:ℕ)+r₂=(MG t g.width+ MG t g.slack:ℕ):=by omega
  exact world_trans j v (σ t g.start) r₂ _ r₁ (MG t g.width:ℕ) _ (σ t g.base) _ (test_entry Y H t j false g') (field_test Y H t j 0 false y) p rfl h0 rfl
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.gate_bud

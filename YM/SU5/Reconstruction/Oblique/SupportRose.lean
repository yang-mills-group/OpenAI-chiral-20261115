import YM.SU5.Reconstruction.Oblique.Rotate
import YM.SU5.Reconstruction.Crease.Regional
/-! # pivot motions, geography needed even on compact apertures. -/
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
open BridgeClub
variable {s:Signed}{j z:Axis}
structure Oriented (s:Signed)(j z:Axis): Prop where
 peer: s.perm j=z
 turns:s.flip j=false
variable (t: Oriented s j z)
lemma Oriented.return_z (t:Oriented s j z): Oriented s⁻¹ z j:= by rw [← t.peer]; exact ⟨s.perm.symm_apply_apply j,by simp [t.turns]⟩
lemma Oriented.relay {s' h}(p:Oriented s' z h)(t:Oriented s j z): Oriented (s'*s) j h:= ⟨by simp [t.peer,p.peer],by simp [t.peer,t.turns,p.turns]⟩
lemma Oriented.height {X:Type*}[AddGroup X](t:Oriented s j z)(x:Four X):s.act x z=x j:=by rw [← t.peer,Signed.act_at,t.turns]; rfl
include t
lemma orientation_Flank(r:ℝ): s.act '' flank j r = flank z r:= by
 ext n; refine ⟨?_, fun h=>⟨s⁻¹.act n, ?_,s.act_inv n⟩⟩ -- wrong image point
 · rintro ⟨y,u,rfl⟩; change r ≤ s.act y z; rw [t.height]; exact u
 · change r ≤ s⁻¹.act n j; rw [t.return_z.height]; exact h
lemma orientation_strip (p r:ℝ) : s.act '' strip j p r=strip z p r:= by
 ext n; constructor
 · rintro ⟨v,w,rfl⟩; change s.act v z∈ Set.Icc p _ ; rw [t.height]; exact w
 intro w; refine ⟨s⁻¹.act n, ?_,s.act_inv n⟩; change s⁻¹.act n j∈ Set.Icc p _ ; rw [t.return_z.height]; exact w
omit t
noncomputable def sailPoint (s:Signed) (x:E4): E4:=WithLp.toLp 2 (s.act x.ofLp)
lemma sails_coord (s:Signed)(x:E4)(j:Axis): sailPoint s x (s.perm j)= hush (s.flip j) (x j):= s.act_at x.ofLp j
lemma Oriented.sees (t:Oriented s j z)(x:E4): sailPoint s x z=x j:= t.height x.ofLp
lemma sail_inverse (s:Signed)(x:E4): sailPoint s⁻¹ (sailPoint s x)=x:= congrArg (WithLp.toLp 2) (s.inv_act _)
lemma sail_right (s:Signed)(x:E4): sailPoint s (sailPoint s⁻¹ x)=x:= congrArg (WithLp.toLp 2) (s.act_inv _)
lemma sail_zero (s:Signed): sailPoint s 0=0:= congrArg _ s.act_zero -- goal tricky
lemma sail_add (s:Signed)(x y:E4): sailPoint s (x+y)=sailPoint s x+sailPoint s y:=by unfold sailPoint; rw [WithLp.ofLp_add,Signed.act_add,WithLp.toLp_add]
lemma sail_neg (s:Signed)(x:E4): sailPoint s (-x)= -sailPoint s x:= by unfold sailPoint; rw [WithLp.ofLp_neg,Signed.act_neg,WithLp.toLp_neg]
lemma sail_axes (s:Signed)(j:Axis)(x:ℝ): sailPoint s (x • basis j)=hush (s.flip j) x • basis (s.perm j):= by
 apply PiLp.ext; intro k; obtain ⟨i,rfl⟩:=s.perm.surjective k; change sailPoint _ _ _ = _; rw [sails_coord]; by_cases p:i=j; · subst i; simp
 unfold hush; split_ifs <;> simp [p]
lemma Oriented.stroll (t:Oriented s j z)(x:ℝ):sailPoint s (x • basis j)=x • basis z:=by rw [sail_axes,t.peer,t.turns]; rfl
lemma tilt_eject {X:Type*}[AddGroup X](x:X)(s:Signed)(j:Axis): s.act (eject j x) = eject (s.perm j) (hush (s.flip j) x):=by
 funext k; obtain ⟨i,rfl⟩:= s.perm.surjective k; rw [Signed.act_at]; by_cases p:i=j; · subst i; simp [hush]
 rw [eject_away j x i p,eject_away _ _ _ (s.perm.injective.ne p)]; simp
lemma Oriented.axis_eject (t:Oriented s j z){X:Type*}[AddGroup X](x:X): s.act (eject j x)=eject z x:= by rw [tilt_eject,t.peer,t.turns]; rfl
lemma Oriented.rotateAB(P:Tilted.Ramp): Oriented (P.s * Signed.mirror P.a) P.a P.b:= ⟨by simp [Signed.mirror],by simp [Signed.mirror]⟩
lemma tilt_quarter(P:Tilted.Ramp)(x:E4): sailPoint (P.s * Signed.mirror P.a) x=Picket.quarter P.a P.b x:=by
 obtain ⟨p,h,X⟩:= Picket.quarter_gear P.cross x; ext1 j; change (P.s * Signed.mirror P.a).act x.ofLp j=Picket.quarter P.a P.b x j; rw [Signed.act_mul,map_returns]
 by_cases u:j=P.a; · subst j; rw [P.move_a,h]; simp [reverseOne,P.cross]
 by_cases v:j=P.b; · subst j; rw [P.move_b,p]; simp [reverseOne]
 rw [P.move_h _ u v,X _ u v]; unfold reverseOne; rw [if_neg u]
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose

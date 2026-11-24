import YM.SU5.Reconstruction.AllGrades.Caption
import YM.SU5.Reconstruction.Seams.Gulf
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.ConePrice.Session
open Function Set Filter MeasureTheory Spectral Analysis InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket Roy
variable {H W:Hilbert} {a: Axis} {Γ: AddSubgroup ℝ} (K: OS.Semigroup H a)(T:Germ.Alliance (CF.Buffered.Afterglow.Tower.Trans a) Γ H)(S:OS.Semigroup W a)
local notation "U" j:max v:max=> (T.crew j).play v
/-! Entire realization from the coast. Compare rays starting from each possible Phase-mark. -/
open Sail
variable {γ : AddSubgroup ℝ}(P:γ →+ Γ)
variable (p:∀ x:γ,(x:ℝ)=(P x:ℝ))(t:Dense (γ:Set ℝ))
local notation "J"=> _root_.YM.CF.Buffered.Afterglow.Tower.Trans a
variable (i:CF.Buffered.Afterglow.Tower.Trans a)
variable (u:∀ z:γ, K.U ((z:ℝ) • cross a i.val i.property)=(T.crew i).play (P z))
variable (e:Forward K)(v:Γ)(x y:H)(t₀:ℝ≥0)(j:0<t₀)
local notation "x₀"=> cross a i.val i.property
local notation "R"=> (T.crew i).play
-- no supposing commutation with *time* to do this. represent at far using other representation already
local notation "tx" w:max=> inner ℂ x (R w (K.E t₀ y))
variable (b: ∃ d:ℝ,∃ f:ℝ→ℂ, Continuous f ∧ ∀ z:Γ,d<(z:ℝ)→ inner ℂ x ((T.crew i).play z (K.E t₀ y))=f (z:ℝ))
include b u e p t j
theorem coast_credit : inner ℂ x (K.U ((v:ℝ) • x₀) (K.E t₀ y)) = tx v:=by
 obtain ⟨d,f,h,g⟩:= b
 let W₀ (r:ℝ):=inner ℂ x (K.U (r • x₀) (K.E t₀ y)); let V(r:ℝ):= inner ℂ x (R v (K.U (r • x₀) (K.E t₀ y))); let UX:= (innerSL ℂ x); let G:ℝ→ℂ:= fun x=> V (x-(v:ℝ))
 have hw:Continuous W₀:= UX.continuous.comp ((K.continuousU (K.E t₀ y)).comp (show Continuous (fun r:ℝ=>r • x₀) by fun_prop))
 have hV:Continuous V:=(UX.comp (R v)).continuous.comp ((K.continuousU (K.E t₀ y)).comp (show Continuous (fun r:ℝ=>r • x₀) by fun_prop))
 have Hx {V f : ℝ→ℂ}(h:Continuous V)(k:Continuous f)(D:ℝ)(p:∀ x:γ, D < (x:ℝ)→ V (x:ℝ)=f (x:ℝ)): EqOn V f (Ioi D):= (Set.EqOn.closure (s:=Ioi D∩ (γ:Set ℝ)) (by rintro i ⟨x,v⟩; exact p ⟨i,v⟩ x) h k).mono (t.open_subset_closure_inter isOpen_Ioi)
 have ht: EqOn W₀ f (Ioi d):= Hx hw h d (fun z q=> by unfold W₀; rw [u]; rw [p] at q ⊢; exact g _ q)
 have he: EqOn G f (Ioi d):=by
    let f':=fun x:ℝ=> f (x+(v:ℝ)); have hz:EqOn V f' (Ioi (d-(v:ℝ))) := Hx hV ((show Continuous f' from h.comp (continuous_id.add continuous_const))) (d-(v:ℝ)) (fun z q=>by unfold V f'; rw [u,(T.crew i).paved]; have h': (z:ℝ)+(v:ℝ)= ((v+ P z : Γ): ℝ):=(by rw [p,AddSubgroup.coe_add,add_comm]); rw [h']; apply g; rw [← h']; linarith)
    intro x h; have hv: d-(v:ℝ)<x-(v:ℝ):=sub_lt_sub_right h _; unfold G; rw [hz (show x-(v:ℝ)∈ Ioi _ from hv)]; unfold f'; rw [sub_add_cancel]
 let a': slit (t₀:ℝ) = slit (t₀:ℝ):=rfl; let n:=show ‖x₀‖ ≤ 1 from le_of_eq (by change ‖basis i.val‖=1; simp); let Z:= transverse K e x₀ n t₀ j
 let f₁:= fun z:ℂ=> UX (Z z y)
 let f₂:= fun z:ℂ=> UX (R v (Z (z-((v:ℝ):ℂ)) y))
 have h₁(r:ℝ): f₁ r =W₀ r:=by unfold f₁ W₀ Z Sail.transverse; rw [on_strip K e x₀ n t₀ j]; rfl
 have h₂(r:ℝ): f₂ r=G r:=by unfold f₂ G V Z Sail.transverse; rw [← Complex.ofReal_sub,on_strip K e x₀ n t₀ j]; rfl
 have op:EqOn f₁ f₂ (slit (t₀:ℝ)) :=by
    apply pioneer (M₁:=f₁) (slit_connected _) (slit_ground _ j (d+1)) d (d+2) (by constructor<;> linarith) (fun z h=> (UX.comp (ContinuousLinearMap.apply ℂ H.space y)).analyticAt _|>.comp (transverse_anal K e x₀ n t₀ j z h)) ?_ (fun z h=> by rw [h₁,h₂,ht h.1,he h.1])
    intro z h; have hz:z-((v:ℝ):ℂ)∈slit (t₀:ℝ):= by change |(z-((v:ℝ):ℂ)).im|<(t₀:ℝ); simpa using (show |z.im|<_ from h)
    exact ((UX.comp ((R v).comp (ContinuousLinearMap.apply ℂ H.space y))).analyticAt _|>.comp (transverse_anal K e x₀ n t₀ j _ hz))|>.comp (f:=fun z:ℂ=>z-((v:ℝ):ℂ)) (analyticAt_id.sub analyticAt_const)
 have hb:= op (slit_ground (t₀:ℝ) j (v:ℝ)); rw [h₁ (v:ℝ),h₂] at hb; unfold G V at hb; rw [sub_self,zero_smul,K.uZero] at hb; exact hb
end YM.ConePrice.Session
#print axioms YM.ConePrice.Session.coast_credit


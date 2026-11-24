import YM.SU5.May.TorqueRent
import YM.SU5.May.TorqueTreat
import YM.SU5.May.FloeMix
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.Torque
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted WindRose
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open PolarArchives Brazier
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable {i k : ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} (V:Universal Y H i k I E)
  (G : GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "v₁" n:max => i (G.rows n)
local notation "v₂" n:max => k (G.columns n)
open LocalLimit.Intermediate Harbour
open Hygrometry Hygrometry.MeterFunding
open May.Floe
open Push.SectorMeasure
open Advance.Depths
variable (κ:ℕ){U : Finset Cover}
local notation "𝗠" i:max j:max=> Journey.side Y i j
variable (m t s R:ℕ) (P:Ramp)
open Therapies May.Floe May.TorqueBeam Advance.Whorl FloeRoom
variable (r:ℝ≥0) (f:Dome (tent Y H))(p:f∈insideAt Λ l (tent Y H) true (Acres P r) s)(ε:ℝ)(hc:0<ε)
local notation "Θ" n:max t:max a:max z:max=> tractor Y H G s t n a z f
local notation "♣" n:max t:max a:max z:max => temper (projectA Y (v₁ n) t) (s+a) Λ.δ (s+a) z
noncomputable abbrev Paid (n t a:ℕ)(z:Intermediate.Room (s+a))(ε:ℝ)(U:Set (Pane (Journey.side Y (i (G.rows n)) (s+a)))):= shelter Y (v₁ n) t (s+a) (♣ n t a z) (poseField P false (Θ n t a z)) U ε
noncomputable def overcast (n t a:ℕ)(z:Intermediate.Room (s+a))(U:Set (Pane (Journey.side Y (i (G.rows n)) (s+a)))):= share Y (v₁ n) t (s+a) (poseField P false (Θ n t a z)) (♣ n t a z) Uᶜ
local notation "Γ" n:max t:max a:max z:max=> next_price Y H G P s n t a z f -- parameter order?
-- (1): order label.Beware
local notation "M" n:max t:max a:max z:max=> markedRead (poseField P false (Θ n t a z)) ((Y.voyage (v₁ n)).CapeT (s+a)) (tap Y (v₁ n) t (s+a) (♣ n t a z))/phaseInspector Y (v₁ n) t (s+a) 0 (♣ n t a z)
structure Regalia(n t a:ℕ) (z:Intermediate.Room (s+a)):Prop where
 owes : Cred Y (v₁ n) t (s+a) z
 env : Envelope (poseField P false (Θ n t a z))
 available(δ:ℝ)(p:0<δ) : ∃ S:Set (Pane (Journey.side Y (i (G.rows n)) (s+a))), Paid Y H G s P f n t a z δ S
 returns(δ:ℝ)(S:Set (Pane (𝗠 (v₁ n) (s+a)))) (p:Paid Y H G s P f n t a z δ S) : 0<∫ i in Prod.fst ⁻¹' S, ‖beamZ _ (tap Y (v₁ n) t (s+a) (♣ n t a z) i)‖ ∂city _
 spent(δ:ℝ)(S:Set (Pane (𝗠 (v₁ n) (s+a)))) (p:Paid Y H G s P f n t a z δ S): ‖ (M n t a z) - ((next_price Y H G P s n t a z f)+overcast Y H G s P f n t a z S)‖ ≤ δ
-- next_price likely arguments Y H G P .... #verify.
include V p
lemma horizon_grant : ∀ᶠ n in atTop,∀ᶠ t in atTop, (∃ (a:ℕ)(z:Intermediate.Room (s+a)),Cred Y (v₁ n) t (s+a) z)∧∀ (a:ℕ)(z:Intermediate.Room (s+a)),Cred Y (v₁ n) t (s+a) z→Regalia Y H G s P f n t a z := by
 obtain ⟨U,T,f'⟩:= formed Y H V G s P r f p; have hv:= (V.pick.grow_i.comp G.history.growsA).tendsto_atTop
 filter_upwards [roll_easy Y H V G s P r f p (show (0:ℝ)<1 from one_pos),hv.eventually (wave_guarantee Y),f'] with n h g q; filter_upwards [h] with t hh; obtain ⟨b,z,e,y⟩:= hh.1; refine ⟨⟨b,z,y⟩,fun a z' hx=>?_⟩; have ha : b=a:= Nat.add_left_cancel (y.high.symm.trans hx.high)
 let X:= Θ n t a z'; let Y':= poseField P false X; let m':=v₁ n; let D:= s+a; let z:=z'; let v:=♣ n t a z'
 obtain ⟨K₁,K₂,K₃⟩:= audit_spend Y H m' t s D (blankMenu Y m' D) z P r f q hx.menu (sprung Y m' t D) hx.carrier a le_rfl
 have hF: AtSupport false Finset.univ X:= K₁.siteF.mono (Finset.subset_univ _); have hg: AtSupport false Finset.univ Y':= (((P.term_marked hF).mono (Finset.subset_univ _)).mulM hF).smulM _
 have hy:=drawStill Y m' t s D P (blankMenu Y m' D) z (a:=a) (by omega) le_rfl hx.menu (sprung Y m' t D) hx.carrier _ q.Stamp q.reflection
 let hd:= blanked Y m' t D z (by unfold D; omega) hx.menu hx.carrier
 refine ⟨hx,hg.env,fun δ p=> locateCost Y m' t D Y' v hd hg.env hx.real (dotSufficient Y m' t D Y' (formCovar P hF K₂ _) (formSteady P hy _) (g D).2) δ p,fun δ S H₀=>?_,fun δ S H₀=>?_⟩
 · obtain ⟨ξ,u,a,h'⟩:=H₀; exact hearts Y m' t D Y' v S ξ hd a
 have Z:= H₀; obtain ⟨ξ,u,g₁,g'⟩:= Z; let KX(W: Set (Pane (𝗠 m' D))):= share Y m' t D Y' v W
 rw [show next_price Y H G P s n t a z' f=dotCurrency Y m' t D Y' from rfl]; rw [show markedRead _ _ _ / _= dotCurrency Y m' t D Y' + KX S + KX Sᶜ from arrangedCash Y m' t D Y' v S hd hg.env hx.real g₁.1.2.1.measurableSet]; change ‖dotCurrency Y m' t D Y'+ KX S+ KX Sᶜ-(dotCurrency _ _ _ _ _+ KX Sᶜ)‖≤ δ; rw [show dotCurrency Y m' t D Y'+ KX S+ KX Sᶜ-(dotCurrency _ _ _ _ _+ KX Sᶜ) = KX S from (by abel)]; exact share_paid Y m' t D Y' v S hd hg.env hx.real δ H₀
omit V p
/-- require frequently t at fixed n (admissible shelf), actually k(s) explicit. -/
noncomputable def Sail : Prop:= ∀ (s:ℕ)(f:Dome (tent Y H)), f∈ insideAt Λ l (tent Y H) true (Acres P r) s→∀ (ε:ℝ),0<ε→ ∃ᶠ n in atTop, ∃ᶠ d in atTop,∃ (a:ℕ)(z:Intermediate.Room (s+a))(U:Set (Pane (Journey.side Y (i (G.rows n)) (s+a)))), Cred Y (i (G.rows n)) (k d) (s+a) z ∧ Paid Y H G s P f n (k d) a z ε U ∧ -ε≤ (overcast Y H G s P f n (k d) a z U).re
include V
lemma turning (t:YieldPlate Y P r) (g:Sail Y H G P r): Rectitude Y H V G P r:= by
 apply solar Y H V G P r; intro s f p ε pe
 let C:= ε/3; have pC:0<C:=by unfold C; positivity
 obtain ⟨y,z,h⟩:=anchored Y H V G s P r t f p C pC; refine ((g s f p C pC).and_eventually (h.and (horizon_grant Y H V G s P r f p))).mono ?_; rintro n ⟨p,h,t⟩
 refine (p.and_eventually (V.pick.grow_k.tendsto_atTop.eventually (h.and t))).mono ?_; rintro d ⟨⟨a,z,v,h₀,g,H'⟩,h,t⟩
 let A:= overcast Y H G s P f n (k d) a z v; let F':= next_price Y H G P s n (k d) a z f; let Q:=upperSession Y (v₁ n) (k d) (s+a) (blankMenu Y (v₁ n) (s+a)) z P (tractor Y H G s (k d) n a z f)
 have hw:‖Q-(F'+A)‖≤C:=by unfold Q; rw [memory_est]; exact (t.2 a z h₀).spent C _ g
 have hm : -C≤ F'.re:= (neg_le_neg (mul_le_of_le_one_right pC.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Nat.cast_nonneg ((Y.ir (v₁ n)).val)) y))))).trans (h.2 a z h₀)
 refine ⟨a,z,h₀,?_⟩; have hp: -(Q-(F'+A)).re ≤ C:= (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hw); rw [Complex.sub_re,Complex.add_re] at hp; change -ε ≤ Q.re; linarith [show -C ≤ A.re from H', show C=ε/3 from rfl]
#print axioms horizon_grant
#print axioms turning
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.Torque

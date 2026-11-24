import YM.SU5.Reconstruction.LinkMeasures.AxisSense
import YM.SU5.Reconstruction.PolarArchives.Console
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satori
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Tapestry
open Tower Tower.SatinVerification PaymentCamera
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    (V:Universal Y H i k I E)(G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (S:Finset Cover)(s:ℕ)(w:Evens S)
local notation "μS" => actual S Λ l
local notation "W" => wingspan Λ l S
local notation "Bx" => PhaseChoice.transfer Y H G S s
local notation "Tx" => singer S w
local notation "rᵢ" i1:max => i (G.rows i1)
local notation "rₖ" i1:max => k (G.columns i1)

open Tower.Vacancy Tower.Selected Tower.FirstWindows PaymentCamera
local notation "q★" => Satori.qty S Λ l
open Tower.FirstWindows.PolarArchives Tower.Tilted Tower.Tilted.Ramp Tower.FirstWindows.WindRose Tower.PhaseChoice
variable (P:Tower.Tilted.Ramp)(gap:ℝ≥0)
open CF.Pannier.Chancel Tower.FirstWindows.Stormwatch
/-! upgrade beyond_χ far root-consumption to all colors, without adding a criterion on χ -/
variable (j:Axis)(C: ∀ i:Axis, Tower.Arena Y H G.history.circuit i 0 false)
variable (χ: displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ]ℂ)
variable (p:PhaseChoice.SupportedPhysically Λ l s S (Acres P gap))(m:Side)
variable (u:Hosp S ((tent Y H).c m))
variable (e:Rectitude Y H V G P gap)
local notation "Ω" => oneAt Y H V G j (C j) χ
local notation "ψ" => whiff Y H V G C j χ
local notation "θF" => windTilt P (tent Y H)
local notation "θ" => gust P (tent Y H)
local notation "ρ" => Domain Y H G false Set.univ
local notation "U₁" => (S ∪ P.survey S)
lemma pulse_material (x y:Swatch S): Ω s (θF (badge K S x)*badge K S y)= (Ω s) (badge K (U₁) (aptR Y H S P (x,y))):= by rw [badge_apt]
noncomputable def fX (x y: Swatch S) : ℂ := (oneAt Y H V G j (C j) χ s) (θF (badge K S x)*badge K S y)
local notation "V₁"=>fX Y H V G S s P j C χ
lemma fX_sched : Continuous (Function.uncurry (fX Y H V G S s P j C χ)):=by
 rw [show Function.uncurry V₁ = (fun x:Swatch (U₁)=> (Ω s) (badge K (U₁) x)) ∘ aptR Y H S P from funext fun ⟨i,j'⟩=> pulse_material Y H V G S s P j C χ _ _]; exact (X_lookup Y H V G _ _ _ _ _).comp (apt_c ..)
include e
lemma tilt_WK(x:Dome (tent Y H)): Ω s (θF x)=star (Ω s x):=by
 let f:=ticket Y H G s x
 have h:= character_rotation Y H V G C j χ P (⟨f,ticket_loose ..⟩: Domain Y H G false Set.univ); rw [restored_rotation _ _ _ _ _ _ _ _ _ e] at h
 change ψ (θ (ticket Y H G s x)) = star (ψ (ticket Y H G s x)) at h
 rw [gust_ticket Y H V,funds_stamp Y H V G C j χ (ticket_loose ..),funds_stamp Y H V G C j χ (ticket_loose ..),os_ticket,os_ticket] at h; exact h
lemma fX_mirror(x y: Swatch S): V₁ x y= star (V₁ y x):= by
 let f:= θF (badge K S y)*badge K S x
 have ht: (θF f)= θF (badge K S x)*badge K S y:=by unfold f; rw [show ∀ u v:Dome K, θF (u*v)=θF u*θF v from fun _ _=>Subtype.ext (P.over_times (tent Y H)), twice_dome, mul_comm]
 unfold fX; rw [←ht]; exact tilt_WK Y H V G s P gap j C χ e f
omit e
noncomputable def lX (x:Swatch S):Swatch S→ₗ[ℂ]ℂ where
 toFun y:= fX Y H V G S s P j C χ x y
 map_add' h y:=by unfold fX; rw [map_add,mul_add,map_add]
 map_smul' z h:=by unfold fX; rw [map_smul,Algebra.mul_smul_comm,map_smul]; rfl
private lemma onPort {X:Type*}[TopologicalSpace X](f:X→X→ℂ)(h:Continuous (Function.uncurry f))(x:X):Continuous (fun y=>f x y):= h.comp (continuous_const.prodMk continuous_id)
lemma lX_here (x:Swatch S) : Continuous (lX Y H V G S s P j C χ x):=onPort _ (fX_sched Y H V G S s P j C χ) _
include p
lemma railX(x y:Swatch S)(g:Zodiac ((tent Y H).c m)): V₁ x y=V₁ x (orbitC S (tent Y H) m y g):=by
 let a:= orbitC S K m y g
 have ht:Tapestry.Circular S (g∘wrap _) (render S K y) (render S K a):= decorates K S _ y; have hv:=P.faces K (texture S K x)
 obtain ⟨z,h⟩:= both_colors ht hv (holy_grid S s P gap p)
 let f(x'):=(θF (badge K S x)*badge K S x'); change (Ω s) (f y) = (Ω s) (f a);
 have hh:pennant K z (f y)=f a:=by exact Tapestry.appointed K U₁ z (f y) (f a) h ((hv.mono Finset.subset_union_right).mul ((texture S K a).mono Finset.subset_union_left))
 rw [←hh]; exact (gauge_one Y H V G j C χ s (f y) z).symm
include u
lemma panoramicX (x y:Swatch S)(h: Continuous (appear S (tent Y H) m y)): V₁ x (reynoldsC S K m y)=V₁ x y := by
 let Q: Swatch S →L[ℂ] ℂ:=⟨lX Y H V G S s P j C χ x,lX_here Y H V G S s P j C χ x⟩; change Q (∫ g,orbitC S (tent Y H) m y g∂domeLaw ((tent Y H).c m))=_
 have he(g):Q (orbitC S K m y g)=V₁ x y:=(railX Y H V G S s P gap j C χ p m x y g).symm
 rw [←(ContinuousLinearMap.integral_comp_comm (E:=Swatch S) (Fₗ:=ℂ) (𝕜:=ℂ) Q ((orbitC_cont S K m y u h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)))]; simp_rw [he]; simp
omit u
lemma amountX (x:Swatch S): V₁ x x=ψ (θ (ticket Y H G s (badge K S x))*ticket Y H G s (badge K S x)):=by
 let z:=θF (badge K S x)*badge K S x
 have t:= custodies Y H S s P gap p (badge K S x) (texture S K x); rw [gust_ticket Y H V, ←ticket_separated Y H G (protects P s _ _ _ t) t (unpaired P gap),funds_stamp Y H V G C j χ (ticket_loose ..),os_ticket]; rfl
lemma nextX(x:Swatch S): V₁ x x=fX Y H V G (W) (s+1) P j C χ ((Bx) x) ((Bx) x):= by
 rw [amountX Y H V G S s P gap j C χ p,amountX Y H V G W (s+1) P gap j C χ (show PhaseChoice.SupportedPhysically Λ l (s+1) (wingspan Λ l S) (Acres P gap) from p.persists 1), ←step_badge, ticket_spread Y H G (Nat.le_succ s)]
include e
lemma voluntary (x:Swatch S)(h:x∈ literal S): 0≤ V₁ x x:=by
 obtain ⟨m,h'⟩:= (Buffered.separates K S).exists; have u:Hosp S ((tent Y H).c m):=⟨h'⟩
 have z:= literal_measured S K m _ h; let A:=reynoldsC S K m x; have hx:V₁ A A= V₁ x x:=by unfold A; rw [panoramicX Y H V G S s P gap j C χ p m u (reynoldsC S K m x) x z,fX_mirror Y H V G S s P gap j C χ e,panoramicX Y H V G S s P gap j C χ p m u _ _ z]; exact (fX_mirror Y H V G S s P gap j C χ e x x).symm
 rw [←hx,amountX Y H V G S s P gap j C χ p]; let a:=badge K S A
 have he:a∈ insideAt Λ l K true (Acres P gap) s := by refine (mem_insideAt ..).2 ⟨⟨S,texture ..,p⟩,fun _=> ?_⟩; exact neutralC S K m x u z
 exact beyond_χ Y H V G C j χ P gap e (ticket Y H G s a) (ticket_mem Y H G he)
omit p e in
private lemma c_limitX {X:Type*}[TopologicalSpace X]{f:X→X→ℂ}(h:Continuous (Function.uncurry f)){x:ℕ→X}{y:X}(u:Tendsto x atTop (𝓝 y))(t:∀ i,0≤f (x i) (x i)): 0≤ f y y:= ge_of_tendsto (f:=fun i=>f (x i) (x i)) (h.continuousAt.tendsto.comp (u.prodMk_nhds u)) (Eventually.of_forall t)
lemma aboard (x:Swatch S):0≤ V₁ x x:= by obtain ⟨f,h,t,-⟩:= suggestions Y H V G S s x false nofun; rw [nextX Y H V G S s P gap j C χ p]; exact c_limitX (X:=Swatch (wingspan Λ l S)) (fX_sched Y H V G (W) (s+1) P j C χ) t fun i=> (nextX Y H V G S s P gap j C χ p (f i)) ▸ voluntary Y H V G S s P gap j C χ p e _ (h i).1
omit p
lemma throughout (x:Sky (tent Y H))(v:x∈ Domain Y H G false (Acres P gap)): 0≤ ψ (gust P K x*x):=by
 obtain ⟨s,F,h,rfl⟩:= v; obtain ⟨⟨S,t,p⟩,_⟩:= (mem_insideAt F s).mp h; obtain ⟨g,u⟩:= accolade K S F t; subst F; rw [←amountX Y H V G S s P gap j C χ p]; exact aboard Y H V G S s P gap j C χ p e g
omit e
lemma helm_true (e: Rectitude Y H V G P 0):RPos Y H V G P C j χ := fun x u=> throughout Y H V G P 0 j C χ e x u
end YM.CF.Buffered.Afterglow.Satori
#print axioms YM.CF.Buffered.Afterglow.Satori.helm_true

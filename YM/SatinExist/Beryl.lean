import YM.SatinExist.TitleE
import YM.SatinExist.Taint
import YM.SatinExist.Road
import YM.SatinExist.Lunary
import YM.SatinExist.Bond
import YM.SatinExist.Turret
import YM.SatinExist.Lede
import YM.SatinExist.Teres
import YM.SatinExist.ShiftE
import YM.SatinExist.Policed
import YM.SatinExist.Shield
import YM.SatinExist.Cameo
import YM.SatinExist.Hall
import YM.SatinExist.Fence
import SatinThinRampart
import SatinThinAngle
import YM.SatinExist.Glacis
import SatinThinSegno

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
open Aria Casting MacroGrid
variable (N₁:P.NightCop) (x:P.Spectrum0 3)(A0:ℝ) (B0:ℝ)(b':ℝ)
local notation "T"=> ℕ × ℕ
variable (v:ℕ→ℕ)(a:ℕ→ (ℕ×ℕ)→ℝ)
local notation "Z"=> P.advocate 3 x j
variable (B:ScoutAnthem P x A0 B0 f r b' v a)
local notation "a₁" i:max=> a i (f,r)
variable (p:f<r)(J:List Axis)
local notation "w" s:max=> P.columnW j s f J
local notation "X'" s:max=> P.rootSpace f s J
local notation "Q'" s:max=> P.column_bill j s f J
local notation "Tk" s:max t:max=> P.spotDuty j (X' s) (w s) (Q' s) x t
variable (hO:Odd P.par.R.L.val)(τ:Aglomerate f r a)(s:ℕ)
local notation "κ"=> P.advocate 3 x j
local notation "λ'"=> P.ManyF j (P.advocate 3 x j)
local notation "ψ"=> P.ColorHil j (P.advocate 3 x j)
local notation "η₀" s:max=> P.fixedStar j f s J
local notation "M₁" i:max=> (P.basePlay x f (v i)).pivot P J
local notation "b₁" i:max=> ((a i (f,r):ℝ):ℂ)
local notation "Z₁" t:max i:max=> b₁ i • P.pillar j κ (M₁ i) (-t) t 0
local notation "Δ" s:max=> P.turtle j s f J
local notation "Ω"=> P.seasons j κ
open SatinTails
lemma kiosk_pinch (v:ℕ)(z:Cover)(t:P.Apron)
 (e₁:t.s≤v) (e₂:s≤v)(d:P.chartAll z (t.full P v)=P.centeredQ x v (P.clockPlate s v (P.rootSpace f s J)))
 (u:0 < Apron.time_panel P j (P.laysM (P.vtile v z)) t)(c:Apron.time_edge P j (P.laysM (P.vtile v z)) t < (Δ s:ℝ)) (b:ℂ):
 P.kiosk j κ (b • P.spotDuty j (P.rootSpace f s J) (P.columnW j s f J) (P.column_bill j s f J) x v)= b • P.pillar j κ t 0 (Δ s:ℝ) (P.laysM (P.vtile v z)):= by
 have ht := P.centPin j (P.rootSpace f s J) (w s) (P.column_bill j s f J) x e₂ t z e₁ d u c
 let V:= P.kiosk j κ
 let p':=(Δ s:ℝ); let y:=P.raze j κ t 0 p' (P.vtile v z)
 have hv:V y = _:= P.kiosk_pillar j κ t _ _ (P.vtile v z)
 exact (P.kiosk_scale j κ _ b).trans (congrArg (b • ·) ((congrArg V ht.symm).trans hv))
include hO
lemma prey {M:(ψ).Op}(d:Tendsto (fun i=> (b₁ i) • (Tk s (v i))) atTop (𝓝 M))(he:Tendsto v atTop atTop)(m:f ≤ s):∃ y:ℕ→ Vantage, Tendsto y atTop (𝓝 (η₀ s)) ∧ (∀ᶠ n:ℕ in atTop, 0 ≤ Apron.time_panel P j (y n) (M₁ n) ∧ Apron.time_edge P j (y n) (M₁ n) ≤ (Δ s:ℝ)) ∧
 Tendsto (fun i=> b₁ i • P.pillar j κ (M₁ i) 0 (Δ s:ℝ) (y i)) atTop (𝓝 ((P.kiosk j κ) M)):=by
 obtain ⟨z,tz,qX⟩:= safeRad P j x s J m hO
 refine ⟨fun i=> P.laysM (P.vtile (v i) (z (v i))),tz.comp he,(he.eventually qX).mono fun i x=>⟨x.2.2.2.1.le,x.2.2.2.2.le⟩,((P.kiosk_s j κ d)).congr' ?_⟩
 filter_upwards [he.eventually qX] with i ⟨tF,q,t,h,uF⟩
 exact P.kiosk_pinch j x J s (v i) (z (v i)) _ t q tF h uF (b₁ i)
omit hO in
lemma norm_open (x:P.Spectrum0 j) (p:ℕ→P.Apron) (q:ℕ→ℂ)(d t:ℝ) (v:Vantage)(G:(P.ManyF j x).Op) (m:d < t)(h:0<v j)(b:v j<d) (P': ∃ y:ℕ→Vantage, Tendsto y atTop (𝓝 v) ∧ (∀ᶠ n:ℕ in atTop,0 ≤ Apron.time_panel P j (y n) (p n)∧ Apron.time_edge P j (y n) (p n) ≤ d) ∧ Tendsto (fun i=> q i • P.pillar j x (p i) 0 d (y i)) atTop (𝓝 G)):
   Brakes (fun n=> q n • P.pillar j x (p n) (-t) t 0) ((P.seasons j x).E (t-v j).toNNReal * (P.cartage j x (-v) * G * P.cartage j x v) * (P.seasons j x).E (v j+t-d).toNNReal) := by
 obtain ⟨x',q',e,h'⟩:= P'; exact P.nearer j x p q q' h b e ((Brakes.by_budget («H»:=P.ManyF j x) h')) m
lemma lower_open {V:(P.ColorHil j (P.advocate 3 x j)).Op}(d:Tendsto (fun i=> (b₁ i) • (Tk s (v i))) atTop (𝓝 V))(he:Tendsto v atTop atTop)(m:f ≤ s) (t:ℝ)(c: (Δ s:ℝ)<t):
    Brakes (fun i=> (Z₁ t i)) ((Ω).E (t-(η₀ s) j).toNNReal * ((P.cartage j κ (-η₀ s))*(P.kiosk j κ V)*P.cartage j κ (η₀ s)) *(Ω).E (((η₀ s) j)+t-(Δ s:ℝ)).toNNReal):=by
 let R':=P.prey j x v a J hO s d he m
 -- name η j explicitly
 have u₀ : 0< (η₀ s) j:= P.pin_p ..
 have h₀: (η₀ s) j < (Δ s:ℝ):= (P.prime_fit j s f J).2
 let M:=(P.kiosk j κ V)
 exact P.norm_open j κ (fun i=> M₁ i) (fun i=> b₁ i) (Δ s) t (η₀ s) M c u₀ h₀ R'
include B p N₁ τ
lemma mast_opens (t:ℝ)(c: (Δ s:ℝ)<t)(m:f ≤ s):∃ A:(ψ).Op, Tendsto (fun i=> (b₁ i) • (Tk s (v i))) atTop (𝓝 A) ∧ Brakes (fun i=> (Z₁ t i)) ((Ω).E (t-(η₀ s) j).toNNReal * ((P.cartage j κ (-η₀ s))*(P.kiosk j κ A)*P.cartage j κ (η₀ s)) *(Ω).E (((η₀ s) j)+t-(Δ s:ℝ)).toNNReal):=by
 obtain ⟨V,d⟩:= P.wear_winner j (P.rootSpace f s J) N₁ x A0 B0 b' v a B m (w s) (P.column_bill j s f J) p τ
 exact ⟨V,d,lower_open P j x v a J hO s d (P.ant_climbs x A0 B0 b' v a B) m t c⟩
lemma oozing : Tendsto (fun i:ℕ=> (M₁ i).realWidth P j) atTop (𝓝 0):=by simp_rw [Apron.pivot_w,P.play_width]; simpa only [mul_zero,Function.comp_apply] using (P.macroStep_zero.comp (P.ant_climbs x A0 B0 b' v a B)).const_mul (P.roomy:ℝ) -- pass
lemma sails_tall : ∃ U:ℝ→(λ').Op, Mosaic P j κ (fun i=> M₁ i) (fun i=> b₁ i) U := by
 choose! U e using fun t:ℝ => fun h:0<t=> (show ∃ A:(λ').Op, Brakes (fun i=> Z₁ t i) A from by
    obtain ⟨s,p',q⟩:= (((P.turtle_down j f J).eventually (gt_mem_nhds h)).and (eventually_ge_atTop f)).exists
    obtain ⟨y,w0,u⟩:=P.mast_opens j N₁ x A0 B0 b' v a B p J hO τ s t p' q; exact ⟨_,u⟩)
 exact ⟨U,⟨P.oozing j N₁ x A0 B0 b' v a B p J hO τ,e⟩⟩
omit B p N₁ hO τ in
private lemma size_anchor (y:(ψ).Op) (p:Vantage)(t v:ℝ):‖(Ω).E (t.toNNReal) * ((P.cartage j κ (-p))*(P.kiosk j κ y)*P.cartage j κ p) * (Ω).E (v.toNNReal)‖≤ ‖y‖:=by
 let p':=P.tableau j κ (0:Vantage) y;
 have ht : P.kiosk j κ y=p':= by unfold p' kiosk tableau; rw [neg_zero,P.cart_zero]; rfl
 rw [ht]; apply (norm_mul_le ..).trans; refine (mul_le_of_le_one_right (norm_nonneg _) ((Ω).shrinks _)).trans ((norm_mul_le ..).trans ?_); refine (mul_le_of_le_one_left (norm_nonneg _) ((Ω).shrinks _)).trans ((norm_mul_le ..).trans ?_)
 exact ((mul_le_of_le_one_right (norm_nonneg _) (P.cart_pay ..)).trans (norm_mul_le ..)).trans ((mul_le_of_le_one_left (norm_nonneg _) (P.cart_pay ..)).trans (P.tableau_pay ..))
lemma altitude (U:ℝ→(λ').Op)(g: Mosaic P j κ (fun i=> M₁ i) (fun i=> b₁ i) U): ∃ K>(0:ℝ),∃ z:ℕ,∀ᶠ t in 𝓝[>] 0,‖U t‖≤ K/t^z:=by
 obtain ⟨W',i,z,k,q⟩:= P.gym_train j N₁ x A0 B0 b' v a B p J
 let R':= (2:ℝ)* (P.sidesPerTick:ℝ); have hr:0<R':=mul_pos (by norm_num) (Nat.cast_pos.mpr P.sides_pos)
 apply Mosaic.driverM P j κ _ _ g hr (C':=W') i.le (z:=z^2) (one_le_pow₀ k)
 have Zp:= StrictMono.tendsto_atTop (show StrictMono (fun i:ℕ=> 2*i) from fun _ _ h=> by simp [h]); filter_upwards [Zp.eventually q,Zp.eventually (eventually_ge_atTop f), P.pin_budget j] with i p' hu w'
 let m:=2*i; let r':=R'*P.macroStep i; have ht:r'>0:=mul_pos hr (P.macroStep_pos _);
 have hv: (Δ m:ℝ)< r':=by rw [P.prime_length]; exact mul_lt_mul_of_pos_left (w' f J) hr
 obtain ⟨A',t,h⟩:=P.mast_opens j N₁ x A0 B0 b' v a B p J hO τ m r' hv hu
 have hk:‖A'‖ ≤ W'*z^m:= le_of_tendsto t.norm p'
 change ‖U r'‖≤ _; rw [(g.paid r' ht).uniqueR h]; exact ((P.size_anchor ..).trans hk).trans_eq (congrArg (W'*·) (pow_mul z 2 i)) -- size
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

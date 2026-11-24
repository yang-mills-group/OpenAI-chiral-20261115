import SatinPP.Footman
import SatinPP.Cornice
import SatinThinJetsPurchase
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six MacroGrid

open TopologicalSpace SatinJets
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "G"=> P.ManyF 3 ξ
local notation "Γ"=> P.cartage 3 ξ
local notation "Θ"=> P.seasons 3 ξ
local notation "E"=> (Θ).E
local notation "κ"=> P.wealth 3 ξ
local notation "D" s:max=>P.lengthP s
local notation "F%" s:max=> P.pointEra s
variable (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))

local notation "ℒ"=>Lead.Clan

open OS ConePrice

lemma lines_equ (t:ℝ)(j:Axis)(p:j≠3) : walk (Θ) j p t=Γ (t • footfall j) :=by
 let y:Cross 3:=t • Picket.cross 3 j p
 rw [show (t • footfall j)=(fun k=> y.val k) from ?_]
 rfl
 ext k
 change t * aglow j 1 k = t* (YM.basis j k)
 simp [aglow,YM.basis,Function.update_apply]
 
variable (w:ℒ→Prism)(b:Bool)(q:ℝ)(F:SampleDose)
variable {Y:ℕ→ P.Apron}{f n:ℕ}(R: GalaxyShow P x f n Y V)
include R

variable (m:ℒ→ℂ)
local notation "φ" b:max q:max F:max=>P.wave x V w b q F
local notation "v"=> ounce m (φ b q F)
local notation "gate" => guards (Θ)

lemma entrance {d h z:ℝ}(q₀:0<q)(p:0<d)(g:0<h)(hz:0<z)
 (e:P.Flare x V w b q F d h z)(hm:fanSet m): h < ‖gate v‖:= by
 let C:= (77/10)/d
 have a: ∀ᶠ t:ℝ in 𝓝[>] 0, dist v (walk (Θ) 0 (by decide) t v)^2 + dist v (walk (Θ) 1 (by decide) t v)^2 + dist v (walk (Θ) 2 (by decide) t v)^2 ≤ (t*C)^2:=by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (mul_pos p hz))] with t u t'
    have u : 0<t:=u
    have b' (j:Axis)(r:j≠3): dist v (walk (Θ) j r t v)≤(slack j+1/4)*(d⁻¹*t) :=by
        rw [P.lines_equ x]
        have a:= e.tranche j r t u t' _ hm
        rw [P.wave_bike x V w b q R m q₀ _ _ r t, norm_smul,norm_inv,Real.norm_of_nonneg u.le,
          ←dist_eq_norm, ←div_eq_inv_mul,div_le_iff₀ u] at a 
        rw [div_eq_mul_inv,mul_assoc] at a 
        exact a

    have b₀:=pow_le_pow_left₀ dist_nonneg (b' 0 (by decide)) 2
    have b₁:=pow_le_pow_left₀ dist_nonneg (b' 1 (by decide)) 2
    have b₂:=pow_le_pow_left₀ dist_nonneg (b' 2 (by decide)) 2
    unfold slack at b₀ b₁ b₂
    rw [if_neg (by decide:(0:Axis)≠2)] at b₀
    rw [if_neg (by decide:(1:Axis)≠2)] at b₁
    rw [if_pos rfl] at b₂
    rw [show t*C=(77/10)*(d⁻¹*t) from by unfold C;ring]
    nlinarith only [b₀,b₁,b₂,sq_nonneg (d⁻¹*t)]
 have s:ℝ≥0:=⟨d*h,(mul_pos p g).le⟩
 have dd:0<d*h:=mul_pos p g
 have e':=few_accounts (Θ) (v) (d*h).toNNReal C a
 rw [Real.coe_toNNReal _ dd.le,show d*h*C=h*(77/10) from by unfold C;field_simp] at e'
 have r := pow_le_pow_left₀ (by linarith only [g]) (e.arch m hm) 2
 change _≤ dist v (E (d*h).toNNReal v)^2 at r
 nlinarith only [g,r,e',norm_nonneg (gate v)]

omit R in
lemma goesSide(y:Vantage):∃s:Cross 3,(Θ).U s=Γ y:=by
 let q':= (WithLp.toLp 2 y)
 let s:=OS.Semigroup.SEP 3 q'
 have k: (fun a:{i:Axis//i≠(3:Axis)}=>s.val a.val)= y ∘ Subtype.val:=by
   funext a
   change q' a.1 - q' 3 * YM.basis 3 a.1=_ 
   simp [YM.basis,a.2, Function.comp,q']
 rw [show Γ y=(Θ).U s from by 
   change (P.voyageF _ _).aviation _ (Tower.look _) (y ∘ Subtype.val)=(P.voyageF _ _).aviation _ (Tower.look _) _
   rw [←k]]
 exact ⟨_,rfl⟩
#print basis
omit R in
lemma atSun(p:1≤q)(e:∀p:Vantage,p∈tsupport F.val→q≤dials b p): φ b 1 F=φ b q F:=by
    funext a
    unfold wave DoseTravel.beam
    refine integral_congr_ae (Eventually.of_forall fun r'=>?_)
    by_cases g:F.val r'=0;· simp [g]
    have t:=e r' (subset_closure g)
    dsimp only [trails_LocalFieldBounds,morning];rw [max_eq_right (p.trans t),max_eq_right t]
lemma drapery (U:SampleDose)(e:P.WalkVoucher x V w F U) :
 ∃Q:(G).Op, Feather (Θ) Q ∧ ReadsSix (oneBox (φ false 1 F) (φ true 1 U) Q) ∧
   ∀m,fanSet m→ ‖gate (ounce m (φ false 1 F))‖ ≠0 ∧
                  ‖gate (ounce m (φ true 1 U))‖ ≠0 :=by
 obtain ⟨q,d,h,z,r,r₀,p,p₁,p₂,p₃,Y₀,Z₀,e₁,e₂⟩:=e
 rw [P.atSun x V w false q F p Y₀.wall,P.atSun x V w true q U p Z₀.wall]

 have q₀:0<q:=zero_lt_one.trans_le p
 have u₁(m:ℒ→ℂ)(u':fanSet m):= P.entrance x V w false q F R m q₀ p₁ p₂ p₃ e₁ u'
 have u₂(m:ℒ→ℂ)(u':fanSet m):= P.entrance x V w true q U R m q₀ p₁ p₂ p₃ e₂ u'
 obtain ⟨a,y⟩:=e₁.near
 obtain ⟨b,u⟩:=e₂.near

 obtain ⟨t,w₁⟩:=P.goesSide x (a-b)
 have d₁: ∀m,fanSet m→dist (ounce m (φ false q F)) ((Θ).U t (ounce m (φ true q U)))<‖gate (ounce m (φ false q F))‖:=by
    intro m r'
    refine lt_trans ?_ (u₁ m r')
    let H:=ounce m (P.cotillon x V w q)
    have ee: (Θ).U t (Γ b H)=Γ a H:=by rw [w₁,←ContinuousLinearMap.comp_apply,←P.cart_paves,sub_add_cancel]
    refine lt_of_le_of_lt (dist_triangle _ (Γ a H) _) ?_
    rw [dist_comm (Γ a H) ((Θ).U t _),←ee,dist_eq_norm ((Θ).U t _) _,←map_sub,(Θ).unitary,←dist_eq_norm,ee]
    linarith only [show _ ≤ h/8 from y m r',show _ ≤ h/8 from u m r',p₂]
 obtain ⟨Q,f,g⟩:= incense_fan (Θ) _ _ t d₁
 exact ⟨Q,f,g,fun m p=>⟨(p₂.trans (u₁ m p)).ne',(p₂.trans (u₂ m p)).ne'⟩⟩
#print axioms drapery

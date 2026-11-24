import SatinPP.Rosary
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
local notation "D%" s:max=>P.lengthP s
local notation "F%" s:max=> P.pointEra s
variable (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))

local notation "ℒ"=>Lead.Clan

open DoseTravel Set

variable {f n:ℕ}{Y:ℕ→ P.Apron}(J:P.GalaxyShow x f n Y V)

def apertureD(i:ℕ):ℝ:=(1/2:ℝ)^i
lemma aperture_pos (i): 0<apertureD i:=pow_pos (by norm_num) _
abbrev faceview(a:Vantage)(i:ℕ):= slider a (chosen a i)
lemma radius_exists {x:ℝ}(u:0<x)(i:ℕ)(t:x<apertureD i):
 ∃n≥i,x ≤ apertureD n ∧ apertureD n≤2*x:=by
 have h:Tendsto (fun n=>apertureD (i+n)) atTop (𝓝 0):=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num:(0:ℝ)≤1/2) (by norm_num)).comp (tendsto_atTop_mono (g:=HAdd.hAdd i) (fun n=>Nat.le_add_left ..) tendsto_id)
 have z:∃ n, apertureD (i+n)<x:= (h.eventually (gt_mem_nhds u)).exists
 have p:= Nat.find_spec z
 have q:Nat.find z≠0:= fun y=>by rw [y, add_zero] at p;exact t.not_ge p.le
 obtain ⟨n,m⟩:=Nat.exists_eq_succ_of_ne_zero q
 refine ⟨i+n,Nat.le_add_right ..,le_of_not_gt (Nat.find_min z (show n<Nat.find z by omega)),?_⟩
 rw [m,Nat.add_succ,apertureD,pow_succ] at p
 unfold apertureD;linarith only [p]


def WalkVoucher (w:ℒ→Prism)(F U:SampleDose):Prop:=
 ∃ q d h z r:ℝ,∃ e:0<r,1 ≤ q ∧ 0<d ∧ 0<h ∧ 0<z ∧
    CanMove false F q r e ∧ CanMove true U q r e ∧
    P.Flare x V w false q F d h z ∧ P.Flare x V w true q U d h z
local notation "𝒱"=>P.WalkVoucher x V
include J
/-- At the old clean centers (balanced about wall), free to impose
 any cofinite constraint on aperture level allowed by the clean jet already before this enhancement. -/
lemma jumpSeats (A:P.Silhouette x V)(a b:Vantage)(t:ℝ)(e:1<t)
 (l:dials false a=t)(u:dials true b=t)
 (w:ℒ→Prism)(v:ReadsSix (P.pointPrism x V w (b-a)))
 (H:ℕ→Prop)
 (late:∀ᶠ i in atTop,H i ∧ ReadsSix (P.readPrism x V w 1 (faceview a i) (faceview b i))):
    ∃i w', H i ∧ ReadsSix (P.pointPrism x V w' (b-a)) ∧ ReadsSix (P.readPrism x V w' 1 (faceview a i) (faceview b i)) ∧
        𝒱 w' (faceview a i) (faceview b i) :=by
 obtain ⟨ρ,σ,y⟩:=A
 obtain ⟨M,h,ϵ,g,p,ε,a0⟩:=P.cavalcade x V y J
 let δ:=ϵ/4
 obtain ⟨C,c,bol⟩:∃ C>0, Bolted C:= bolts

 have g₀:0<δ:=by unfold δ; positivity
 have cc:∀ᶠ z:ℝ in 𝓝 0,C*z*M≤δ^2/4:=
    (((show Continuous fun z:ℝ=>C*z*M from by fun_prop).tendsto (0:ℝ))).eventually (ge_mem_nhds (by simpa using (by positivity:(0:ℝ)<δ^2/4)))
 obtain ⟨z,p',L₁,L₂,k⟩:∃ z, 0<z ∧ z≤δ ∧ C*z*M≤δ^2/4 ∧ _:= (Eventually.and (self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ))) (((ge_mem_nhds g₀ |>.filter_mono nhdsWithin_le_nhds)).and ((cc.filter_mono nhdsWithin_le_nhds).and a0))).exists
 obtain ⟨i₀,w₁⟩:=eventually_atTop.1 late
 have gg:=y.scarce.const_mul δ;rw [mul_zero] at gg
 obtain ⟨i,t₁,t₂,d₀⟩:= ((gg.eventually (gt_mem_nhds (aperture_pos i₀))).and ((gg.eventually (gt_mem_nhds (half_pos (sub_pos.mpr e)))).and k)).exists
 let d:=P.lengthP (ρ i); have ds:0<d:=P.lengthP_pos _
 obtain ⟨n,n',f₁,f₂⟩:=radius_exists (mul_pos g₀ ds) i₀ t₁
 let r:=apertureD n; let q:=t-r
 have l₁:1≤q:=by unfold q r; linarith only [e,t₂,f₂]
 have f₀:=aperture_pos n; have l₂:0<q:=zero_lt_one.trans_le l₁
 obtain ⟨u',p₀⟩:=d₀ q l₂
 obtain ⟨j,h₁,h₂,h₃⟩:= P.rehearses x V u' w J _ _ (w₁ n n').2 _ v _ _ p₀

 have S(g:Bool)(A:Vantage)(B:dials g A=t):= P.wave_paid x V j g q J A f₀ ds g₀
    (show dials g A=q+apertureD n from B.trans (sub_add_cancel ..).symm)
    ((mul_assoc 2 δ d).symm ▸ f₂ : apertureD n ≤ 2 * δ * d)
    (show 4*δ≤ϵ from le_of_eq (by unfold δ;ring))
    l₂ bol c p' L₁ L₂ f₁ h₃
 obtain ⟨a₀,a₁⟩:= S _ _ l; obtain ⟨b₀,b₁⟩:= S _ _ u
 exact ⟨n,j,(w₁ n n').1,h₂,h₁,q,d,h,z,r,f₀,l₁,ds,p,p',a₀,b₀,a₁,b₁⟩
#print axioms jumpSeats

import SatinPP.WakeWave
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

open scoped ContDiff
private def proofSign (x:CrossRead):ℂ:= x.det * ∏ i:Lead.Clan,x i i
private lemma proof_sign_lit(M:CrossRead): ReadsSix M ↔ proofSign M ≠ 0 := by rw [proofSign,mul_ne_zero_iff,Finset.prod_ne_zero_iff]; simp [ReadsSix]
lemma royal {H:Hilbert}(A B:ℝ→ℒ→H)
 (x':∀i,AnalyticOnNhd ℝ (fun t=>A t i) Set.univ)
 (y':∀j,AnalyticOnNhd ℝ (fun t=>B t j) Set.univ)
 (h:ReadsSix (matchRoles H (A 1) (B 1))):∀ᶠ t:ℝ in 𝓝[≠] 0,ReadsSix (matchRoles H (A t) (B t)):=by
 let M(t:ℝ):=matchRoles H (A t) (B t);let v:=proofSign ∘ M
 let hg : v 1≠0:= (proof_sign_lit _).mp h
 have hx:AnalyticOnNhd ℝ v Set.univ:=by
   intro t a
   have he(i j:Lead.Clan): AnalyticAt ℝ (fun q=> M q i j) t:= ((x' i t a|>.contDiffAt (n:=ω)).inner ℂ ((y' j t a).contDiffAt (n:=ω))).analyticAt -- tune
   change AnalyticAt ℝ (fun q=> (M q).det * ∏ i:Lead.Clan,M q i i) t
   refine AnalyticAt.mul ?_ (Finset.analyticAt_fun_prod _ (fun i _=> he i i))
   simp_rw [Matrix.det_apply']; exact Finset.analyticAt_fun_sum _ fun i _=> analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun _ _=> he _ _))

 by_contra e
 refine hg (hx.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (z₀:=0) (Set.mem_univ 0) ?_ (Set.mem_univ 1))
 refine (show ∃ᶠ (z:ℝ) in 𝓝[≠] 0, ¬ ReadsSix (M z) from ?_).mono (fun a g=>not_ne_iff.mp (mt ((proof_sign_lit _).2) g))
 exact not_eventually.mp e




variable (u w:ℒ→Prism)
abbrev rosary(t:ℝ)(i:ℒ):Prism:=(1-(t:ℂ)) • u i+(t:ℂ) • w i
lemma beads_0:rosary u w 0=u:=by funext; simp [rosary]
lemma beads_1:rosary u w 1=w:=by funext; simp [rosary]
local notation "row"=>rosary u w
local notation "φ"=>P.cotillon x V
lemma rosary_profile(t q:ℝ)(i:ℒ):
 φ (row t) q i= (1-t) • (φ u q i)+t • φ w q i:=by
 unfold cotillon rosary profilesZ SatinJets.prism;rw [map_add,map_smul,map_smul,Complex.coe_smul,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.coe_smul]
lemma rosary_c(q:ℝ)(i:ℒ):AnalyticOnNhd ℝ (fun t=>φ (row t) q i) Set.univ:=by
 simp_rw [P.rosary_profile]
 exact fun t _=>((analyticAt_const.sub analyticAt_id).smul analyticAt_const).add (analyticAt_id.smul analyticAt_const)
lemma necklace(q:Vantage)(h:ReadsSix (P.pointPrism x V w q)):
 ∀ᶠ t:ℝ in 𝓝[≠] 0, ReadsSix (P.pointPrism x V (row t) q):=by
 let A(t:ℝ):=φ (row t) (q 3/2)
 let B(t:ℝ):= (Γ q) ∘ A t
 have H: P.pointPrism x V (row 1) q=P.pointPrism x V w q:=by rw [beads_1]


 have p:=H.symm ▸ h
 have a(i):AnalyticOnNhd ℝ (fun t=> A t i) Set.univ:=P.rosary_c x V u w _ _
 exact royal A B a (fun i t e=> (((Γ q).restrictScalars ℝ).analyticAt _).comp (a i t e)) p

local notation "O"=> P.wave x V
variable {f n:ℕ}{Y:ℕ→ P.Apron}(J:P.GalaxyShow x f n Y V)
include J
lemma rosary_wave(b:Bool)(F:SampleDose)(i):
 AnalyticOnNhd ℝ (fun t=>O (row t) b 1 F i) Set.univ:=by
 have h(t:ℝ):O (row t) b 1 F i=(1-t) • (O u b 1 F i)+t • (O w b 1 F i):=by
    let A(v:ℒ→Prism):= beam_int _ F (P.trails_c x V v b 1 J zero_lt_one i)
    unfold wave DoseTravel.beam
    rw [←integral_smul, ←integral_smul, ←integral_add]
    rotate_left
    · exact Integrable.smul (1-t) (A u)
    · exact Integrable.smul t (A w)
    refine integral_congr_ae (Eventually.of_forall fun p=>?_)


    change (F.val p:ℂ) • Γ p (φ (row t) (morning b 1 p) i) =
        (1-t) • ((F.val p:ℂ) • Γ p (φ u (morning b 1 p) i))+t • ((F.val p:ℂ) • Γ p (φ w (morning b 1 p) i))
    simp_rw [P.rosary_profile,← Complex.coe_smul,map_add,map_smul,smul_add,smul_smul]
    rw [mul_comm (↑(F.val p):ℂ),mul_comm (↑(F.val p):ℂ)]
 simp_rw [h]
 exact fun t _=>((analyticAt_const.sub analyticAt_id).smul analyticAt_const).add (analyticAt_id.smul analyticAt_const)
lemma jasper(F U:SampleDose)(h:ReadsSix (P.readPrism x V w 1 F U)):
 ∀ᶠ t:ℝ in 𝓝[≠] 0, ReadsSix (P.readPrism x V (row t) 1 F U):=by
 have H:P.readPrism x V (row 1) 1 F U=P.readPrism x V w 1 F U:=by rw [beads_1]
 have y b:=P.rosary_wave x V u w J b
 exact royal (fun t=> O (row t) false 1 F) (fun t=> O (row t) true 1 U)
    (y false F) (y true U) (show ReadsSix (P.readPrism x V (row 1) 1 F U) from H.symm ▸ h)

lemma rehearses (F U:SampleDose)(h:ReadsSix (P.readPrism x V w 1 F U))(b:Vantage)(c:ReadsSix (P.pointPrism x V w b))
 (q:ℝ)(T:(ℒ→G)→Prop)(v:∀ᶠ p in 𝓝 (P.cotillon x V u q), T p):
 ∃u', ReadsSix (P.readPrism x V u' 1 F U) ∧ ReadsSix (P.pointPrism x V u' b) ∧ T (P.cotillon x V u' q):= by
 have p:Tendsto (fun t=> φ (row t) q) (𝓝[≠] (0:ℝ)) (𝓝 (φ u q)):=by
    have H:Tendsto (fun t=> φ (row t) q) (𝓝 0) (𝓝 (φ (row 0) q)):=
        tendsto_pi_nhds.mpr fun i=>(P.rosary_c x V u w q i _ (Set.mem_univ _)).continuousAt.tendsto
    rw [beads_0] at H
    exact H.mono_left nhdsWithin_le_nhds
 obtain ⟨t,h'⟩:= ((P.jasper x V u w J F U h).and ((P.necklace x V u w b c).and (p.eventually v))).exists
 exact ⟨row t,h'⟩
#print axioms rehearses


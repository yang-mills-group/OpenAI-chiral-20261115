import SatinPP.Hutch
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

local notation "H"=> P.ColorHil 3 ξ
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Δ"=> P.truck 3 ξ
local notation "ω"=> P.colorZero 3 ξ

variable (A:ℕ→P.Apron)(c r n:ℕ→ℕ)(w:ℒ→ Prism)(g h:ℕ)
variable (T:P.HandleWith x c r A n)
local notation "W"=> P.soldTrumpet A c r n w
local notation "B[" a "," i "]"=> P.sold_birth x A c r n w a i T
local notation "η"=>P.enter 3 ξ

variable (R:P.ThinArmada x A c r n w T V g h)(J:P.Ellis 3 x)
variable (b:Bool)(q:ℝ)(F:SampleDose)
local notation "Xᵦ"=>P.pastureGrid x A c r n w T b
local notation "ν"=>P.wave x V w b q
include R J
local notation "Ω₁"=> P.advocate 3 x 3
variable {d y z:ℝ}(df:0<d)(yp:0<y)(u:IsPaid b q F)(e:0<q)
 (Q:P.Flare x V w b q F d y z)

omit J
local notation "𝒞" a:max i:max => P.cradleH x (W a i) B[a,i]
include e
lemma herd_thick:∃ M> (0:ℝ),∀ᶠ i in atTop,∀ a, ‖P.cradleH x (W a i) B[a,i] q‖≤M:=by
 obtain ⟨m,s⟩:=(Set.finite_range (fun a=> ‖P.profilesH x w a V q‖)).bddAbove
 let r₀:=max (m+1) 1
 refine ⟨r₀,zero_lt_one.trans_le (le_max_right ..), eventually_all.mpr fun a =>?_⟩
 have K:‖P.profilesH x w a V q‖<r₀:=(lt_add_of_le_of_pos (s ⟨a,rfl⟩) zero_lt_one).trans_le (le_max_left ..)
 exact (R.heated_points a q e).1.norm.eventually (ge_mem_nhds K)
omit e R
lemma herd_cost(U:SampleDose):
    ∃ D>0,∀ᶠ i:ℕ in atTop,P.humidity i U ≤D:=by
 let u':= ∫p,‖U.val p‖
 let D':=max (u'+1) 1
 exact ⟨D',zero_lt_one.trans_le (le_max_right ..), (P.thin_activation_abs U).eventually (ge_mem_nhds ((show u'<u'+1 from lt_add_of_pos_right _ zero_lt_one).trans_le (le_max_left _ _)))⟩
include R e
-- avoid v shadow
lemma stable_pitch {r':ℝ}(f:0<r')(Y:CanMove b F q r' f):
 ∃ L₀>0,∀ᶠ i:ℕ in atTop,∀t'≥i,∀s' τ,0<s'→s'≤τ→τ≤r'→ ∀j:Axis,j≠3→∀m,fanSet m→
    dist (ounce m (Xᵦ (bike (footfall j) F s') i t'))
      (ounce m (Xᵦ (bike (footfall j) F τ) i t'))≤ L₀*τ:= by
 obtain ⟨a,rfl⟩:=Y.pix
 obtain ⟨M,mp,s₀⟩:=P.herd_thick x V A c r n w g h T R q e
 obtain ⟨C,cp,bol⟩:∃ C>0, Bolted C:= bolts
 obtain ⟨D',dp,hk⟩:=P.herd_cost (facing b (coverall a f))
 obtain ⟨i₀,hi⟩:=eventually_atTop.1 hk
 refine ⟨6*(D'*((C/r'^2)*M)),by positivity,?_⟩


 filter_upwards [s₀,eventually_ge_atTop i₀] with i M' t₀ k t' s τ s_p st le_r j j' m m'
 rw [dist_eq_norm];unfold ounce;rw [←sum_sub_distrib]
 simp_rw [←smul_sub]
 rw [mul_assoc]
 refine ounce_bound m (v:=fun i₁=> Xᵦ (bike (footfall j) (pixel' a r' f) s) i k i₁ - Xᵦ (bike (footfall j) (pixel' a r' f) τ) i k i₁) m' (fun a'=>?_ )
 rw [←dist_eq_norm]
 have D₀:=hi k (t₀.trans t')
 have x':0<τ:=s_p.trans_le st
 apply (P.harvest_grade x _ B[a',i] k b q bol cp e f Y.wall j j' s_p st le_r).trans
 exact (mul_le_mul D₀ (mul_le_mul_of_nonneg_left (M' a') (by positivity)) (mul_nonneg (by positivity) (norm_nonneg _)) dp.le).trans_eq (by ring)


include J Q df
lemma sharp_pitch (vp:0<z) {r':ℝ}(f:0<r')(Y:CanMove b F q r' f):
 ∃τ>0,∀ᶠ i:ℕ in atTop,∀t'≥i,∀l:ℝ,0<l→l≤τ→ ∀j:Axis,j≠3→∀m,fanSet m→
    ‖ounce m (Xᵦ (bike (footfall j) F l) i t')‖≤ (13/2)/d:=by
 obtain ⟨L,p,S'⟩:=P.stable_pitch x V A c r n w g h T R b q F e f Y
 let τ:= min (min (d*z) r') (((1/2)/d)/L)
 have p₀:0<τ:=by unfold τ; positivity
 have h₁:τ≤d*z ∧ τ≤r' ∧ L*τ≤(1/2)/d:=by
    rw [mul_comm L,← le_div_iff₀ p]
    exact ⟨(min_le_left ..).trans (min_le_left ..),(min_le_left ..).trans (min_le_right ..),min_le_right ..⟩
 refine ⟨τ,p₀,?_⟩
 have q':=P.hutch_space x V A c r n w g h T R J b q F df Y.wall e Q p₀ h₁.1
 filter_upwards [q',S'] with i v h'' t₀ u₀ l pl lt' j j0 m v'
 let Z(h₁:ℝ):=ounce m (Xᵦ (bike (footfall j) F h₁) i t₀)
 apply (norm_le_insert' (Z l) (Z τ)).trans
 rw [←dist_eq_norm]


 exact (add_le_add (v _ u₀ j j0 m v') ((h'' _ u₀ _ _ pl lt' h₁.2.1 j j0 m v').trans h₁.2.2)).trans_eq (by ring)

-- transfer identity in span
omit R J df e Q
lemma stable_div {I:Hilbert}(m:ℒ→ℂ)(f g:ℒ→I)(A':I.Op){l r':ℝ}(h₀:0<l)
    (hg:∀a:ℒ,g a=l⁻¹ • (f a-A' (f a)))(p:‖ounce m g‖≤r'):
 dist (ounce m f) (A' (ounce m f))≤ l*r':=by
 have z:ounce m g=l⁻¹ • (ounce m f-A' (ounce m f)):=by
    rw [←Complex.coe_smul, ←ounces_map]
    unfold ounce
    rw [←sum_sub_distrib,smul_sum]
    exact sum_congr rfl fun a _=>by rw [hg,←smul_sub,←Complex.coe_smul,smul_smul,smul_smul,mul_comm];rfl
 rw [z,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity:l⁻¹>0), ←dist_eq_norm] at p
 exact (inv_mul_le_iff₀ h₀).mp p


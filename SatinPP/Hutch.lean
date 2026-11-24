import SatinPP.Bough
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 150000
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
def pastureGrid(b:Bool)(F:SampleDose)(i t:ℕ)(a:ℒ):H:= P.harvest x _ B[a,i] t b F

variable (R:P.ThinArmada x A c r n w T V g h)(J:P.Ellis 3 x)
variable (b:Bool)(q:ℝ)(F:SampleDose)
local notation "Xᵦ"=>P.pastureGrid x A c r n w T b
local notation "ν"=>P.wave x V w b q
include R J
lemma pasture_one (p:IsPaid b q F)(e:0<q)
 (k:ℕ→ℕ)(u:Tendsto k atTop atTop) (a:ℒ):
 Tendsto (fun i=>Xᵦ F i (k i) a) atTop (𝓝 (η (ν F a))):=by
 cases b
 · exact (P.illuminate_backward x A c r n w V g h T R J q a F e p).2 k u
 exact (P.illuminate_forward x A c r n w V g h T R J q a F e p).2 k u
lemma pasture_near (p:IsPaid b q F)(e:0<q)
 (k:ℕ→ℕ)(u:Tendsto k atTop atTop){δ:ℝ}(f:0<δ):
 ∀ᶠ i in atTop,∀m,fanSet m→dist (ounce m (Xᵦ F i (k i))) (η (ounce m (ν F))) ≤ δ:=by
 have l:∀ᶠ i in atTop,∀a,dist (Xᵦ F i (k i) a) (η (ν F a)) < δ/6:=
    eventually_all.mpr fun a=> (P.pasture_one x V A c r n w g h T R J b q F p e k u a).eventually (ball_mem_nhds _ (by positivity))
 refine l.mono fun i y m t=>?_
 rw [dist_eq_norm];unfold ounce;rw [map_sum, ←sum_sub_distrib];simp_rw [map_smul,←smul_sub]

 have w':‖ounce m (fun a=> Xᵦ F i (k i) a - η (ν F a))‖≤6*(δ/6):=
    ounce_bound m t (fun a=>by rw [←dist_eq_norm];exact (y a).le)
 exact w'.trans_eq (by ring)
omit R J in
lemma walk_heat (T':ℝ≥0)(v:G):(S).E T' (η v)= η ((Θ).E T' v):=rfl

omit R J in 
lemma hutch_rule {Q:ℕ→ℕ→Prop}(h₀:∀ k:ℕ→ℕ,Tendsto k atTop atTop → ∀ᶠ i in atTop,Q i (k i)) :
 ∀ᶠ i in atTop,∀ t'≥i,Q i t':=by
 choose k g v using show ∀i:ℕ,∃t:ℕ,i≤t∧ (Q i t→∀s≥i,Q i s) from fun i=>by
    by_cases d:∀s≥i,Q i s
    · exact ⟨i,le_rfl,fun _=>d⟩
    push Not at d
    obtain ⟨s,u,w'⟩:=d
    exact ⟨s,u,fun z=>(w' z).elim⟩
 exact (h₀ k (tendsto_atTop_mono g tendsto_id)).mono v

lemma hutch (p:IsPaid b q F)(e:0<q){δ:ℝ}(f:0<δ):
 ∀ᶠ i in atTop,∀ t'≥i,∀m,fanSet m→dist (ounce m (Xᵦ F i t')) (η (ounce m (ν F))) ≤ δ:=
 hutch_rule fun k z=>P.pasture_near x V A c r n w g h T R J b q F p e k z f
variable {d y z:ℝ}(hp₁:0<d)(hp₂:0<y)(u:IsPaid b q F)(e:0<q)
 (Q:P.Flare x V w b q F d y z)
include hp₁ u e Q


lemma hutch_space{l:ℝ}(s:0<l)(o:l≤ d*z) :
 ∀ᶠ i in atTop,∀ t'≥i,∀j:Axis,j≠3→∀m,fanSet m→
    ‖ounce m (Xᵦ (bike (footfall j) F l) i t')‖ ≤ 6/d:=by
 have C (j:Axis)(v:j≠3):= P.hutch x V A c r n w g h T R J b q _ (u.wheels j v l) e (δ:=(1/2)/d) (by positivity)
 filter_upwards [eventually_all.mpr (fun j=>eventually_all.mpr (C j))] with i L t' a j f m k
 let β:= bike (footfall j) F l
 apply (norm_le_insert' (ounce m (Xᵦ β i t')) (η (ounce m (ν β)))).trans
 rw [LinearIsometry.norm_map,←dist_eq_norm]
 exact (add_le_add (Q.spire j f l s o _ k) (L j f _ a _ k)).trans_eq (by ring)


omit R J hp₁ u e Q
lemma hutch_cap {I:Hilbert}(a:ℒ→I):∃B,∀m,fanSet m→‖ounce m a‖≤B:=by
 obtain ⟨s,c₀⟩:= (Set.finite_range (fun i=> ‖a i‖)).bddAbove
 exact ⟨6*s,fun m h₀=> ounce_bound m h₀ (d:=s) (fun i=> c₀ ⟨i,rfl⟩)⟩
include R J u e Q hp₂
lemma hutch_hold:
 ∃C,∀ᶠ i in atTop,∀t'≥i,∀m,fanSet m→
    ‖ounce m (Xᵦ F i t')‖≤C ∧
    7*y ≤ dist (ounce m (Xᵦ F i t')) ((S).E (d*y).toNNReal (ounce m (Xᵦ F i t'))):=by
 obtain ⟨C,c₀⟩:=hutch_cap (ν F)
 refine ⟨C+y/8,(P.hutch x V A c r n w g h T R J b q _ u e (δ:=y/8) (by positivity)).mono fun i Z t' a m k=>?_⟩
 let X:=η (ounce m (ν F)); let Y:=ounce m (Xᵦ F i t')
 let U:=(S).E (d*y).toNNReal
 have Y₀:dist Y X≤y/8:= Z _ a _ k

 constructor
 · apply (norm_le_insert' Y X).trans (add_le_add _ (by rw [←dist_eq_norm];exact Y₀))
   unfold X;rw [LinearIsometry.norm_map];exact c₀ _ k
 have hU: (29/4)*y ≤ dist X (U X):=by
    unfold X U; rw [P.walk_heat,LinearIsometry.dist_map]; exact Q.swipe m k
 have D:= (abs_le.mp (lipschitz (A:=U) ((S).shrinks _) Y X)).1
 change _ ≤ dist Y (U Y)
 linarith only [D,hU,Y₀]

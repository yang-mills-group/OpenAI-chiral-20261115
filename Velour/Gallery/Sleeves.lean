import Velour.Gallery.Canvases
import Velour.Wadding.Wadding
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 110000
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
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine




open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set



open YM.Velour
open Boundary Probe

variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "ℋ"=> P.ColorHil j x
local notation "𝓗"=> P.ManyF j x
local notation "Σ₀"=> P.physicalEnergy j x
local notation "Σ₁"=> P.seasons j x

local notation "D"=> (Σ₁).muslin
local notation "Φ"=> (Σ₁).Detector
local notation "U"=> (Σ₁).unit.translation
local notation "Ω"=> P.heaven j x


local notation "E"=>(Σ₁).E
def mounted (A:P.Apron):(𝓗).Op:= P.tableau j x 0 (A.engine P j x)
def matt (A:P.Apron)(d:ℝ≥0):(𝓗).Op:=E d*P.mounted j x A*E d

lemma sleeve_dense : DenseRange (fun A=>P.mounted j x A Ω):= by
 convert P.single_sleeve_dense j x using 2
 rename_i A
 exact P.lyre j x (A.engine P j x) Ω
lemma sleeve_star (A:P.Apron): star (P.mounted j x A)=P.mounted j x (A.kiss P j):= by
 unfold mounted; rw [P.lyre_star,A.peer]
def sleeve (A:P.Apron):Φ:= (Σ₁).labelled (P.mounted j x A)
lemma sleeve_lit (A:P.Apron): (Σ₁).Instates (P.matt j x A) (P.sleeve j x A):= by
 rw [show P.sleeve j x A=(Σ₁).hatch (P.mounted j x A) 0 from ?_]
 · apply hatch_welcome
   intro d q
   rw [pow_zero,one_mul,mul_one]
   rfl
 ext1 f; ext1 u
 change _= (Σ₁).weight 0 ((P.sleeve j x A f) ((Σ₁).weight 0 u))
 rw [weight0,weight0]

abbrev Brocade := P.Bobbin j x ⊕ P.Apron
def drapes : P.Brocade j x→ Φ :=Sum.elim (P.detects j x) (P.sleeve j x)
def velourDrapery : P.Brocade j x→ℝ≥0→ (𝓗).Op :=Sum.elim (P.bobQuote j x) (P.matt j x)
lemma brocade_storage : (Σ₁).Fray (P.velourDrapery j x) (P.drapes j x):= by
 constructor
 · rintro (a|a)
   · exact (P.satin_storage j x).1 a
   · exact P.sleeve_lit j x a
 rintro (a|a)
 · obtain ⟨r,p⟩ := (P.satin_storage j x).2 a
   exact ⟨.inl r,p⟩
 refine ⟨.inr (a.kiss P j), Eventually.of_forall ?_⟩
 intro t
 change star (_*_*E t)= P.matt j x (a.kiss P j) t
 rw [star_mul,star_mul,P.sleeve_star,show star (E t)= E t from (Σ₁).sym t,matt,mul_assoc]

-- No need combine first. Any Fray family containing sleeves has full reach.

lemma reach_top {ι:Type}{d:ι→Φ}{q:ι→ℝ≥0→ (𝓗).Op} (v:(Σ₁).Fray q d)
 (h:∀a,∃i, q i=P.matt j x a)
 (r:P.invCrown j x):
 (Σ₁).nursery d (P.firstTulle j x)=⊤:=by
 let N:=(Σ₁).nursery d (P.firstTulle j x)
 have c:IsClosed (N:Set (𝓗).space):= nursery_closed
 suffices e:Set.range (fun A=>P.mounted j x A Ω) ⊆ N from
   top_unique (fun a _=>closure_minimal e c ((P.sleeve_dense j x) a))
 rintro _ ⟨A,rfl⟩
 obtain ⟨i,h⟩:=h A
 have a: Tendsto (fun t=> E t (P.mounted j x A Ω)) (𝓝[>] 0)
     (𝓝 (P.mounted j x A Ω)) := by
    simpa only [eZero, ContinuousLinearMap.id_apply] using
      (((Σ₁).continuousE _).tendsto 0).mono_left nhdsWithin_le_nhds
 apply c.mem_of_tendsto a
 have b:Ω∈N:= OS.Semigroup.reflected (P.firstTulle j x) ((Σ₁).at_bud ..)
 filter_upwards [self_mem_nhdsWithin] with t ht
 rw [←P.heaven_hot j x t]
 -- only right
 have z:=(v.pruned_keep (P.crown_vac j x r) i).2
 rw [h] at z
 exact z t ht b
lemma whole_reach (r:P.invCrown j x) :
 (Σ₁).nursery (P.drapes j x) (P.firstTulle j x)=⊤:= reach_top P j x (P.brocade_storage j x) (fun a=>⟨Sum.inr a,rfl⟩) r


local notation "G" => P.Viewers j x
lemma mounted_VEV (A:P.Apron): inner ℂ Ω (P.mounted j x A Ω)= P.singleState j A.s x A.F:= by
 have z(y:ℋ):inner ℂ Ω (P.wealth j x y) = inner ℂ (P.colorZero j x) y:=by
    have h : (P.wealth j x y:G) = (G).orthogonalProjectionOnto y :=
      Subtype.ext (DFunLike.congr_fun (P.visitors_op j x) y)
    exact (congrArg (inner ℂ Ω) h).trans (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (K:=G) Ω y)
 unfold mounted; rw [lyre,z]
 exact (A.sewn.expected (x:=x)).trans (P.slide_single ..)
theorem sleeve_reading (A:P.Apron)(f:Test4)(e:P.invCrown j x) :
 inner ℂ Ω ((P.sleeve j x A f (P.firstTulle j x)).val)=
 (∫b:E4,f b)*P.singleState j A.s x A.F:=by
 change inner ℂ Ω ((Σ₁).rasp _ _ Ω)=_
 have t(b): inner ℂ Ω ((Σ₁).dangle b (P.mounted j x A) Ω)=P.singleState j A.s x A.F:= by
   have v:U (-b) Ω=Ω:=P.crown_vac j x e _
   unfold dangle
   rw [mul_apply_eq_comp,v,mul_apply_eq_comp,
     ← ContinuousLinearMap.adjoint_inner_left,
     show (U b).adjoint=U (-b) from (Σ₁).unit_star b, v,P.mounted_VEV]
 rw [←rasp_inner]; simp_rw [t,smul_eq_mul]
 rw [integral_mul_const]

#print axioms sleeve_reading
#print axioms brocade_storage
#print axioms whole_reach
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

import ZecaMirror
import ZecaSlip
import SatinThinQuizPair
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
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
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets


open DoseTravel Set

private lemma smooth_norm : Tendsto (fun i:ℕ=>(1/2:ℝ)^i) atTop (𝓝 0):=
 tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

variable (p:Vantage)(q:ℕ→Vantage)(v:Tendsto q atTop (𝓝 p))
include v
lemma floats (Q:Set Vantage)(h:Q ∈𝓝 p):
 ∀ᶠ i in atTop, q i∈Q ∧ tsupport (skate (q i) i).val ⊆ Q:=by
 obtain ⟨ε,he,k⟩:=Metric.mem_nhds_iff.mp h
 filter_upwards [v.eventually h,smooth_norm.eventually (gt_mem_nhds (half_pos he)),
    v.eventually (Metric.ball_mem_nhds p (half_pos he))] with i h r s
 refine ⟨h, fun x y=>k ?_⟩
 have m:dist x (q i)≤(1/2:ℝ)^i:=
    mem_closedBall.mp ((DoseTravel.supported (q i) (chosen (q i) i) ▸ (show x∈tsupport (slider (q i) (chosen (q i) i)).val from y)):x∈ closedBall (q i) ((1/2:ℝ)^i))
 exact mem_ball.mpr ((dist_triangle x (q i) p).trans_lt (show _ < ε from (add_lt_add (m.trans_lt r) (mem_ball.mp s)).trans_eq (add_halves _)))

lemma moveSpray (X:Hilbert)(y:Vantage→X)(c:Continuous y):
 Tendsto (fun i=>DoseTravel.beam X (skate (q i) i) y) atTop (𝓝 (y p)):=by
 apply Metric.tendsto_nhds.mpr; intro ε e
 let S:= y ⁻¹' (Metric.ball (y p) (ε/2))
 filter_upwards [floats p q v S ((c.tendsto p).eventually (Metric.ball_mem_nhds _ (half_pos e)))] with i a
 rw [dist_eq_norm]
 exact lt_of_le_of_lt (tol p X y c (skate (q i) i) (prescribed ..) (ε/2) (fun z h=>
        lt_of_eq_of_lt (dist_eq_norm (y z) (y p)).symm (mem_ball.mp (a.2 h))|>.le)) (half_lt_self e)

variable (p':Vantage)(X:Hilbert)
 (A B:Lead.Clan→ Vantage→ X)(u:∀i,Continuous (A i))(k:∀i,Continuous (B i))
local notation "J"=> matchRoles X (fun i=>A i p') (fun i=>B i p)

include u k in
lemma bothSix (e:ReadsSix J):
 ∀ᶠ i in atTop, ReadsSix (crossBeams X A B (skate p' i) (skate (q i) i)) ∧
       ReadsSix (matchRoles X (fun j=>A j p') (fun j=>B j (q i))):=by
 have l:=readsSix_open.mem_nhds e
 have t:Tendsto (fun i=> crossBeams X A B (skate p' i) (skate (q i) i)) atTop (𝓝 (J)) :=
   tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=>
    (sprinkle p' X (A i) (u i)).inner (moveSpray p q v X (B j) (k j))
 have t':Tendsto (fun i=>matchRoles X (fun j=>A j p') (fun j=>B j (q i))) atTop (𝓝 (J)):=
   tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=>
    (tendsto_const_nhds (x:= A i p')).inner (((k j).tendsto p).comp v)
 exact (t.eventually l).and (t'.eventually l)

omit v

lemma minkSequence (p:Vantage)(C:ℕ→Vantage→Prop)
 (h:∀ᶠ i:ℕ in atTop, ∃ᶠ t:ℝ in 𝓝 0,C i (p+ripple (-t))):
 ∃ q:ℕ→Vantage,Tendsto q atTop (𝓝 p)∧ ∀ᶠ i in atTop,C i (q i):=by
 have e: Tendsto (fun t=>p+ripple (-t)) (𝓝 0) (𝓝 p):=by
   have v:Continuous (fun t=>p+ripple (-t)):=continuous_const.add (ripple_cont.comp continuous_id.neg)
   have u:=v.tendsto 0; rw [neg_zero,ripple_zero,add_zero] at u;exact u
 let d:=fun i:ℕ=>(1/2:ℝ)^i
 have k(i:ℕ):0<d i:=by unfold d; positivity
 obtain ⟨g,b⟩:= eventually_atTop.mp h
 have hv(i:ℕ): ∃ x∈ball p (d i),g ≤ i →C i x :=by
    by_cases n:g ≤ i 
    · obtain ⟨t,z,u⟩:= ((b i n).and_eventually (e.eventually (Metric.ball_mem_nhds p (k i)))).exists
      exact ⟨_,u,fun _=>z⟩
    exact ⟨p,mem_ball_self (k i),fun t=>(n t).elim⟩
 choose y b₁ b₂ using hv
 refine ⟨y,Metric.tendsto_nhds.mpr ?_,(eventually_ge_atTop g).mono b₂⟩
 exact fun _ a=>((show Tendsto d atTop (𝓝 0) from smooth_norm).eventually (gt_mem_nhds a)).mono fun i s=> (mem_ball.mp (b₁ i)).trans s

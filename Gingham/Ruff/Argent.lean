import Gingham.Ruff.Silver
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine.Gingham

open Spine
variable (P:Spine)

namespace VoyageB
open Diary
open CF.Gingham.Ruff
variable (a c μ E:ℝ)(d l s i k:ℕ)
local notation "Y"=>P.run
local notation "~p~" s:max=>P.run.meter.a s
local notation "K"=>P.calibration
local notation "W"=>underlay P.par
local notation "R" s:max i:max k:max => RootBook Y i k s
local notation "Ω" s:max i:max => Journey.side Y i s



open VelourBoard
open Papyrus Papyrus.Franc Preparation Yoke
open Pressure.Worth
variable {P s i k} {C ρ v q :ℝ}
local notation "𝒳" s:max i:max => exhibit P.run P.large s i
set_option linter.unusedSectionVars false

/- verified after YM/SU5/Thin/Whim/Sedge.lean -/
private lemma tighten{Kt:Calibration}{F:Family Kt}{a b:ℝ}(p:pay F a)(h:a≤b):pay F b:= fun n x=> (p n x).trans h
private lemma scaleQ {Kt:Calibration} {F:ℕ→ Family Kt}{S:Finset Cover}{f:Family Kt}(p:SlabMark.BQueue S F f)(z:ℂ):BQueue S (fun i=>z • F i) (z • f):=by
 obtain ⟨t,h,⟨C,b,u,v⟩,s⟩:=p; refine ⟨fun i=> (Buffered.InTest.smul _ (t i)),.smul _ h,⟨‖z‖*C+1,(by positivity),tighten (pay_scale u z) (by linarith),v.mono fun i h=> tighten (pay_scale h z) (by linarith)⟩,fun ε p=>?_⟩; let d:= ε/(‖z‖+1); have he:0<d:= by unfold d; positivity
 filter_upwards [s d he] with i hx; rw [←smul_sub]; apply tighten (pay_scale hx z); have h:d*(‖z‖+1)=ε:=div_mul_cancel₀ _ (by positivity); nlinarith only [he,h]
private lemma polishQ {Kt:Calibration} {S T:Finset Cover}{F G:ℕ→Family Kt}{f g: Family Kt} (p:BQueue S F f)(q:BQueue T G g):BQueue (S∪T) (fun i=> F i-G i) (f-g):=by
 obtain ⟨h,u,⟨C,a,x,v⟩,e⟩:=p; obtain ⟨t,h',⟨D,d,r,w⟩,e'⟩:=q; refine ⟨fun i=> InTest.subOp ((h i).mono subset_union_left) ((t i).mono subset_union_right),InTest.subOp (u.mono subset_union_left) (h'.mono subset_union_right),⟨C+D,(by positivity),pay_sub x r,(v.and w).mono fun i h=>pay_sub h.1 h.2⟩,fun b p=>?_⟩
 filter_upwards [e (b/2) (by positivity),e' (b/2) (by positivity)] with i hx hz; rw [sub_sub_sub_comm]; exact tighten (pay_sub hx hz) (by linarith)

namespace Regalia
variable {S T U:Finset Cover} {A X:Cluster P.calibration}
  {ν:ℕ→ℕ}
local notation "Λ" => Regalia P ρ s ν
lemma broaden (p:Λ S A q)(t:S⊆T):Λ T A q:=by
 obtain ⟨g,h,v,f⟩:=p
 exact ⟨⟨fun _=>(g.whereTo _).mono t, g.landing.mono t,g.bdd,g.saved⟩,h,v,f⟩

lemma adorn(p:Λ S A v)(t:Λ T X q):Λ (S∪T) (A*X) (v*q):=
 ⟨p.queue.multiply t.queue, (enclave P.calibration).mul_mem p.legal t.legal,mul_nonneg p.pos t.pos,
    (p.late.and t.late).mono (fun _ h=> h.1.pair h.2)⟩

lemma apart(p:Λ S A v)(t:Λ T X q):Λ (S∪T) (A-X) (v+q):=
 ⟨polishQ p.queue t.queue, (enclave P.calibration).sub_mem p.legal t.legal, add_nonneg p.pos t.pos,
    (p.late.and t.late).mono (fun _ h=> h.1.subtract h.2)⟩

lemma scale(p:Λ S A v)(z:ℂ):Λ S (z • A) (‖z‖*v):=
 ⟨scaleQ p.queue z, (enclave P.calibration).smul_mem p.legal z, mul_nonneg (norm_nonneg _) p.pos,
    p.late.mono (fun _ h=> h.scale z)⟩



lemma lime(p:Λ S A v)(t:Λ T X q):Λ (S∪T) (A+X) (v+q):=by
 simpa using p.apart (t.scale (-1))

lemma raise(p:Λ S A v)(t:v≤q):Λ S A q:=
 ⟨p.queue,p.legal,p.pos.trans t,p.late.mono (fun _ h=>h.raise t)⟩

lemma moss(p:Λ S A v)(j:Axis)(u:ℤ):
     Λ (reflectedBox j u S) (fun i=>Tower.mirror K j u (A i)) v:=by
 refine ⟨p.queue.revolve j u, ?_,p.pos, ?_⟩
 · let X:=inLeaf p.queue.landing
   change _ ∈ _
   rw [(enclave_spec P.calibration)] 
   intro m
   exact covariant_reflected (p.queue.landing.support m) ((enclave_spec P.calibration).mp p.legal m) u j
 exact p.late.mono (fun _ h=> h.poseB j u)

lemma leaves(p:Λ S A v)(r:List (Axis×ℤ)):
     Λ (CF.Gingham.Ruff.stage r S) (Dancing r A) v:= by
 induction r with
 | nil=>exact p
 | cons a r ih=>exact ih.moss _ _

lemma stems(p:Λ S A v)(j:Axis)(u:ℤ):
    Λ (plow K j u S) (fun i=>relocate K j u (A i)) v:=
 ⟨p.queue.station j u,(p.moss j 0|>.moss j (gaugeT K u)).legal,p.pos,
    p.late.mono (fun _ h=>h.ticks j u)⟩

lemma fall:Regalia P ρ s ν S 0 0:=
  ⟨(show Bouquet S 0 false (0:Cluster K) from Bouquet.nil).check, Subalgebra.zero_mem _,le_refl _,
     Eventually.of_forall (fun _=>Shining.pennies)⟩


lemma winding {I:Type*}{T:Finset I}{Z:I→Cluster K}{d:I→ℝ}
     (p:∀x∈T, Regalia P ρ s ν S (Z x) (d x)):
     Λ S (∑x∈T,Z x) (∑x∈T,d x):=by
 induction T using Finset.induction_on with
 | empty=>rw [sum_empty,sum_empty];exact fall
 | insert x t h ih=>
    rw [sum_insert h,sum_insert h]
    have g:=(p _ (mem_insert_self ..)).lime (ih (fun _ h=>p _ (mem_insert_of_mem h)))
    rwa [union_idempotent] at g

#print axioms winding
end Regalia


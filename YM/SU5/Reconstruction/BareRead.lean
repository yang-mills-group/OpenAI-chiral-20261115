import VerifiedSatinSelectedSectors
import YM.SU5.Reconstruction.NoWrapPairs
import YM.CF.Reed.Play
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected PhaseChoice PhaseChoice.SameCharacter PhaseChoice.Theory
open Tapestry Tapestry.Altitude Tapestry.Exhibition

/-!
# Identification on the actual UV regularization

Pin down exactly the cost of the full supported polynomials, not only in limiting
refinement semantics but in the cutoffs removed in this law. Demand for
true bare gauge and matter system in all readings at every affordability.
Drop all auxiliary dependence of the marked operator at that very bare
resolution. Its support still stays within a fixed physical region as the cutoff
is removed. There is no *norm* control here at such moving height! We use only
actual-read identities there, do not infer moving-height bounds from this locality.
-/

open _root_.YM.CF.Py.Rate.LocalLimit
open Dial Thera Scree Paige -- collision `Orbit`?
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable (i k : ℕ)
local notation "m" => Y.uv k
local notation "V" => Journey.side Y i (Y.uv k)
local notation "R" => Y.voyage i
local notation "ρ" => (R).CapeT m
local notation "G" => ((R).X m).gram m
local notation "β" => (G).beta
local notation "P" => partitionZ G Λ.U ρ
local notation "p" => (Y.meter.a m).threshold
local notation "w" => Vale.capP («K»:=Λ.K) («m»:=Vale.mesh (Y.ir i) Λ.R.L m) Λ.U β (Y.meter.a m) -- m local notation
local notation "o" => Dial.mateK V
local notation "μ" => Wilson.prior SU.group (More V)

section diagonal
-- test operator on original links
noncomputable def observableTop (x : Cloud (Dome (tent Y H)))
    (U : Pane (Journey.side Y i (Y.uv k))) := attire (breathing Y H (Y.uv k) i k x) (U,U)
noncomputable def numeratorTop (x : Cloud (Dome (tent Y H))) (U : Pane (Journey.side Y i (Y.uv k))) : ℂ :=
  inner ℂ o (acts (observableTop Y H i k x U) (w U))

lemma top_system (a : Skye.Orbit (Journey.side Y i (Y.uv k)))
    (h : flags ((Y.meter.a (Y.uv k)).threshold) a.1=∅) :
    ρ a=a.1 ∧
    (let F := Lat.frame SU.matter (Cube.links a.1) (Lat.anticut (Journey.side Y i (Y.uv k))); let PS:= spar Λ.K.j babyM a.1
     Safe F.H ∧ PS=portW (Tulip.helix _).symm (projector F.H) ∧ Sea PS (changeM Λ.U a.1 babyM) ∧
     (denZ G Λ.U ρ a)= Complex.exp (-((β * basicP Λ.K.top.clip a.1 : ℝ):ℂ)) • changeM Λ.U a.1 babyM ∧
     F.overlap * projector F.H = cutM (Lat.upperP (Journey.side Y i (Y.uv k))) * projector F.H ∧
     F.chir * F.overlap+F.overlap*F.chir=(F.overlap*F.chir*F.overlap)+(F.overlap*F.chir*F.overlap)) := by
  have t : ρ a=a.1:= Vale.Grace.Robes.solar a ρ (Papal.roofage Y i m) (Y.meter.a m) ((Y.history i k).pole m) h
  have hx := (Y.equity i k a.1 h)
  refine ⟨t,?_⟩
  intro F PS
  have he : Cube.Guard a.1 Λ.d:= t ▸ (Papal.roofage Y i m).paid a
  have ht : Safe F.H := Phase.wiel_ok («m»:=Vale.mesh (Y.ir i) Λ.R.L m) (B:=Λ.block) _ Λ.U.baseY he
  refine ⟨ht,hx.1,hx.2,?_,?_,F.gw ht⟩
  · rw [Y.whole]; exact Set.indicator_of_mem (s:={U| flags p U=∅}) h _
  exact (F.overlap_action ht).trans (by rw [show F.plus=_ from Reed.plus_joint (Cube.links a.1) _])

lemma marked_diagonal (x : Cloud (Dome (tent Y H))) (v : Skye.Orbit (Journey.side Y i (Y.uv k))) :
    inner ℂ o (acts ((attire (breathing Y H m i k x)) (drawn ρ v)) (denZ G Λ.U ρ v)) = numeratorTop Y H i k x v.1 := by
  unfold numeratorTop observableTop; rw [Y.whole]
  by_cases h : flags p v.1=∅
  · rw [show drawn ρ v=(v.1,v.1) from Prod.ext rfl (top_system Y i k v h).1]
  rw [show w v.1=0 from Set.indicator_of_notMem (s:={U|flags p U=∅}) h _]; simp

lemma unmarked_top (U : Pane (Journey.side Y i (Y.uv k))) : numeratorTop Y H i k 1 U = inner ℂ o (w U) := by
  have he: observableTop Y H i k 1 U=1:= by
    unfold observableTop breathing; rw [Decking.crown1]
    exact congrFun (show attire (1 : Tapestry.Ward V) = 1 from rfl) _
  unfold numeratorTop; rw [he,act_one]

end diagonal

section measures
variable (x : Cloud (Dome (tent Y H)))
include H
lemma bare_ledger (t : (Y.voyage i).kick ≤ k) (q : x∈ shorter (Dome (tent Y H)) (Y.uv k)) :
    Integrable (numeratorTop Y H i k x) (Wilson.prior SU.group (More V)) ∧ P≠0 ∧
      taking Y H i k x=(∫ U,numeratorTop Y H i k x U∂μ)/P := by
  let f:= numeratorTop Y H i k x
  let F:= fun v : Skye.Orbit V => inner ℂ o (acts ((attire (breathing Y H m i k x)) (drawn ρ v)) (denZ G Λ.U ρ v))
  have he : F=f ∘ Prod.fst := funext (marked_diagonal Y H i k x)
  obtain ⟨h,v,g⟩ := taking_formula Y H m i k x ⟨t,le_rfl⟩ q
  change Integrable F (city V) at h; change _=(∫ a,F a∂city V)/P at g
  rw [he] at h g
  let a:= depot V; have ht: IsProbabilityMeasure a:=inferInstanceAs (IsProbabilityMeasure (depot V))
  letI := ht
  have ha : Integrable f μ := Integrable.of_comp_fst (ν:=a) h (NeZero.ne _) -- tune namespace
  exact ⟨ha,v,g.trans (congrArg (·/P) (Window.usesPrior f ha))⟩
lemma physical_partition (t : (Y.voyage i).kick ≤ k) :
    Integrable (fun U:Pane (Journey.side Y i (Y.uv k))=>inner ℂ o (w U)) μ ∧
    P= ∫ U, inner ℂ o (w U)∂μ ∧ P≠0 := by
  obtain ⟨h,v,t'⟩:= bare_ledger Y H i k 1 t ((shorter _ _).one_mem)
  rw [takingUnit _ _ i k t] at t'
  have he := (div_eq_iff v).mp t'.symm
  rw [one_mul] at he
  simp_rw [unmarked_top] at he
  exact ⟨(show _ from (funext (unmarked_top Y H i k)) ▸ h), he.symm,v⟩ -- parser grouping integral
end measures

section gauge
variable (x : Cloud (Dome (tent Y H)))
lemma diagonal_AtSupport {n : Side}{S : Lattice.Support (More n)}{x : Mark n}{b : Bool}(h : AtSupport b S x) :
    AtSupport b S (toMark (fun v=>x (v,v))) := AtSupport.fromEval _ (Env.along h.env (by fun_prop))
      (fun a c t=>h.dep (a,a) (c,c) t t) (fun v=>h.allV _)
lemma bare_support (F : BillOfWork) (t : (Y.voyage i).kick ≤ k)
    (q : x∈ fountainHeads K F m) :
    AtSupport false (Satin.region (frameBudget F Λ l m) (Journey.side Y i m)) (toMark (observableTop Y H i k x)) :=
  diagonal_AtSupport (actual_supported Y H (show Tapestry.Pay Y m i k from ⟨t,le_rfl⟩) F x q)
lemma top_covariant {A : Set RSpace} (t : (Y.voyage i).kick ≤ k) (q : x∈well Λ K l true A Set.univ) (v : x∈shorter (Dome (tent Y H)) (Y.uv k)) :
    covariant (toMark (observableTop Y H i k x)) := fun g U => paid_coherence Y H i k m ⟨t,le_rfl⟩ x q v g (U.1,U.1)
end gauge

end YM.CF.Buffered.Afterglow.Tower.Reconstruction

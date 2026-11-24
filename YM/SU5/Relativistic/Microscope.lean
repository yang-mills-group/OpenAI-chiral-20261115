import YM.SU5.Relativistic.ThroughCutoff
import YM.CF.Reed.Play
import YM.SU5.FiniteGaugeData.LocalLimit.Physical

/-!
# The actual finite-cutoff interpretation of a local measurement

No new asymptotic receipt here. Use the Terra & Con/Satin grants on the same
Course, and go through the exact step and physical-region estimates, keeping
support at fixed physical offsets EVEN at the bare level that is going to
infinity. Top read uses one link field, not an extra independent draw. Use
original overlap (including phase) and its normalization. Thus effective
mark conclusions including genuine gauge and chiral interactions can be read
as statements about observables that are measured in that physical cutoff
model, not just a formal secondary process with a budget contractor as
unnormalized oracle. This does not claim the field content/signature of a
Wightman realization.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction

open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Scree Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark Dial Push.SectorMeasure
open Journey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L" => Λ.R.L.val
variable (s : ℕ) (i k : ℕ)
local notation "T" => Y.uv k
local notation "J₀" => (Y.voyage i)
local notation "G" => (Y.voyage i).X (Y.uv k)
local notation "N₀" => Journey.side Y i (Y.uv k)
local notation "D" => (Y.voyage i).CapeT
local notation "Π" => (Y.ir i)
local notation "P" => Y.meter.a (Y.uv k)
local notation "R" => ((Y.voyage i).X (Y.uv k)).gram (Y.uv k)
local notation "cityΩ" => Scree.city (side Y i (Y.uv k))
local notation "μ" => Wilson.prior SU.group (More (side Y i (Y.uv k)))

section pricing
noncomputable abbrev vacuumKet (u : Pane (side Y i (Y.uv k))) := Vale.capP Λ.U (R).beta (Y.meter.a (Y.uv k)) u

def microscope (f : Mark (side Y i (Y.uv k))) : ℂ := ∫ u : Pane (side Y i (Y.uv k)), inner ℂ (Dial.mateK _) (acts (f (u,u)) (vacuumKet Y i k u)) ∂Wilson.prior SU.group (More (side Y i (Y.uv k)))

lemma pedestal (u : Pane (side Y i (Y.uv k))) (h : flags (P).threshold u=∅) :
    let W := Lat.frame SU.matter (Cube.links u) (Lat.anticut _)
    vacuumKet Y i k u= Complex.exp (- (( (R).beta * Vale.basicP Λ.K.top.clip u:ℝ):ℂ)) • changeM Λ.U u Vale.babyM ∧
    spar Λ.K.j Vale.babyM u= portW (Tulip.helix _).symm (projector W.H) ∧
    Sea (spar Λ.K.j Vale.babyM u) (Spire.changeM (m:=mesh (Y.ir i) Λ.R.L T) Λ.U u Vale.babyM) ∧
    Safe W.H ∧
    W.overlap * projector W.H = cutM (upperP _) * projector W.H := by
  intro W
  obtain ⟨w,v⟩:= Course.equity Y i k u h -- should Preparation.Course
  refine ⟨Set.indicator_of_mem (s:={x|flags (P).threshold x=∅}) h _,w,v,?_⟩
  let x : Orbit N₀:=(u,Classical.arbitrary _)
  have ht:= ((Y.history i k).roof T).paid
  have hx : D T x=u := Vale.Grace.Robes.solar x (D T) ht P ((Y.history i k).pole T) h
  have hy:Guard u Λ.d:= hx ▸ (ht.paid x).shrink Λ.J.hr.le
  have hr:Safe W.H:= wiel_ok (anticut N₀) Λ.U.baseY hy
  exact ⟨hr, Eq.trans (W.overlap_action hr) (by unfold W; rw [Reed.plus_joint (Cube.links u) (Lat.anticut _)])⟩

private lemma integrable_plate (f : Mark (side Y i (Y.uv k))) (h : RG.Envelope f)
    (t : (Y.voyage i).kick ≤ k) :
    Integrable (fun x=> letterRead (f (drawn (D T) x)) (denZ R Λ.U (D T) x)) cityΩ:= by
  exact mark_integrable ((Y.voyage i).ownership T).paid.bill h (Marks.can_read _ _ _ _ (Course.each_level Y i k _ t (le_refl _)))

private lemma value_one (f : Mark (side Y i (Y.uv k))) (x : Orbit (side Y i (Y.uv k))) :
    letterRead (f (drawn (D T) x)) (denZ R Λ.U (D T) x) =
      inner ℂ (Dial.mateK _) (acts (f (x.1,x.1)) (vacuumKet Y i k x.1)) := by
  rw [Y.whole]
  by_cases h : flags (P).threshold x.1=∅
  · rw [show drawn (D T) x=(x.1,x.1) from Prod.ext rfl (Vale.Grace.Robes.solar x (D T) ((Y.history i k).roof T).paid P ((Y.history i k).pole T) h)]
    rfl
  have h₀:vacuumKet Y i k x.1=0:=Set.indicator_of_notMem (s:={x | flags (P).threshold x=∅}) h _
  change letterRead _ (vacuumKet Y i k x.1)= _
  rw [h₀,map_zero,map_zero, inner_zero_right]

lemma onePrior (f : Mark (side Y i (Y.uv k))) (h : RG.Envelope f) (t : (Y.voyage i).kick ≤ k) :
    Integrable (fun x:Pane (side Y i T)=> inner ℂ (Dial.mateK _) (acts (f (x,x)) (vacuumKet Y i k x))) μ ∧
    markedRead f (D T) (denZ R Λ.U (D T))=microscope Y i k f := by
  have ht:=integrable_plate Y i k f h t
  simp_rw [value_one Y i k f] at ht
  let F(x:Pane N₀):= inner ℂ (Dial.mateK _) (acts (f (x,x)) (vacuumKet Y i k x))
  have he : Integrable (fun x:Orbit N₀=> F x.1) ((μ).prod (depot N₀)):=ht
  obtain ⟨i₀,hi⟩:= he.prod_left_ae.exists
  refine ⟨hi,?_⟩
  unfold markedRead
  change (∫ x:Orbit N₀,letterRead (f (drawn (D T) x)) (denZ R Λ.U (D T) x) ∂cityΩ)=_
  simp_rw [value_one Y i k f]
  exact (MeasureTheory.integral_prod_symm (fun x:Orbit N₀=> F x.1) he).trans (by simp only; simp; rfl) -- tune

lemma same_denominator (h : (Y.voyage i).kick ≤ k) (t : s ≤ Y.uv k) :
    partitionZ ((G).gram s) Λ.U (D s) = microscope Y i k 1 ∧ microscope Y i k 1≠0:= by
  have hx : partitionZ R Λ.U (D T) = microscope Y i k 1:= by
    rw [← (onePrior Y i k 1 (AtSupport.oneM (Finset.univ)).env h).2, markvac]; rfl
  exact ⟨((G).balance s t).trans hx, hx ▸ (Y.each_level i k (Y.uv k) h le_rfl).valid⟩

lemma topLens {S:Finset Cover} {f:Family (tent Y H)} (h : InTest (tent Y H) true S false f)
    (x : (Y.voyage i).kick ≤ k) :
    sharp Y H (Y.uv k) i k f=
     microscope Y i k (distribute Y H (Y.uv k) i f)/microscope Y i k 1:=by
  let F':= distribute Y H (Y.uv k) i f
  change Journey.compass Y i k (Y.uv k) F'= _
  unfold Journey.compass
  rw [(same_denominator Y T i k x le_rfl).1,(onePrior Y i k F' (stationed Y H _ _ _ h).env x).2]

end pricing
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.pedestal
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.topLens

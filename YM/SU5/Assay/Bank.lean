import YM.SU5.Assay.Face
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "Λ"=> P.par
local notation "σ"=>P.shifts j
local notation "β"=>ruler P.par.block
local notation "τ"=>P.tock
variable {P j x}{k:ℤ}{w t:ℕ}{a b:ℝ}{f:P.Test}
/-! The stamp face is a valid simultaneous width caliper for *every* component,
 including the separate appointment of a component under a broad rather than
 the colored receipt. -/
variable {V:Set Vantage} {S:Finset Cover}
-- As for periodRoom (Avenue) but will apply without moving regions.
lemma FrameFace.between (h:P.FrameFace j t V a b k w)(z:P.pinFoot t S ⊆ V):
  Between K j (β*k) (β*(k+w)) S:=by
 intro y p
 let r:ℤ:=reserve P.par P.width
 let d:ℝ:=precisionAt P.par t
 let n(e:ℤ):Vantage:=fun i=>markZ P.par t (y i+e)
 let u(e:ℤ):Vantage:=fun i=>n e i / 2
 have dh:0<d:=positiveScale ..
 have a(e)(v:|e|≤r): u e∈V:=by
   refine z ⟨_,p,?_⟩
   have he:(2:ℝ) • u e=n e:=by ext; simp [u]; ring
   rw [he]
   intro i; change |d*n e i - y i|≤ _
   have he:d*n e i=(y i+e:ℤ):=by unfold d n markZ; rw [mul_comm,div_mul_cancel₀ _ dh.ne']
   rw [he]; push_cast; simp only [add_sub_cancel_left]; exact_mod_cast v
 have b: 2*τ t k≤ n (-r) j:=by
   have g: τ t k≤ n (-r) j/2:=(h.buys _ (a (-r) (by rw [abs_neg,abs_of_nonneg (show 0≤r from Int.natCast_nonneg _)]))).1
   linarith only [g]
 have v: n r j≤2*τ t (k+w):=by
   have g: n r j/2≤τ t (k+w):=(h.buys _ (a r (by rw [abs_of_nonneg (show 0≤r from Int.natCast_nonneg _)]))).2
   linarith only [g]
 have he(e): 2*τ t e=markZ P.par t (β*e) := Apron.distance_mark P ..
 rw [he] at b v
 unfold n markZ at b v
 rw [div_le_div_iff_of_pos_right dh] at b v
 have g:β*k≤y j-r:=by rw [sub_eq_add_neg]; exact_mod_cast b
 exact ⟨le_sub_iff_add_le.mp g,by exact_mod_cast v⟩
lemma FrameFace.bank (h:P.FrameFace j t V a b k w)(p:P.asked_at t f V): P.BEntry j w (σ (-k) f):=by
 obtain ⟨S,p,z⟩:=p
 refine ⟨h.width,_,P.shifts_support _ _ _ p,?_⟩
 have v:=Between.relocate K j (h.between z) (-k)
 rwa [show ruler (K).B=β from rfl,mul_neg,neg_add_cancel,mul_add,←add_assoc,neg_add_cancel,zero_add] at v
/-- At every Face the pure consultations on the advertised Spent budget
are billed with the SAME caliper; no test on coincident compositions. -/
lemma FrameFace.rebate (h:P.FrameFace j t V a b k w)(r:P.Register)(q:f∈P.Spent t V)(x:P.Spectrum0 j):
 P.BEntry j w (σ (-k) f) ∧
 (P.doorBox j t w (σ (-k) f)).1.1= P.meanBox j t w (σ (-k) f) ∧ P.meanBox j t w (σ (-k) f)=0∧
 P.seenBox j x t w (σ (-k) f)=0∧P.singleState j t x f=0:=by
 let p:= Spent.clips q
 let u:= Cinder.shift p j (-k)
 have d:= Cinder.room t w r u x
 exact ⟨h.bank (Spent.in_y q),d.1,Cinder.operator t r u,d.2.1,Cinder.value t p x⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

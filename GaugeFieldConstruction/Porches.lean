import GaugeFieldConstruction.Hab
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option maxRecDepth 5700
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.style.longLine false
open Function Filter Set MeasureTheory
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace Spine
open Fock Analysis SlabMark MeshClock Vacancy Tapestry Etch
open Germ Alliance Lattice Py.Rate Py.Rate.LocalLimit Preparation Journey Satin Heat
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
noncomputable section
open SelectionAnalysis

variable {P:Spine}{cost:ℕ→P.Test→ℂ} {j:Axis} (R:Porch P cost j)
namespace Porch
lemma watch_le (A:P.Slabs j): ‖R.ρ A‖≤ ‖A‖:=NonUnitalStarAlgHom.norm_apply_le R.ρ _
include R in
lemma plot_le {s w:ℕ}{F:P.Test}(p:P.BEntry j w F):‖cost s F‖≤‖P.meanBox j s w F‖:=by
 rw [←R.expense p]
 apply (norm_inner_le_norm ..).trans
 rw[R.normΩ,one_mul]; refine ((R.ρ (P.HabBox j s w F)).le_opNorm _).trans ?_; rw [R.normΩ,mul_one,← heard_box s p]; exact R.watch_le _
local notation "M"=>timeMesh P.par
local notation "Γ"=>marks M
local notation "η"=>R.ρ
local notation "Σ" a:max=>η (P.movesOf j a)
def soloArray (a:Trans j):Lunation (timeMesh P.par) R.H where
 nav s i:= R.ρ (P.movesOf j (s,i,a))
 zero s:=by rw [show P.movesOf j (s,0,a)=1 from Subtype.ext (P.shift_zero j s a),map_one]; rfl
 sums s i k:=by
   change η _*η _=η _; rw[←map_mul]; exact congrArg η (show P.movesOf j (s,i,a)*P.movesOf j (s,k,a)=P.movesOf j (s,i+k,a) from Subtype.ext (P.shift_plus j s i k a))
 changeover s t p i:=congrArg η (show P.movesOf j (s,i,a)=P.movesOf j _ from Subtype.ext (P.slide_up j s i t p a))
 limited s i:= (R.watch_le (P.movesOf j (s,i,a))).trans (P.grow j _)
def coCrew : Alliance (Trans j) (marks (timeMesh P.par)) R.H where
 crew k:= (R.soloArray k).plays
 cCom a b p q:= by
   obtain ⟨s,u,rfl⟩:=notch_exists M p; obtain ⟨t,w,rfl⟩:=notch_exists M q
   have h:P.movesOf j (s,u,a)*P.movesOf j (t,w,b)=P.movesOf j (t,w,b)*P.movesOf j (s,u,a):=
     Subtype.ext ((ladder P.run P.large P.law P.history.circuit j 0 false (P.room j)).cCom a b (notch M s u) (notch M t w))
   change (R.soloArray _).ship _*(R.soloArray _).ship _=(R.soloArray _).ship _*(R.soloArray _).ship _
   rw [Lunation.navZ, Lunation.navZ]; change η _*η _=η _*η _; rw [← map_mul,←map_mul,h]

def canopy : Sunbelt j (marks (timeMesh P.par)) R.H where
 track:=R.coCrew
 list:=look j
 traverses i:=look_all j i -- tune
 unique_list:=look_one j
 heat:=R.Time.E
 smooth:=R.Time.continuousE
 diffusion x:=by simp_rw [R.Time.sym]; exact R.Time.continuousE x
lemma canopy_plays (i:Trans j)(s:ℕ)(k:ℤ): (R.canopy.track.crew i).play (notch (timeMesh P.par) s k)=R.ρ (P.movesOf j (s,k,i)):=
 Lunation.navZ (R.soloArray i) s k
lemma heat_share (d:Trans j)(v:marks (timeMesh P.par))(t:ℝ≥0):
   ((R.canopy.track.crew d).play v).comp (R.Time.E t)=(R.Time.E t).comp ((R.canopy.track.crew d).play v):=by
 obtain ⟨s,k,rfl⟩:= notch_exists _ v; rw [R.canopy_plays, R.heat]
 change R.ρ _ * R.ρ _= R.ρ _*R.ρ _; rw [←map_mul, ←map_mul,P.grid_member]
lemma Ω_ready (d:Trans j)(v:marks (timeMesh P.par)): (R.canopy.track.crew d).play v R.Ω=R.Ω:=by
 obtain ⟨s,k,rfl⟩:=notch_exists _ v; rw [R.canopy_plays, R.transverse]
lemma rising_mem : R.Ω ∈ R.canopy.track.aviator R.canopy.list:=by
 rw [Alliance.assembled]; intro d _; change ContinuousAt (fun a:marks M=> (R.canopy.track.crew d).play a R.Ω) 0; simp_rw [R.Ω_ready]; exact continuousAt_const

abbrev DegreeHab:= R.canopy.track.Realm R.canopy.list
/-- The real semigroup with *honest* real translation on these continuous vectors. -/
def BrightHab: OS.Semigroup (DegreeHab R) j:= glass R.canopy (daylight M) R.Time R.heat_share
abbrev groundHab : DegreeHab R:= ⟨R.Ω,R.rising_mem⟩

variable {I:Type*} (Up W:I→ marks (timeMesh P.par))(H:∀ i,0 < (W i:ℝ))
/-- pose symbol estimates independent of whether the operator was formed already
 at mesh or as a limiting member of the same Slabs algebra. `Up` is from the lower
 wall to the reference placement; includes offsets of any sign. -/
def elementals (A:I→P.Slabs j): Repertoire I j (timeMesh P.par) R.H where
 sky:= R.canopy
 sea:= R.Time
 match_time:= rfl
 glides:=R.heat_share
 rise:=Up
 width:=W
 bar:=H
 op i:= R.ρ (A i)
 light:=R.Ω
 grounded:=R.rising_mem


section turn
variable {W Up H}
local notation "Υ" g:max=> R.coCrew.raw (look j) (fun i:Trans j=> (g:P.VMark) i.val)
def porchMove (g:P.VMark):R.H.Op:=Υ g
lemma porch_zero : R.porchMove 0=1:=(R.coCrew.raw_zero _ : (R.coCrew).raw (look j) 0= _)
lemma porch_plus (a b:P.VMark):R.porchMove (a+b)= R.porchMove a*R.porchMove b:=
 R.coCrew.travelR (look j) (fun i=> a i.val) (fun i=> b i.val)
lemma porch_share (a:P.VMark)(t:ℝ≥0):R.porchMove a * R.Time.E t= R.Time.E t * R.porchMove a:=
 R.coCrew.hard _ _ (fun i _ x => R.heat_share i x t) (fun i=> a i.val)

lemma porch_ops_aux (L:List (Trans j))(s:ℕ)(v:Cover) {w:ℕ}{F:P.Test} (p:P.BEntry j w F):
 P.BEntry j w (P.cruise (spare j L) v F) ∧
 let U:=R.coCrew.raw L (fun i:Trans j=> notch M s (v i.val))
 U*η (P.HabBox j s w F)=η (P.HabBox j s w (P.cruise (spare j L) v F))*U:=by
 induction L with
 | nil=> refine ⟨p,?_⟩; dsimp only; rw [Alliance.raw_nil]; change 1 * η _= η (P.HabBox j s w F)*1; rw [one_mul,mul_one]
 | cons d L ih=>
   obtain ⟨hp,he⟩:=ih
   let v':=v d.val
   refine ⟨hp.across d v',?_⟩; dsimp only at he ⊢
   let U:=R.coCrew.raw L (fun i:Trans j=> notch M s (v i.val)); let T:=P.movesOf j (s,v',d); let F':=P.cruise (spare j L) v F
   have e: (R.coCrew.crew d).play (notch M s v')=η T:=R.canopy_plays d s _
   have W₀:P.shifts d v' F' = P.cruise (spare j (d::L)) v F:=rfl
   rw [Alliance.raw_step]; change (R.coCrew.crew d).play (notch M s v') * U * _= _ * ((R.coCrew.crew d).play (notch M s v')*U)
   change U*_=_*U at he; rw [←W₀,e,mul_assoc,he,← mul_assoc,← map_mul,HabBox_across s hp,map_mul,mul_assoc]

lemma porch_box (s:ℕ)(v:Cover){w:ℕ}{F:P.Test}(p:P.BEntry j w F):
 P.BEntry j w (P.cruise (spare j (look j)) v F) ∧
 R.porchMove (P.vtile s v)*η (P.HabBox j s w F)*R.porchMove (-(P.vtile s v))=
 η (P.HabBox j s w (P.cruise (spare j (look j)) v F)):=by
 obtain ⟨h,p⟩:=R.porch_ops_aux (look j) s v p
 dsimp only at p
 change R.porchMove (P.vtile s v)*_=_*R.porchMove (P.vtile s v) at p
 rw [p,mul_assoc, ← R.porch_plus, add_neg_cancel,R.porch_zero,mul_one]
 exact ⟨h,rfl⟩ -- tune
end turn
end Porch
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

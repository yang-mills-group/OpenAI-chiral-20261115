import ZecaFount
import ZecaSnap
import YM.SU5.Six.Aprons
import YM.SU5.Cordial.Horizon
import YM.SU5.Cordial.Spritz
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option maxRecDepth 8000

open CF.Velvet CF.Pannier.Chancel

open Aria Set
variable (P:Spine)(j:Axis)
local notation "K"=> P.calibration
local notation "w!"=> ruler P.par.block
local notation "Q"=> P.shifts j

def AnyFit (S:Finset Cover)(w:ℕ):Prop:=
 ∀j:Axis, Between K j (-w! * w) (w! * w) S
lemma large_fit (S:Finset Cover):∀ᶠ w in atTop,P.AnyFit S w:=by
 apply Filter.eventually_all.mpr; intro j
 refine (Finset.eventually_all ..).mpr fun z v=>?_
 filter_upwards [(tendsto_natCast_atTop_atTop.eventually_ge_atTop ((K).ℓ + |(z j:ℤ)|:ℤ))] with w h
 have hv:(w:ℤ)≤ w! * w:= le_mul_of_one_le_left (by positivity) (ruler_gene _)
 have v:=le_abs_self (z j)
 have t:=neg_le_abs (z j)
 rw [neg_mul]
 omega

variable {q r:ℕ}
def rougeTest (L:Parts q r): P.Test:= P.tuneK L.song
def rouge (L:Parts q r)(s w:ℕ)(v:0<w)(h:P.AnyFit L.sites w) : P.Apron where
 s:=s
 u:=fun _=>w
 pos:=fun _=>v
 F:=P.rougeTest L
 S:=L.sites
 realM:=P.celebrity L.song
 bay:=by
    have ht:=L.song.1.narrow P.calibration
    exact (Tapestry.locates ..).mpr ht.widen
 shelter:=h

local notation "u!"=>UniformSpace
def piano (s w:ℕ)(e:ℝ)(L:Parts q r): Prop:=
 ∀ (a:Axis) (x:P.Spectrum0 a),P.Cash a x s (2*w)
    (P.shifts a w (P.rougeTest L) - L.depiction • (1:P.Test)) e

structure Crayon (q r w s:ℕ) (e:ℝ):Prop where
 pos : 0<w
 fits:∀L:Parts q r,P.AnyFit L.sites w
 sell: w * P.macroStep s < e
 rate :∀L:Parts q r,P.piano s w e L

variable {X:Supplier}{v b:ℝ}{K':P.Register}(p:uniform P K' X v b)(O:P.NightCop)
include p O
lemma crayon_help {e:ℝ}(q:ℕ)(u:0<e):
 ∀ᶠ r in atTop, ∀ᶠ w in atTop, ∀ᶠ s in atTop,P.Crayon q r w s e:=by
 let y:=Real.exp 1
 have hy:0< y:=Real.exp_pos 1
 let d:= e/(2*y)
 have hd:0<d:=div_pos u (by positivity)
 have hd':2*(Real.exp 1*d)=e:=by
    change 2*(y*d)=_; unfold d; field_simp
 obtain ⟨_,_,_,_,_,_,t,_⟩:= p.1.paper
 filter_upwards [Twah.aroused q (d/4) (by positivity)] with r ht
 have h:=Filter.eventually_all.mpr
    (fun Z:Parts q r=> Filter.eventually_all.mpr
      (fun j:Axis=> Papal.crystal_law P.run P.large P.law P.history
          P.projection.clipped O j (P.room j)
            (F:=Papal.meanF Z.craft Z.depiction)
            (Z.song.sub ((Voice.one Z.sites).hushed Z.depiction))
            t p.2 p.1.nerve hd (by rw [P.par.kJ];exact ht Z)))
 filter_upwards [h,(Filter.eventually_all.mpr (fun Z:Parts q r=>P.large_fit Z.sites)),eventually_gt_atTop 0] with w v' z pos
 have t₀:=Filter.eventually_all.mpr (fun Z:Parts q r=> Filter.eventually_all.mpr (v' Z))

 have hl : Tendsto (fun s=>w * P.macroStep s) atTop (𝓝 (0:ℝ)):=by simpa using (P.macroStep_zero.const_mul (w:ℝ))
 filter_upwards [t₀,hl.eventually (gt_mem_nhds u)] with s hg hk
 refine ⟨pos,z,hk,?_⟩
 intro Z j x
 let Front:=P.rouge Z s w pos (z Z)
 obtain ⟨T,v,_⟩:=
    Front.snap_here P j x
        (show (↑(Front.u j):ℤ)≤w from le_refl _)
        (w:=2*w) (by change (w:ℤ)+ ↑w≤_; omega) rfl
        (show bell (timeMesh P.par) s (↑(2*w:ℕ))= bell (timeMesh P.par) s ↑w + bell (timeMesh P.par) s ↑w from by unfold bell; push_cast; ring)
 let f:P.Fired j x s (2*w) (P.shifts j w (P.rougeTest Z)) T:=v
 let a:= f.sub ((Fired.identity f.pos).smul Z.depiction)
 refine ⟨_, a, ?_⟩
 apply a.mean_le
 intro E p' t'
 apply le_trans _ hd'.le
 apply hg Z j
 let G:=P.rougeTest Z - Z.depiction • (1:P.Test)
 have g:P.voxTest j s E.val=P.shifts j w G:=by
   unfold G; rw [map_sub,map_smul,map_one]; exact t'
 exact congrArg (fun a:P.Test => a.val) g

#print axioms crayon_help

omit p O
structure Bean (c r m:ℕ→ℕ):Prop where
 eager:StrictMono r
 heights:StrictMono c
 births:∀i,0<r i
 clearing:∀i, Prototype.inchR P.par (c i) (r i) ≤ keyV i
 paint:∀i,P.Crayon i (r i) (m i) (c i) (keyV i)

private lemma improve (f:ℕ→ℕ):∃g,StrictMono g∧f≤g:=
 let g:ℕ→ℕ := Nat.rec (f 0) (fun i v=>max (f (i+1)) (v+1))
 ⟨g,strictMono_nat_of_lt_succ fun i=> (Nat.lt_succ_self _).trans_le (le_max_right (f (i+1)) (g i+1)),fun i=>by cases i;exact le_rfl;exact le_max_left ..⟩
include p O in
lemma bean :∃ c r m:ℕ→ℕ,P.Bean c r m:= by
 choose f g using fun i=>eventually_atTop.1 ((P.crayon_help p O i (keyV_positive i)).and (eventually_gt_atTop 0))
 obtain ⟨r,s,h⟩:=improve f
 choose m d using fun i=> (g i (r i) (h i)).1.exists
 choose l t using fun i=>eventually_atTop.1 ((d i).and (Prototype.rent_unit (P:=P) (r i) _ (keyV_positive i)))
 obtain ⟨c,b,j⟩:=improve l
 exact ⟨c,r,m,s,b,fun i=>(g i (r i) (h i)).2,fun i=>(t i (c i) (j i)).2,fun i=>(t i (c i) (j i)).1⟩
#print axioms bean

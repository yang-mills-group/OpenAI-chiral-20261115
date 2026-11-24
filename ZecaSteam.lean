import ZecaBoba
import ZecaLustre
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


variable (P:Spine)

section iri
variable {U:Hilbert} {f:ℕ→U.Op} {T:U.Op}
lemma LatticeFieldEstimates.bean_smul (h:LatticeFieldEstimates U atTop f T) {v:ℕ→ℂ}{z:ℂ}(u:Tendsto v atTop (𝓝 z)):
 LatticeFieldEstimates U atTop (fun i=>v i • f i) (z • T):=by
 have t:= (LatticeFieldEstimates.pops (u.smul_const (1:U.Op))).mul h
 rw [smul_mul_assoc,one_mul] at t
 exact t.congr' (Eventually.of_forall (fun i=> by dsimp only; rw [smul_mul_assoc,one_mul]))
end iri

variable (x:P.Spectrum0 3) (c r m:ℕ→ℕ)
 (h:P.Bean c r m)

def sipping (i:ℕ)(L:Parts i (r i)) :=
   P.rouge L (c i) (m i) (h.paint i).pos ((h.paint i).fits _)

lemma sip_step (i:ℕ)(L:Parts i (r i)) (j:Axis):
 (P.sipping c r m h i L).realWidth P j < keyV i:=by
   have k:= (h.paint i).sell
   unfold sipping rouge Apron.realWidth bell
   rw [Int.cast_natCast]
   exact k

variable (D:ℕ→P.Apron)

structure Spoon (p:ℕ→ℕ):Prop where
 new : StrictMono p
 age : ∀i,(D i).s ≤ c (p i)
 width : ∀i,keyV (p i) ≤ (D i).realWidth P 3
 rate : ∀i, ‖(D i).engine P 3 x‖ * keyV (p i) ≤ P.macroStep i

include h in
lemma stirB : ∃p,P.Spoon x c D p:=by
 choose f g using fun i=>eventually_atTop.1 ((h.heights.tendsto_atTop.eventually_ge_atTop (D i).s).and
    ((keyV_go.eventually_le_const ((D i).real_width_pos P 3)).and
      ((keyV_go.const_mul ‖(D i).engine P 3 x‖).eventually_le_const
       (by rw [mul_zero];exact P.macroStep_pos i))))
 let p:ℕ→ℕ := Nat.rec (f 0) (fun i v=>max (f (i+1)) (v+1))
 have q : f ≤ p:=fun i=>by cases i; exact le_rfl;exact le_max_left ..
 exact ⟨p,strictMono_nat_of_lt_succ fun i=> (Nat.lt_succ_self _).trans_le (le_max_right (f (i+1)) (p i+1)),
        fun i=>(g i (p i) (q i)).1,fun i=>(g i (p i) (q i)).2.1, fun i=>(g i (p i) (q i)).2.2⟩

variable (p:ℕ→ℕ)(L:∀i,Parts (p i) (r (p i)))
 (d:P.Spoon x c D p)

local notation "U" i:max=> P.sipping c r m h (p i) (L i)
def flavor (i:ℕ):=
 P.teatip (U i) (D i)
local notation "W" i:max=> P.flavor c r m h D p L i
variable (G:P.Nib 3 x) (f:P.Iguana 3 x G D)
 (v:ℂ) (t:Tendsto (fun i=>(L i).depiction) atTop (𝓝 v))
include d f
lemma flavor_thin (j:Axis)
 (q:Tendsto (fun i=> (D i).realWidth P j) atTop (𝓝 0)):
 Tendsto (fun i=> (W i).realWidth P j) atTop (𝓝 0):=by
 have e:Tendsto (fun i=> (U i).realWidth P j) atTop (𝓝 0):=
     squeeze_zero (fun i=>((U i).real_width_pos P j).le)
      (fun i=>(P.sip_step c r m h (p i) (L i) j).le)
       (keyV_go.comp d.new.tendsto_atTop)
 have e':(0:ℝ)+3*0+0=0:=by ring
 refine Tendsto.congr ?_ ((e' ▸ ((q.add (f.thin.const_mul 3)).add e)))
 exact fun i=> (P.teatip_width (U i) (D i) j (d.age i)).symm

include t
lemma flavored :
 P.Iguana 3 x (fun a b=>v • G a b) (P.flavor c r m h D p L):=by
 have y:= P.flavor_thin x c r m h D p L d G f 3 f.thin
 refine ⟨NibPay.smul _ f.pay,y,?_⟩
 intro a b h₁ h₂
 have g:= f.read h₁ h₂
    (show Tendsto (fun i=>a+(D i).realWidth P 3) atTop (𝓝 a) by simpa using (f.thin.const_add a))
    (show Tendsto (fun i=>b-(D i).realWidth P 3) atTop (𝓝 b) by simpa using (f.thin.const_sub b))
 apply (g.bean_smul t).mend P.macroStep_zero
 filter_upwards [y.eventually_le_const h₁, y.eventually_le_const h₂] with i q₁ q₂
 have he:(U i).u 3 ≤ (D i).zoom P ((U i).s) 3:=by
    have t':= (P.sip_step c r m h (p i) (L i) 3).le.trans (d.width i)
    rw [←(D i).zoom_bell P 3 (c (p i)) (d.age i)] at t'
    exact_mod_cast ((bell_le ..).1 t')
 exact (P.tapioca_pay (D i) (U i) x _
         ((h.paint (p i)).rate (L i) 3 x) he (d.age i) q₁ q₂).trans (d.rate i)
#print axioms flavored

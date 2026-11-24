import Lucent.Money
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

set_option maxHeartbeats 380000
set_option linter.unusedSimpArgs false
open YM.Stationary (Gaia)
open Onyx Kea Flare Dial Ballad.Twah Cordial Emu Gist
open Regis Circuit
variable {I:Type}(Y:I→Role)
namespace Arity

#print Lattice.stop
#print Lattice.Walk
#print Lattice.step
#print dayStars
variable (x:Cover)
abbrev gin (v:Cover):Gaia:= WithLp.toLp 2 (fun i:Axis=>(v i:ℝ)) -- coe WithLp? need toLp

def lime(x:Cover)(n:ℕ):= n • x
lemma l_pt {P:Preparation}{R:ℕ→ℝ}{r:ℕ→ℕ}(p:Velocity P R r):
 Tendsto (fun s=> riseX (r s) (lime x (r s))) atTop (𝓝 (gin x)) :=by
 apply tendsto_const_nhds.congr; intro s
 ext j; change (x j:ℝ) = ((r s • x j:ℤ):ℝ) / r s
 have y:=p.t s; rw [nsmul_eq_mul]; push_cast; field_simp
lemma face_pt {R:ℕ→ℕ}(p:Tendsto (fun s:ℕ=> (R s:ℝ)) atTop atTop) :
 Tendsto (fun s=>riseX (R s) (lime x (R s)+1)) atTop (𝓝 (gin x)):=by
 apply (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr ?_)
 intro i; let t:= (tendsto_inv_atTop_zero.comp p).const_add (x i:ℝ)
 rw [add_zero] at t; apply t.congr'
 filter_upwards [p.eventually_gt_atTop 0] with s u
 change ↑(x i)+(R s:ℝ)⁻¹= ↑((R s • x i+1:ℤ)) /(R s:ℝ)
 rw [nsmul_eq_mul];push_cast;field_simp

abbrev disp (a:ℕ): Cover := a • Lattice.step 2
lemma reach (x:Cover)(a:ℕ): stop x (List.replicate a (posDir 2))=x+disp a:=by
 induction a generalizing x with
 | zero=>simp [disp,stop]
 | succ a t=> rw [List.replicate_succ,stop,t,Step.vec_pos]; unfold disp; rw [succ_nsmul]; abel
abbrev pour (r:ℕ):ℕ:=2*r
lemma atlas_end(x:Cover)(a r:ℕ):
 stop (nodeC (lime x r)) (List.replicate (pour r*a) (posDir 2))= lime (x+disp a) (pour r)+1:=by
 rw [reach]; unfold disp lime pour nodeC; rw [smul_add,smul_smul,smul_smul]; abel

def chime (x:Cover)(a r:ℕ)(b:DirSpin): Staff where
 hub:=nodeC (lime x r)
 u:=lime x r
 face:=(lime (x+disp a) (pour r)+1,xy)
 spin:=b
 steps:=List.replicate (pour r*a) (posDir 2)
 stop_at:= atlas_end x a r
#check @pav_mono


variable {a r:ℕ} (b:DirSpin)
def girder(r:ℕ):=pour r +4

lemma chime_fee (p:a≤1): (chime x a r b).Pays (girder r) (pour r):=by
 have s: stop (nodeC (lime x r)) (chime x a r b).steps ∈ visits (nodeC (lime x r)) (chime x a r b).steps:=by
    generalize (chime x a r b).steps=t
    generalize nodeC (lime x r)=z
    induction t generalizing z with|nil=>simp [visits,stop]|cons i L h=> rw [stop,visits]; exact List.mem_cons_of_mem _ (h _)
 have v:(chime x a r b).steps.length≤pour r:=by simp only [chime,List.length_replicate]; exact (Nat.mul_le_mul_left _ p).trans (Nat.mul_one _|>.le) -- tune
 refine ⟨v,fun i u=>pav_mono (v.trans (Nat.le_add_right ..)) (walk_pav _ _ _ u),fun y t=>?_⟩
 rw [show stop (nodeC (lime x r)) (chime x a r b).steps = lime (x+disp a) (pour r)+1 from atlas_end x a r] at s -- after expose
 exact span_walk (lime (x+disp a) (pour r)+1) (nodeC (lime x r)) y (pour r) (Lattice.square xy.val.1 xy.val.2) (pav_mono v (walk_pav _ _ _ s)) (List.mem_toFinset.mp t)
def array (X:I→ Cover)(A:I→ℕ)(B:I→DirSpin) :FieldPlan I :=
 ⟨fun i=>⟨gin (X i +disp (A i)),xy⟩, fun i=>⟨gin (X i),B i⟩⟩
abbrev framing (r:ℕ→ℕ):=fun s=>(pour (r s):ℝ)

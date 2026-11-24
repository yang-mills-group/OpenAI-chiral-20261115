import Lucent.Pixel
import Lucent.Chorus
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

variable (P:Preparation){r:ℕ→ℕ}
variable (T:Velocity P (framing r) r)(X:I→ Cover)(A:I→ℕ)(B:I→DirSpin)
def spell (X:I→ Cover)(A:I→ℕ)(B:I→DirSpin)(r:ℕ→ℕ):= fun s i=>chime (X i) (A i) (r s) (B i)
def arch(r:ℕ→ℕ):=girder ∘ r
include T
lemma measureSpell [Fintype I]: MeasureAt (array X A B) (spell X A B r) (framing r) r where
 hear i:=⟨Eventually.of_forall fun _=>rfl,face_pt _ T.gauge⟩
 see i:=l_pt _ T
 feel _ _:=rfl
 touch i j h:= by
   have g:X i=X j:=by funext a; exact_mod_cast (show ((X i a):ℝ)=X j a from congrArg (fun p:Gaia=>p a) h)
   exact Eventually.of_forall fun s=> congrArg (fun x=>lime x (r s)) g

omit T in
lemma hubBand (x:Cover){H:ℝ}(h:∀j, |(x j:ℝ)| ≤ H)(t:ℕ)(j:Axis):
    |↑(nodeC (lime x t) j)| ≤ (pour t:ℝ)*H+1:=by
 change |(↑(2 • t • (x j:ℤ) + (1:ℤ)):ℝ)|≤_
 rw [smul_smul,nsmul_eq_mul]; unfold pour; push_cast
 refine (abs_add_le ..).trans ?_
 rw [abs_mul,abs_of_nonneg (show 0≤2*(t:ℝ) by positivity),abs_one]; gcongr; exact h _

lemma chargeSpell {H:ℝ}(p:0≤H)(q:∀ i j,|(↑(X i j):ℝ)|≤H)(e:∀i,A i≤1):
    DanceCost (2+H) (framing r) (spell X A B r) (arch r) (pour ∘ r):=by
 filter_upwards [T.gauge.eventually_ge_atTop 4] with s t
 refine ⟨fun _=>(show day xy from ⟨by decide,by decide⟩), le_mul_of_one_le_left (by linarith) (by linarith), ?_,fun i=>chime_fee _ _ (e i),?_⟩
 · change ((pour (r s)+4:ℕ):ℝ)≤_; rw [Nat.cast_add]; norm_num only [Nat.cast_ofNat]; have v:= mul_nonneg p (T.p s).le; unfold framing at *;linarith
 intro i j; refine (hubBand _ (q i) _ _).trans ?_
 unfold framing at *; linarith

omit T
open Pannier.Chancel Vale Jewel
def bar (P:Preparation):ℕ:= 4*P.block.val
def mosaic(P:Preparation)(a:ℝ)(s:ℕ):= bar P *zoomR P a s

lemma barPos : 0<bar P:=by unfold bar;positivity
lemma fit {a:ℝ}(p:0<a):Velocity P (framing (mosaic P a)) (mosaic P a):=by
 have V:=Velocity.normal P p
 have u:0<(bar P:ℝ):=by exact_mod_cast barPos P
 have w(s):0<(mosaic P a s:ℝ):=by unfold mosaic;rw [Nat.cast_mul];exact mul_pos u (V.t s)
 have e: Tendsto (fun n=>(mosaic P a n:ℝ)) atTop atTop:= (V.matter.const_mul_atTop u).congr fun s=> (Nat.cast_mul ..).symm
 refine ⟨?_,e,?_,fun s=>?_,w,?_⟩
 · apply (e.const_mul_atTop (show (0:ℝ)<2 by norm_num)).congr; intro s; simp [framing,pour]
 · apply tendsto_const_nhds.congr; intro s; unfold framing pour; push_cast; rw [mul_div_cancel_right₀ _ (w s).ne']
 · unfold framing pour; have :=w s; push_cast; exact mul_pos (by norm_num) this
 obtain ⟨A,q,l⟩:= V.bill (2*(bar P:ℝ)) 0
 refine ⟨A,q,?_⟩; filter_upwards [l,V.sky] with s g h
 unfold framing pour mosaic; push_cast; rw [←mul_assoc]; rw [add_zero] at g; exact le_trans (by gcongr;exact h.1) g

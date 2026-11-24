import YM.SU5.LitCurrent.Light
import YM.SU5.LitCurrent.ReflectLeg
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N
open Buffered Salt
-- Circ on Pane too: note one mesh q, areal. shared mask for tax (inc bar subtraction)
-- and for each chir ingredient.
variable {P T:SOp N} {p:BudgetPoint}{K:Scree.Loom N}{t u:ℝ}{k q:ℕ}
variable (K:Scree.Loom N)(p:BudgetPoint)(k:ℕ)(w:ℝ)(x:Site N)(E:Pattern P T r d a v)
local notation "S"=>offsetMask p.B x
noncomputable def taxHat : Pane N→Op I:=live K p k x (E.A x)
noncomputable def carrierHat (e:FaceDir): Pane N→ Op I:=live K p k x (E.J (x,e))
local notation "Â"=>taxHat K p k x E
local notation "J"=> carrierHat K p k x E
local notation "Λ"=> (tickA N)
def gaugeSeed : Mark N:=fun V=> Matrix.trace (Â V.1) • 1
def currentSeed (e:FaceDir): Mark N:=fun V=> preHalf w Λ (J e V.1)
/-- Use w=0 for (127)-(128), w=1/2 for the reflection-centered variant. Here
before applying the front length/charge scale only. Sigma over ± aids orientation. -/
noncomputable def physicalSeed : Mark N:= gaugeSeed K p k x E+ ∑ e:FaceDir,currentSeed K p k w (destSite x r e) E e
noncomputable def excess (p:BudgetPoint)(x:Site N)(r:ℕ): Mark N:= fun V => if pingS p.threshold (offsetMask p.B x) V.1 then
    dg (roomW x r)- Matrix.trace ((tickA N)*roomW x r) • 1 else 0
def fatSeed (e:FaceDir): Mark N:=fun V=> liftHalf w (J e V.1)
noncomputable def surrogate : Mark N:= gaugeSeed K p k x E+ ∑ e:FaceDir,fatSeed K p k w (destSite x r e) E e -excess p x r
-- Precise footprint in gauge seats. Fock modes even smaller. X,s,i kept across all uses
abbrev tendril (p:BudgetPoint)(r:ℕ)(x:Site N):Sa N:= inspectFoot p x ∪ (univ:Finset FaceDir).biUnion (fun e=> inspectFoot p (destSite x r e))
private lemma seed_dg (w:ℝ)(A:Op I): Continuous (preHalf w A):=by
 have he: Continuous (Fock.dg (n:=I)):=by unfold dg dyad; refine continuous_finsetSum _ fun i _=>?_ ; refine continuous_finsetSum _ fun j _=>?_ ; exact (continuous_id.matrix_elem i j).smul continuous_const
 unfold preHalf preJ; exact ((((continuous_const.mul continuous_id).matrix_trace).smul continuous_const).add (he.comp ((continuous_const.mul continuous_id).mul continuous_const))).sub ((continuous_const (y:=(w:ℂ))).smul ((continuous_id.matrix_trace).smul (continuous_const (y:=(1:FC I)))))
variable (z:Checked p K t d a k q)
local notation "HΩ"=>tendril p r x
local notation "MΩ"=>modesIn N HΩ
local notation "Y"=>physicalSeed K p k w x E
local notation "Ξ"=>surrogate K p k w x E
include z
lemma gauge_support : AtSupport false (inspectFoot p x) (gaugeSeed K p k x E) := by
 let f:Pane N→ FC I:= fun U=>Matrix.trace (Â U) • 1
 change AtSupport false _ (toMark f); refine AtSupport.fromEval f (Girt.pole_w Â _ (continuous_id.matrix_trace.smul continuous_const) (enve_pass x _ z (E.moorA x))) (fun U V u=> congrArg (fun z:Op I=> Matrix.trace z • (1:FC I)) (live_local x _ z (E.moorA _) U V u)) (fun U=> Reed.Fine.one.scale _)
lemma current_support (e:FaceDir) : AtSupport false (inspectFoot p x) (currentSeed K p k w x E e):=by
 let f:Pane N→ FC I:= fun V=> preHalf w Λ (J e V)
 have ht:= show moored (node x) _ from E.moorJ (x,e)
 refine AtSupport.fromEval f (Girt.pole_w (J e) (preHalf w Λ) (seed_dg ..) (enve_pass x _ z ht)) (fun U V h=>congrArg (preHalf w Λ) (live_local x _ z ht _ _ h)) ?_
 intro U; unfold f preHalf; rw [touchP,sub_eq_add_neg]
 exact Reed.Fine.add (Window.fine_enlarge (modes_monotone (halo_foot p x)) (inSector (J e U) (Tset N) _ (modes_pass x _ z ht (U,Classical.arbitrary (Ids N))))) (Buffered.fine_neg ((Reed.Fine.one.scale _).scale _))
lemma physical_support : AtSupport false (tendril p r x) Y:=by
 let Z:= fun e=>currentSeed K p k w (destSite x r e) E e
 have ht(e:FaceDir):inspectFoot p (destSite x r e) ⊆ tendril p r x := fun i hi=> mem_union_right _ (mem_biUnion.mpr ⟨e,mem_univ _,hi⟩)
 apply (gauge_support K p k x E z|>.mono subset_union_left).addM
 change AtSupport false HΩ (∑ e,Z e)
 suffices h:∀ T:Finset FaceDir, AtSupport false HΩ (∑ e∈T,Z e) from h _
 intro A; induction A using Finset.induction_on with
 |empty=> rw [sum_empty]; exact AtSupport.zeroM
 |insert i A v ih=>rw [sum_insert v]; exact ((current_support K p k w _ E z i).mono (ht i)).addM ih
lemma gauge_moves : covariant (gaugeSeed K p k x E):=by
 intro i g; change Matrix.trace (live K p k x (E.A x) (gauge i g.1)) • 1= twist _ (Matrix.trace (Â g.1) • 1); rw [glyphMove x (E.A x) z (E.moorA x), trace_twist,twist_scalar,map_one]; rfl
lemma current_moves (e:FaceDir) : covariant (currentSeed K p k w x E e):=by
 intro g U; let t:=tradew N g
 change preHalf w Λ (J e (gauge g U.1))= twist (quantU t) (preHalf w Λ (J e U.1)); let Y':= J e U.1
 have hp:=glyphMove x _ z (show moored (node x) _ from E.moorJ (x,e)) U.1 g
 rw [show J e (gauge g U.1)=twist t Y' from hp]
 change preHalf _ _ _= twist _ (preHalf w Λ Y')
 unfold preHalf preJ; rw [map_sub,map_add, twist_scalar,twist_scalar,twist_scalar,map_one,dg_cov,map_mul,map_mul,Cascade.tick_g, map_sub,map_one,Cascade.tick_g, trace_twist, ←show twist t (Λ*Y')= _ from (show twist t (Λ*Y')=Λ*twist t Y' from (by rw [map_mul,Cascade.tick_g])) ,trace_twist]
lemma physical_moves : covariant Y:=by
 intro g U; simp only [physicalSeed,Pi.add_apply,map_add,gauge_moves K p k x E z g U,Finset.sum_apply,map_sum,current_moves K p k w _ E z _ g U]

omit z in
lemma centered_bra (V: Fields N) : acts (star (Y V)) (mateK N)=acts (star (Ξ V)) (mateK N):=by
 let A:=mateK N; have he: IsStarProjection Λ:=touchP N ▸ cutM_idp _
 have hp : acts (star (excess p x r V)) A=0:=by
    unfold excess; split
    · rw [star_sub, star_smul,star_one,act_sub,act_smul,act_one,sandwichV (roomW x r) he (rooms_pay x r) (mateK N) (tickB N),sub_self]
    rw [star_zero,act_zero]
 simp only [physicalSeed,surrogate,Pi.sub_apply,Pi.add_apply,star_sub,star_add,act_sub,act_add,Finset.sum_apply,star_sum,act_sum]
 change _=_-acts (star (excess p x r V)) A; rw [hp,sub_zero]; apply congrArg₂ (·+·) rfl; apply sum_congr rfl; intro e _
 unfold currentSeed fatSeed preHalf liftHalf; simp only [star_sub,act_sub]; rw [bra_eq _ he _ (tickB N)]
-- better actual spelling
omit z in
private lemma preHalf_neg (A:Op I): preHalf w Λ (-A)= -preHalf w Λ A:=by unfold preHalf preJ; simp only [mul_neg, neg_mul,Matrix.trace_neg,dg_neg,neg_smul,smul_neg]; abel
lemma currentSeed_anti (y:Fields N)(e:FaceDir): currentSeed K p k w x E (axisFlip e) y= -currentSeed K p k w x E e y:=by
 let U:Orbit N:=(y.1,Classical.arbitrary _); unfold currentSeed carrierHat; rw [show live K p k x _ _=_ from E.cabaret z x e U, preHalf_neg]; -- tune method
lemma physical_spelling (V:Fields N): Y V= (gaugeSeed K p k x E) V+ ∑ i:Axis,((currentSeed K p k w (x+r • step i) E (i,false) V)-(currentSeed K p k w (x-r • step i) E (i,false) V)):=by
 unfold physicalSeed; rw [Pi.add_apply,Finset.sum_apply, Fintype.sum_prod_type]; refine congrArg _ (sum_congr rfl fun i _=> ?_); rw [Fintype.sum_bool, show (i,true)=axisFlip (i,false) from rfl,currentSeed_anti K p k w _ E z V]; simp [sub_eq_add_neg,destSite,strideD,Step.vec,axisFlip]; abel
omit z
lemma literal_current (x:Site N)(e:FaceDir)(V:Fields N):currentSeed K p k 0 x E e V=preJ Λ (carrierHat K p k x E e V.1):=by unfold currentSeed preHalf; rw [Complex.ofReal_zero,zero_smul,sub_zero]
lemma words_fit (l:ℕ)(h:p.B+2*r+12 ≤ l*p.B): HΩ ⊆ grooveB l p (node x):=by
 intro i hi; have he(y:Site N)(t:separation x y ≤ r)(g:i∈ inspectFoot p y): i ∈ grooveB l p (node x):=by
    have ht:= Yaw.touchK _ g
    obtain ⟨c,b,v⟩:=halo_spec.mp ht; obtain ⟨j,m,n⟩:=halo_spec.mp b
    rw [mem_singleton.mp m] at n; refine halo_spec.mpr ⟨node x,mem_singleton_self _, Nat.le_trans (separation_triangle _ (node y) _) ?_⟩; rw [Hove.ζdist]; exact Nat.le_trans (Nat.add_le_add_left (separation_triangle _ c _) _) (by omega)
 rcases mem_union.mp hi with u|u; · exact he x (by simp) u
 obtain ⟨⟨v,b⟩,e,t⟩:=mem_biUnion.mp u
 apply he _ _ t; cases b; exact (stopBeam x v r).1; simpa [destSite,strideD,Step.vec,Swell.gapPlus,sub_eq_add_neg] using (stopBeam x v r).2

end YM.CF.LitCurrent

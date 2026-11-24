import YM.CF.BProof.Prox.Route
import YM.CF.BProof.Gauss.High

/- Hessian has finite range, local arguments, identity on ALL severe coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gauss
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Roll Precision RealM
open Prox (Base Scope gridBase Pup)
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
local notation "G" => SU.group
variable {s: Side}(Y:Yard s)(T:PathData G)(M:ℕ)(c:Clip)(θ:ℝ)

def base (Y:Yard s): Prox.Base Y.Col := (gridBase (fun _:TAxis=>s)).layer Y.Index -- name conflict base

def edge : (Gauss.base Y).Index (Stamp Y) := (Gauss.base Y).ports (Place Y)
lemma charge_near (x y:Y.Col)(k:ℕ): (Gauss.base Y).N x y k ↔ close Y x y k:=Iff.rfl
lemma roof_eq : (edge Y).roof= Y.short*3*SU.group.lieDim:= by change Fintype.card (Place Y)=_; simp [Place,Apt,Color,TAxis]
lemma sterile (l:Tile s)(H:Room Y M)(h:Stove Y M l)(i:Stamp Y)(g:¬ Needs Y M l i.1): stepMap Y T M l (Pi.single i 1)=0:=by
 rw [← show stepMap Y T M l 0=0 from map_zero _]; refine cave_dep Y M l H _ h T _ (fun d u=>?_) -- `rw` rewrites? order
 refine PiLp.ext fun n=> ?_; have e:(d.1,d.2,n) ≠ i:= fun p=>g ((congrArg Prod.fst p) ▸ u); exact Pi.single_eq_of_ne e _ -- tune

lemma extraP (k:ℕ): Prox.Via (edge Y) (Scope.flags _) (extra Y) k:=by
 let B:=Gauss.base Y; constructor
 · intro i j S h; have he:i≠j:=fun e=>h (e ▸ (B.start j.1 k)); unfold extra; simp [he]
 intro i S W h j; unfold extra; simp only [Matrix.diagonal_apply]; by_cases v:i=j; subst j; simp only [h i.1 (B.resides _ k)]; simp [v]

lemma hostP (H:Room Y M): Prox.Via (edge Y) (Scope.flags _) (host Y T M c θ) (6*M):=by
 let B:=Gauss.base Y
 let F(l:Tile s)(S:Finset Y.Col): Pool (Stamp Y):= if l∈good Y M S then gram (stepMap Y T M l) (unit c θ l) else 0
 have u (l:Tile s): Prox.Via (edge Y) (Scope.flags _) (F l) (6*M):=by
   have hz(i:Stamp Y)(x:Finset Y.Col)(h:l∈good Y M x) : ¬ Needs Y M l i.1→ stepMap Y T M l (Pi.single i 1)=0:= fun q=> sterile Y T M l H ((mem_filter.mp h).2.1) i q
   have hl (x y:Y.Col) (p:Needs Y M l x)(q:Needs Y M l y): B.N x y (6*M):= (show 3*M+3*M=6*M from by omega) ▸ B.triangle (r:=3*M) (u:=3*M) (B.symm (show B.N _ _ _ from charge_close Y M l p)) (charge_close Y M l q)
   have hb(i j:Stamp Y)(h: ¬ Needs Y M l i.1)(S:Finset Y.Col) : F l S i j=0:=by unfold F; split; rename_i g; simp only [RealM.gram,of_apply,hz i S g h,inner_zero_left,mul_zero]; exact rfl
   constructor
   · intro i j S h; by_cases v:Needs Y M l i.1; swap; · exact hb i j v S
     have hx: ¬ Needs Y M l j.1:=fun g=> h (hl _ _ v g); unfold F; split; rename_i k; simp only [RealM.gram,of_apply,hz j S k hx,inner_zero_right,mul_zero]; exact rfl
   intro i X Y' h j; by_cases v:Needs Y M l i.1; swap; · rw [hb i j v X,hb i j v Y']
   have hg: l∈good Y M X ↔ l∈good Y M Y':=by
     simp only [good,mem_filter,mem_univ,true_and]; unfold Cave; exact and_congr_right fun hx=> forall_congr' fun g=>imp_congr_right (fun u=>(h g ((B.ball_m ..).2 (hl _ _ v u))).not)
   unfold F; rw [if_congr hg rfl rfl] -- tune
 have ht : host Y T M c θ= extra Y+∑ l:Tile s,F l:=by
   ext1 x; simp only [host,Pi.add_apply,Finset.sum_apply,F,← sum_filter]; congr; simp
 rw [ht]; exact (extraP Y (6*M)).add (Prox.Via.sum _ _ (fun i h=>u i))
-- identity on severe rows
variable (S: Finset Y.Col)
lemma host_row (i j: Stamp Y)(H: Room Y M)(h:i.1∈ S): host Y T M c θ S i j= (1: Pool (Stamp Y)) i j:= by
 simp only [host,Matrix.add_apply,Matrix.sum_apply] -- tune
 have he(l)(u:l∈ good Y M S) : RealM.gram (stepMap Y T M l) (unit c θ l) i j=0:=by simp only [RealM.gram,of_apply,sterile Y T M l H ((mem_filter.mp u).2.1) i (fun q=> (mem_filter.mp u).2.2 _ q h),inner_zero_left,mul_zero] -- tune
 rw [sum_eq_zero he]; simp [extra,Matrix.diagonal_apply,h,Matrix.one_apply]
end YM.CF.BProof.Gauss

import YM.SU5.Registration.Postcards.Pilgrim
import YM.SU5.Registration.LineUp.Diversion
import YM.SU5.Registration.Ink.Potential

/-!
 # Euclidean crossing (116) by finite averages escaping to infinity.
 
 Enough in this version to run many usual *Eu boost-plane* tests. No full-cone estimate
 used in the cluster pricing, in E or in M! (Need equality of unconditioned point-moment at the indicated
 tests as structural angular estimate.) Our method uses real-angle co-rotation even
 in the payments evaluating (116). Works with REAL displacements large even in every axis,
 need not supply time-ground projector equality to joint projection of unconditioned.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.Passage
open Boundary Mink Analysis Function Set Filter OS.Semigroup
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal
open CF.Buffered.Afterglow.Tower.VacuumSelection
open CF.Buffered.Afterglow.Hierarchy.Seld
open CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Carton
variable {H : Hilbert} (S : OS.Semigroup H timeAxis)
open ContinuousLinearMap MeasureTheory Small
variable {S} {V : Type*}[AddCommGroup V][Module ℂ V] (B:Carton S V){n m:ℕ}
-- use Postcards/ bridge with temporal fare subtracting before pricing
noncomputable def pitStop (S:OS.Semigroup H timeAxis)(p:ℝ≥0)(x y:E4) : H.Op:= postcard S (y-x-((p+p:ℝ≥0):ℝ) • basis timeAxis)
lemma pit_clock (p:ℝ≥0)(x y:E4): YM.time (y-x-((p+p:ℝ≥0):ℝ) • basis timeAxis)= YM.time y-YM.time x-(p+p:ℝ≥0):=by simp [sub_eq_add_neg]
-- use own proof to avoid fusing repr. need heat commute
lemma pit_shift (p:ℝ≥0)(x y:E4) : pitStop S p x y = M S (position (spatial y-spatial x) 0)* S.E (YM.time y-YM.time x-↑(p+p)).toNNReal:=by
 unfold pitStop postcard; rw [pit_clock]; congr 2; apply Mink.ext_by <;> simp [sub_eq_add_neg,OS.Semigroup.SEP]; try (unfold YM.time; ring)
lemma pit_add (p:ℝ≥0) (x y:E4)(h:4*(p:ℝ)<YM.time y - YM.time x)(u:E4)(g:0≤YM.time u): pitStop S p x (y+u)= pitStop S p x y * postcard S u:=by
 unfold pitStop; rw [show y+u-x-(((p+p:ℝ≥0):ℝ) • basis timeAxis)= (y-x-(((p+p:ℝ≥0):ℝ) • basis timeAxis))+u from (by abel)]; refine card_journey _ _ _ ?_ g; rw [pit_clock,NNReal.coe_add]; linarith [p.coe_nonneg]
lemma pit_translate (p:ℝ≥0)(x y u:E4):pitStop S p (u+x) (u+y)=pitStop S p x y:= by rw [pitStop,pitStop,add_sub_add_left_eq_sub]
lemma pit_hot (p:ℝ≥0)(x y:E4): pitStop S p x y B.omega=B.omega:=by unfold pitStop postcard; let r:=y-x-((p+p:ℝ≥0):ℝ) • basis timeAxis; change M S _ (S.E _ _)=_; rw [B.hot]; exact B.stay _
-- geometric mirror obs
abbrev mirror (x:E4):= Ortho.move (Signed.reflect timeAxis) x
@[simp] lemma mirror_time (x:E4): YM.time (mirror x)= - YM.time x:=by simp [YM.time,mirror,Signed.mirrored] -- plane signs
@[simp] lemma mirror_space (x:E4): spatial (mirror x)= spatial x:=by
 apply PiLp.ext; intro j; change mirror x j.castSucc=x j.castSucc; simp [mirror,Signed.mirrored,Fin.castSucc_ne_last]
lemma pit_star (p:ℝ≥0)(x y:E4): star (pitStop S p x y) = pitStop S p (mirror y) (mirror x):=by
 rw [pit_shift,pit_shift,star_mul,tstar,show (star (S.E _))=S.E _ from S.sym _, mirror_time,mirror_time,mirror_space,mirror_space,show -YM.time x- -YM.time y= _ from neg_sub_neg .., show -position (spatial y-spatial x) 0=position (spatial x-spatial y) 0 from ext_by (by simp) (by simp)] -- tune
 exact (SatinRegistration.heat_commutes ..).eq
variable (p:ℝ≥0)
-- Eu non-coincident. tie appointment
abbrev TrainJ (V:Type*):= V × E4
abbrev moveCaps (L:List (TrainJ V))(d:E4):List (TrainJ V):= L.map fun y=>(y.1,y.2+d)
noncomputable def caps (L:List (TrainJ V)) : H.Op:= Film (fun x:TrainJ V=> B.bar p x.1) (fun x y=> pitStop S p x.2 y.2) L
lemma cap_stationary (L:List (TrainJ V))(d:E4): caps B p (moveCaps L d)=caps B p L:=by
 unfold moveCaps caps; rw [Film_map]; congr 1; funext i j; rw [add_comm i.2, add_comm j.2, pit_translate]
private lemma rolling {R:Type} (T:Type*)[Monoid R] (A:T→R)(X:T→T→R)(t l:List T)(a b:T): Film A X ((t++[a])++b::l)=Film A X (t++[a])*X a b*Film A X (b::l):=by
    induction t with
    | nil=> rw [List.nil_append,solitary, show [a]++b::l=a::b::l from rfl,Film_step,mul_assoc]; rfl
    | cons i t h=>
       cases t with
       | nil=>
          change A i*(X i a*Film A X (([]++[a])++b::l))=(A i*(X i a*Film A X ([]++[a]))) * X a b* _; rw [h]; simp only [mul_assoc]
       | cons k t=>
          change A i * (X i k * Film A X (((k::t)++[a])++b::l))=(A i*(X i k*Film A X ((k::t)++[a]))) *X a b * _; rw [h]; simp only [mul_assoc]
lemma cap_append (t l:List (TrainJ V))(a b:TrainJ V): caps B p ((t ++ [a])++ b::l)=caps B p (t++[a]) * (pitStop S p a.2 b.2)* caps B p (b::l):=by
 exact rolling (TrainJ V) (fun i:TrainJ V=> B.bar p i.1) (fun i j=> pitStop S p i.2 j.2) t l a b
@[simp] lemma cap_one (i:TrainJ V): caps B p [i]=B.bar p i.1:=solitary ..
abbrev halfShot (J:JMap V)(i:TrainJ V):TrainJ V:=(J i.1, mirror i.2)
abbrev turnSpec (J:JMap V)(L:List (TrainJ V)):= L.reverse.map (halfShot J)
variable {B}
lemma cap_mirror (J:JMap V)(u:Remembers B J)(L:List (TrainJ V)): star (caps B p L)=caps B p (turnSpec J L):=by
 induction L with
 | nil=> exact (show star (1:H.Op)= _ from star_one _)
 | cons a l h=>
    simp only [turnSpec,List.reverse_cons,List.map_append,List.map_cons,List.map_nil]; cases l with
    | nil=> rw [List.reverse_nil,List.map_nil,List.nil_append,cap_one, cap_one]; exact (u.bill p a.1).symm -- field name
    | cons b l=>
       simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil]; rw [cap_append]; change star (B.bar p a.1*(pitStop S p a.2 b.2*caps B p (b::l)))= _*_ * _; rw [star_mul,star_mul,h,pit_star,cap_one]; simp only [turnSpec,List.reverse_cons,List.map_append,List.map_cons,List.map_nil]; congr 1; exact (u.bill p a.1).symm -- maybe assoc
-- connect to geometry
abbrev slots (q:Points n)(v:Fin n→V):List (TrainJ V):= List.ofFn (fun i=>(v i,q i))
/-- budget small width p & all position ink, no rotation estimate. -/
lemma cap_matrix {F:InkWaves V}(P:B.Defined F)(q:Points n)(v:Fin n→V)(t: enough (lineK q) p): F.entrance q v = inner ℂ B.omega (caps B p (slots q v) B.omega):=by
 let z:= fun i=>(↑(lineK q i):ℂ)* Complex.I; let x:= Boundary.trace q; have he:lit z p:=by change enough _ p; simpa [z,lineK,Function.comp_def] using t -- enough
 unfold InkWaves.entrance; rw [P n _ (Work.C03.lit_strict he) p he,B.matrix_film,caps, slots,List.ofFn_eq_map,Film_map]; let g(i j: Fin n):= ripZ S (z j-z i) (p+p) (x j-x i)
 change inner ℂ B.omega (Film (fun i=> B.bar p (v i)) g (Each n) B.omega)= _; congr 2;
 -- adapt Railing private
 have h(g g':Fin n→Fin n→H.Op)(L:List (Fin n))(h:∀ i j,i<j→ g i j=g' i j)(t:L.Pairwise (·<·)): Film (fun i:Fin n=>B.bar p (v i)) g L=Film (fun i=>B.bar p (v i)) g' L:=by
    induction L with
    | nil=>rfl
    | cons i l ih=> rw [Film_step,Film_step, ih t.of_cons]; congr 2; cases l with
                                                                            | nil=> rfl
                                                                            | cons j l=> exact h i j ((List.pairwise_cons.mp t).1 j (.head ..))
 refine h g (fun i j=> pitStop S p (q i) (q j)) (Each n) ?_ (List.pairwise_lt_finRange n)
 intro i j k; let p':=points (fun i:Fin n=> YM.position (spatial (q i)) 0); let y:= lineK q; have hS: Boundary.trace p'=x:=by ext1 a; simp [p',x,Boundary.trace]
 have hx:Boundary.shift p' y=z:=by ext1 a; simp [p',y,z,Boundary.shift];
 let N:=ripZ_gap (S:=S) p y p' i j (by push_cast; unfold y; linarith [t.2.2 i j k,p.coe_nonneg]); rw [hx,hS] at N; rw [show g i j=_ from N,pit_shift,(SatinRegistration.heat_commutes ..).eq, show p' j-p' i=YM.position (spatial (q j)-spatial (q i)) 0 from ext_by (by simp [p', sub_eq_add_neg]) (by simp [p', sub_eq_add_neg])]; rfl
end YM.SatinWFixed.Passage
open YM.SatinWFixed.Passage
#print axioms caps
#print axioms pit_star
#print axioms cap_matrix
#print axioms cap_mirror

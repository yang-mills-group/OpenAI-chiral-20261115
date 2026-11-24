import YM.CF.Stilo.Harper
import YM.CF.Scree.Locus
set_option autoImplicit false
noncomputable section
/-! Parent-incidence book for CAR/Wick. Each hyperlocation registers a full clique,
not assuming geometric connectedness inside that set. -/
namespace YM.CF.Stilo
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {A:Type*}[SemilatticeSup A][OrderBot A][Fintype A][DecidableEq A]
abbrev Track(A X:Type*):= A→X
def over (a b:A) := a≤b
def deckX(a:A):Finset A:= Finset.univ.filter (fun i=>over i a)
lemma deckH(a b:A):b∈deckX a ↔ b≤a:=mem_filter.trans (and_iff_right (mem_univ _))
variable {R E :Type*}[CommRing R][Ring E][Algebra R E]
-- joins; `ring` independent Module
section
variable {Q S:Type*}[AddCommMonoid Q][AddCommMonoid S]
def view (a:A) (f:A→Q): Q:= ∑ i∈ deckX a,f i
lemma singleV (a b:A)(x:Q):view a (Pi.single b x)= if b≤a then x else 0:=by
 unfold view; by_cases h:b ≤ a; · rw [if_pos h]; apply sum_eq_single_of_mem b ((deckH ..).mpr h) (fun k m v=>Pi.single_eq_of_ne v _) |>.trans; exact Pi.single_eq_same ..
 rw [if_neg h]; exact sum_eq_zero fun i hi=> by rw [Pi.single_eq_of_ne (show i≠ b from fun v=> h (v ▸ (deckH ..).mp hi))]
lemma view_add(a:A)(f g:A→Q):view a (f+g)=view a f +view a g:=sum_add_distrib
lemma view_zero(a:A):view a (0:A→Q)=0:=sum_eq_zero fun _ _=>rfl
lemma viewH (a:A) (f:A→S)(h: S→+Q): view a (h ∘ f)=h (view a f):=(map_sum ..).symm
def vAdd(a:A):(A→Q) →+ Q:={ toFun:=view a, map_zero':=view_zero a,map_add':=view_add a }
lemma map_List(a:A)(L:List (A→Q)):view a L.sum=(L.map (view a)).sum:=map_list_sum (vAdd a) _
def coal (F:Track A Q)(G:Track A Q)(T:Q→Q→S):Track A S :=∑ i:A,∑ j:A,Pi.single (i⊔j) (T (F i) (G j))
lemma focuses(a:A)(F G:Track A Q)(T:Q→Q→S)(h:∀ x:Q,∃ t: Q→+S, T x=t)(p:∀ x:Q,∃ t:Q→+S,(fun y=> T y x)=t):view a (coal F G T)= T (view a F) (view a G):=by
 unfold coal; rw [show view a = (⇑(vAdd (Q:=S) a)) from rfl] -- abbrev wrong
 simp_rw [map_sum, show ∀ x:A→S, (vAdd a) x=view a x from fun _=>rfl,singleV,sup_le_iff]
 suffices L : view a (fun i=> T (F i) (view a G))=T (view a F) (view a G) by
    rw [← L]; unfold view deckX; rw [sum_filter]; apply sum_congr rfl; intro i _; by_cases f:i ≤ a
    · simp only [f, true_and,over,if_true]; obtain ⟨t,x⟩:= h (F i); rw [x, map_sum, sum_filter]
    simp [over,f]
 obtain ⟨t,x⟩:=p (view a G); exact Eq.trans (congrArg (view a) (show (fun i=> T (F i) (view a G))= t ∘ F from funext fun i=>congrFun x (F i))) ((viewH _ _ _).trans (congrFun x _).symm)
end
lemma proves{f g:A→E} {H:A}(h:∀ i,i ≤ H→view i f=view i g): f H=g H:=by
 induction H using WellFoundedLT.induction with
 | ind H ih=>
    have he: H ∈ deckX H:= (deckH ..).mpr le_rfl; let L:= (deckX H).erase H; have hf: ∑ i∈L,f i=∑ i∈L,g i:=sum_congr rfl (fun i k=>
       let P : i ≤ H:= (deckH ..).mp (mem_erase.mp k).2
       ih i (lt_of_le_of_ne P (mem_erase.mp k).1) fun j p=> h j (p.trans P))
    have hh:=h H le_rfl; unfold view at hh; rw [←add_sum_erase _ _ he,←add_sum_erase _ _ he,hf] at hh; exact add_right_cancel hh
abbrev crank(F G:Track A E):= coal F G (· * ·)
lemma view_crank(a:A)(F G:Track A E):view a (crank F G)=view a F* view a G:= focuses a F G _ (fun x=> ⟨AddMonoidHom.mulLeft x,rfl⟩) (fun x=>⟨AddMonoidHom.mulRight x,rfl⟩)
abbrev ownH(Q:Type*)[One Q][Zero Q](A:Type*)[PartialOrder A][OrderBot A][DecidableEq A]: Track A Q:=Pi.single ⊥ 1
lemma view_one (a:A):view a (ownH E A)=1:=(singleV ..).trans (if_pos bot_le)
lemma crank_A(F G H:Track A E):crank (crank F G) H=crank F (crank G H):=funext fun i=> proves fun j _=>by simp only [view_crank,mul_assoc]
lemma crank_L(F:Track A E): crank (ownH E A) F=F:=funext fun i=> proves fun j _=>by rw [view_crank,view_one,one_mul]
lemma crank_R(F:Track A E): crank F (ownH E A)=F:=funext fun i=> proves fun j _=>by rw [view_crank,view_one,mul_one]
end YM.CF.Stilo

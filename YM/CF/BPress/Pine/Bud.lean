import YM.CF.BPress.Pine.Paint
import YM.CF.BPress.Palmer.Limousine
/- Eq:B-PfC sum over decorated labels. Group with Palmer, fits contour-free theorem part. Pairing *sign* and zero of non-matches/repeats implemented through genuine Pfaffian tested on exterior strings, only geometry projection for power. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pine
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Ledger Push.AbsoluteSums Ursell Palmer Fock Pastry Pf EdgeD
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]
variable {B J:Type}[Fintype B][DecidableEq B][Fintype J][DecidableEq J] {Y:Type}[DecidableEq Y][Fintype Y]{F:Branch.Field Y}
structure Story (J:Type) (D:EdgeD I B Y F) where
 base : J→ Seal Y
 word : J→ List I
 landed : ∀ i, Grove F (base i)
 e (i): Even (word i).length
 n (i): (word i).Nodup
 paid(i)(k:I)(h:k∈word i): D.anchor k∈ base i
 rule : J→J→Prop
 focus : ∀i j, rule i j→¬Disjoint (base i) (base j)
namespace Story
variable {D:EdgeD I B Y F}(S:Story J D) (K:B→ℂ)(u:J→ℂ)
local notation "ΩP"=>vacuum I
abbrev trunk (i:J): Dough I:=⟨raw (S.word i), (lifted (S.word i) (S.e i)).1⟩ -- syntax
abbrev branch (i:J):=D.stair K (S.word i).toFinset
lemma branch_eq (i:J): S.branch K i=((S.word i).map (D.stalk K)).prod:= List.prod_toFinset _ (S.n _)
abbrev digit(T:Finset J): Dough I:=∏ i∈ T,S.trunk i
abbrev minor(T:Finset J): Dough I:=∏ i∈ T,S.branch K i
abbrev text (L:List J):= (L.map S.word).flatten
lemma chunk (L:List J): raw (S.text L)=((L.map S.trunk).prod).val:=by induction L with| nil=>rfl|cons i l ih=> rw [text,List.map_cons,List.flatten_cons, raw_join,show raw _= _ from ih, List.map_cons, List.prod_cons]; rfl -- tune
lemma chunk_minor (L:List J): ((S.text L).map (D.stalk K)).prod= (L.map (S.branch K)).prod:=by induction L with|nil=>rfl|cons i l ih=> rw [List.map_cons,List.prod_cons,text,List.map_cons,List.flatten_cons,List.map_append,List.prod_append, show (( (l.map S.word).flatten).map (D.stalk K)).prod= _ from ih, S.branch_eq]
def grap (A B : Dough I):= inner ℂ (acts A.val ΩP) (acts B.val ΩP)
def lives (t:Finset J)(l:List J): Prop:= l.toFinset=t∧ l.Nodup -- tune S drops
lemma projection(L:List J)(q:Finset J)(t:lives q L): shape (bkg D K) (S.text L)= grap (S.digit q) (S.minor K q):=by rw [D.rewind,chunk,chunk_minor]; simp only [grap, digit, minor, ← t.1,List.prod_toFinset _ t.2] -- tune
abbrev Drone:Type:=Σ x:J,D.Net (S.word x)
def fetch : S.Drone→ J:= Sigma.fst -- don't name token starts reserved?
def fort (p:S.Drone):= S.base p.1 ∪ location D (S.word p.1) p.2
abbrev firm(p:S.Drone):=S.trunk p.1
abbrev cairn(p:S.Drone) := glow D K _ p.2
def totalU(p:Finset J) := if Push.AbsoluteSums.Gas.separated S.rule p then (∏ i∈p,u i)*grap (S.digit p) (S.minor K p) else 0
def Class (p:Finset (S.Drone)): Prop:=Set.InjOn S.fetch p ∧ Push.AbsoluteSums.Gas.separated S.rule (p.image S.fetch) -- same label diff decorations
abbrev allStem (p:Finset (S.Drone)):=∏ i∈ p,firm S i
abbrev allFresh(p:Finset (S.Drone)):=∏ i∈ p,cairn S K i
def totalW(p:Finset (S.Drone)):= if S.Class p then (∏ i∈p,u (S.fetch i))*grap (S.allStem p) (S.allFresh K p) else 0
lemma unroll(T:Finset J): S.minor K T=∑ i∈Assembly S.fetch T,allFresh S K i:= by
 apply salon; intro i; rw [S.branch_eq, D.springP K _ (S.n i)]; exact (trib_sigma (P:=fun x=>D.Net (S.word x)) (cairn S K) i).symm -- tune eq expansion due Sigma Dec mismatch
lemma unload (p:Finset (S.Drone))(s:Finset J)(h:p∈Assembly S.fetch s): S.allStem p=S.digit s:=by unfold allStem digit; rw [←blocks _ _ _ h, prod_image (mem_filter.mp h|>.2.2)]; rfl -- tune class
lemma tonality(T:Finset J): totalU S K u T=∑ i∈ Assembly S.fetch T,totalW S K u i:= by
 unfold totalU; split; next p=>
    rw [grap, unroll, show Subtype.val (∑ i∈Assembly S.fetch T,allFresh S K i)=_ from sumS _ _, act_sum,inner_sum,mul_sum]; apply sum_congr rfl; intro i h; let u':= mem_filter.mp h|>.2; have he:i.image S.fetch=T:=blocks _ _ _ h; rw [totalW,if_pos (show S.Class i from ⟨u'.2,he.symm ▸ p⟩), unload S i T h]; apply congrArg₂ (·*·); rw [← he,prod_image u'.2]; rfl -- tune
 next p=> symm; apply sum_eq_zero; intro i h; rw [totalW,if_neg ?_]; intro t; exact p (blocks _ _ _ h ▸ t.2) -- tune
lemma hike: ∑ i:Finset J,totalU S K u i=∑ p:Finset S.Drone,totalW S K u p:=by simp_rw [S.tonality K u]; rw [collectMe,sum_subset (filter_subset ..)]; intro i _ p; rw [totalW,if_neg (fun u=>p (mem_filter.mpr ⟨mem_univ _,u.1⟩))] -- tune universe arg
end Story
end YM.CF.BPress.Pine

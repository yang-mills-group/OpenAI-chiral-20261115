import YM.CF.BProof.Pods.Motion
import YM.CF.BProof.Gates.Coat

/- Local tests precomputed for λ. Holder of requests via cloth(∛bρ). Operation off any
budget `r≥200`. Real Gauge predicates.
 -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.BProof.Cabinet
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing Micro
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Pods Posts
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}(P:Entice S L a d y){N:Side}(Y:S.Setup L a (More N) d y)
variable (T:PathData G)(θ:ℝ)
local notation "mH"=> Y.yard
local notation "B"=> Y.Block
local notation "g₀"=> Y.g
abbrev Pod:= Brick.Static mH g₀
variable (x x':Pod Y)
abbrev tool:= Brick.Act.pawn mH g₀ x
abbrev spores:= Brick.Act.fields mH g₀ x
abbrev orbitL:= Brick.Act.ids mH g₀ x
abbrev picture:= Setup.area P Y T θ (tool Y x)
abbrev yelp:= Setup.color P Y T θ (tool Y x)
abbrev bitL:= Brick.shake mH g₀ y x -- use Brick.
abbrev sick := Setup.bad Y (tool Y x)
abbrev Ready := Along P Y T θ (tool Y x)
lemma readyV : Virtue (House.Season mH Y.c') _ (Ready P Y T θ):= (Brick.Act.pawn_m ..) (Pawn.rich_m ..)
lemma sick_c(i:B): i∈ sick Y x↔ Brick.Act.Fac mH g₀ y i (x i):= Brick.Act.peak ..
lemma health : Vis (sick Y):= Brick.Act.sick_vis mH g₀ y
lemma enlargement : sick Y x⊆ bitL Y x:= Brick.Act.sick_e ..
-- frame vertices and horiz tests per column b:N side Face owned by gap index attaching.
abbrev nX (k:Y.yard.Index) := Manual.nIndex mH k
abbrev nB (k:Y.yard.Index) := Manual.nSide mH k
abbrev lid := Brick.fresh mH y (tool Y x)
lemma frame (i:Y.yard.Index) (p:Space (More N)): Setup.owner Y (i:=nX Y i) (nB Y i) p=(i,p):=by unfold Setup.owner; rw [Manual.slide] -- tune
variable (q:Y.yard.Col)
-- commit tests. Use snuff rather than bed eq. Scope approval at a single q.
def Snuff := q∈ (tool Y x).sev ↔ Pawn.level (tool Y x) y T θ (soil P Y) q∉ Locale.dry mH S.κ y q
abbrev lay(b:Bool)(i:Y.yard.Index):= swell (i:=i) P Y T θ (tool Y x) b q.2
def glamour (i:Y.yard.Index)(b:Bool)(q:Space (More N))(j:TAxis): Prop:= Face.Follow y (yelp P Y T θ x i b q) (yelp P Y T θ x i b (q+tstep j)) ((obtainF P Y T θ (tool Y x) b (i:=i)) (q,j))
def Bloom:= Snuff P Y T θ x q∧ lay P Y T θ x q (nB Y q.1) (nX Y q.1) ∧∀ i:TAxis, glamour P Y T θ x (nX Y q.1) (nB Y q.1) q.2 i
lemma bloom_m : Virtue (House.Season mH Y.c') _ (fun x=> Bloom P Y T θ x q):=by
 let i:=nX Y q.1; let b:=nB Y q.1; let A(x:Pod Y):= tool Y x; let Cz(x:Pod Y):=obtainF P Y T θ (A x) b (i:=i); let f(x:Pod Y):=yelp P Y T θ x i b
 have hA:= Brick.Act.pawn_m mH g₀; have hv:= (Pawn.issue_m mH y T θ (soil P Y)).comp hA; let Wp:=Space (More N)
 have hf(p':Wp):Measurable fun x: Pod Y=> f x p':=by
    have ht:= (Pawn.rent_m mH Y.hall y T θ (soil P Y)).comp hA; exact (measurable_pi_apply p').comp ((measurable_pi_apply b).comp ((measurable_pi_apply i).comp ht))
 have hg:Measurable Cz:= by apply measurable_pi_lambda; intro ⟨p,q⟩; exact (measurable_pi_apply (horiz (front (Y.yard.u i) Y.yard.long b) p q)).comp hv
 apply MeasurableSet.inter; swap
 · apply MeasurableSet.inter (show MeasurableSet {x:Pod Y|Face.Mood S.K y (Cz x) q.2 (f x q.2)} from hg.prodMk (hf _) (Face.mood_c ..)); change MeasurableSet {x:Pod Y | ∀ j:TAxis, glamour P Y T θ x (nX Y q.1) (nB Y q.1) q.2 j}; rw [Set.setOf_forall]; apply MeasurableSet.iInter; intro j; unfold glamour Face.Follow; apply measurableSet_le _ measurable_const; let D':=q.2; exact (continuous_cd G).measurable.comp (f:=fun x=> (f x (q.2+tstep j),f x q.2*(Cz x) (q.2,j))) ((hf _).prodMk ((hf _).mul ((measurable_pi_apply _).comp hg)))
 -- urgent
 · change MeasurableSet {x:Pod Y|Snuff P Y T θ x q}; unfold Snuff; apply MeasurableSet.iff; exact hA (Pawn.sev_sets (fun t=> q∈t)); exact (((measurable_pi_apply q).comp ((Pawn.level_m mH y T θ (soil P Y)).comp hA)) (Pub.den_m ..)).compl
lemma authority : Ready P Y T θ x↔ lid Y x∧∀ c:Y.yard.Col,Bloom P Y T θ x c:=by
 let Q:= tool Y x; let K:=Pawn.level Q y T θ (soil P Y); let Hp:=F' P Y T θ Q
 have he: (∀ c:Y.yard.Col, Snuff P Y T θ x c) ↔ Locale.bed mH S.κ y K= Q.sev:=by
    rw [Finset.ext_iff]; apply forall_congr'; intro i; unfold Locale.bed; rw [Finset.mem_filter]; simp only [Finset.mem_univ,true_and]; exact ⟨Iff.symm,Iff.symm⟩
 have hu: certified P Y T θ Q ↔∀ q:Y.yard.Col, lay P Y T θ x q (nB Y q.1) (nX Y q.1) ∧∀ i:TAxis, glamour P Y T θ x (nX Y q.1) (nB Y q.1) q.2 i:=by
    constructor
    · intro h q; have ht:=yard_climb P Y T θ Q h (nX Y q.1) (Manual.wall mH q.1) (nB Y q.1); exact ⟨ht.1 q.2,ht.2 q.2⟩
    intro h i; split; rename_i u; exact Brick.Act.marked mH g₀ x i u
    rename_i u; have hx(b:Bool): nX Y (location mH i b)= i ∧ nB Y (location mH i b)=b:= Manual.round mH b i u; have hg(b:Bool):Face.Lift Y.hall.K y (obtainF P Y T θ Q b (i:=i)) (yelp P Y T θ x i b):=by -- Y.yard.x change
       have H(p:Space (More N)):let a:Y.yard.Col:=(location mH i b,p); lay P Y T θ x a b i ∧∀ j:TAxis, glamour P Y T θ x i b p j:= by intro a; have he:= h a; rw [show nX Y a.1=i from (hx b).1,show nB Y a.1=b from (hx b).2] at he; exact he -- unsafe rewriting i in a!
       exact ⟨fun p=>(H p).1,fun p=>(H p).2⟩
    rw [wages_mem]; intro b; have hw:=hg b; rw [yelp,color,Pawn.rent,sweepLabel,if_neg u] at hw; exact hw -- tune 
 change (hot.Fares mH y Q.gauss ∧ Locale.bed mH S.κ y K=Q.sev ∧ certified P Y T θ Q∧ _ )↔ _; rw [←he,hu]  -- tune
 unfold Bloom lid Brick.fresh; grind
end YM.CF.BProof.Cabinet

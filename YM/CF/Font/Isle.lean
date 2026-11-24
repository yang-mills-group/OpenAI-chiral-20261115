import YM.Exterior.Complex
import YM.Work.E04
import YM.Lattice.Box
/-! Polynomial path records including torus generators. Four-direction discrete homotopy preserving quantitative extent. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Font
open Function Filter Metric Lattice Finset MeasureTheory Exterior
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {n:Side}{C: Type*} [AddCommGroup C]
abbrev Wind(n:Side):= (Face (Per n))⊕Axis
def swirl (n:Side)(a:Axis): Walk:= List.replicate n.val (posDir a)
def heat(x:Site n)(J:Links (Per n) C)(a:Wind n):C:= match a with
 | Sum.inl (y,i)=> linkSum J y (square i.val.1 i.val.2)
 | Sum.inr i=> linkSum J x (swirl n i)
def dial(x:Site n)(a:Wind n):ℕ:= match a with | Sum.inl y=> separation x y.1 | Sum.inr _=> n.val
def ask(a:Step)(u:Links (Per n) C)(x:Site n):= if a.neg then -u (a.used x) else u (a.used x)
lemma bin_reverse(a:Step)(u:Links (Per n) C)(x:Site n): ask a.rev u (x+a.vec)= -ask a u x:=by cases a with| mk a i=> cases i <;> simp [ask,Step.rev,Step.vec,Step.used,sub_eq_add_neg]
lemma amix(x:Site n)(J:Links (Per n) C)(a b: Walk):linkSum J x (a++b)=linkSum J x a+linkSum J (stop x a) b:=by induction a generalizing x <;> simp_all [linkSum,stop,add_assoc]
lemma aturn(x:Site n)(J:Links (Per n) C)(a:Walk):linkSum J (stop x a) (reverse a)= - linkSum J x a:=by
 induction a generalizing x with
 | nil=>simp [linkSum,reverse]
 | cons d w h=>
   rw [show reverse (d::w)= reverse w++[d.rev] by simp [reverse],stop,amix,h,reverse_stop]; change _+ (ask _ _ _+0)=-(ask _ _ _+_); rw [bin_reverse]; abel
lemma small(x:Site n)(w:Step): separation x (x+w.vec)≤1:=Work.E04.stop_separation_le x [w]
private def dow(x:Site n)(a:Step):Site n:=if a.neg then x-step a.dir else x
def patch(x:Site n)(a b:Step):Site n:= dow (dow x a) b
lemma dial_v (x:Site n)(a:Step):separation x (dow x a) ≤1:=by
 unfold dow; split; · exact (by simpa [sub_eq_add_neg,Step.vec,negDir] using small x (negDir a.dir))
 simp -- private inaccessible
lemma patch_near (x:Site n)(a b:Step):separation x (patch x a b)≤2:=by unfold patch; exact (separation_triangle x (dow x a) _).trans (add_le_add (dial_v x a) (dial_v _ _))
def seal_t (b:Bool)(x:C) :C:= if b then -x else x
lemma rope(x:Site n)(J:Links (Per n) C)(a b:Step): linkSum J x [a,b]=linkSum J x [b,a]+seal_t (a.neg.xor b.neg) (linkSum J (patch x a b) (square a.dir b.dir)) :=by
 rcases a with ⟨i,p|p⟩<;>rcases b with ⟨j,q|q⟩<;> simp [linkSum,Step.used,Step.vec,seal_t,dow,patch,square,posDir,negDir,sub_eq_add_neg]<;> abel_nf -- tune
lemma pitch (x:Site n)(J:Links (Per n) C)(a b:Axis): linkSum J x (square a b) = -linkSum J x (square b a):=by simp [square,linkSum,posDir,negDir,Step.used,Step.vec,sub_eq_add_neg]; abel_nf
abbrev Course(n:Side):= List (Face (Per n) × Bool)
def book (u:Links (Per n) C)(f:Course n): C:= (f.map (fun z=> seal_t z.2 (heat 0 u (.inl z.1)))).sum
lemma pays(a b:Course n)(u:Links (Per n) C):book u (a++b)=book u a+book u b:=by simp [book]
def Mice(x:Site n)(a b: Walk)(j R:ℕ)(C:Type*) [AddCommGroup C]:Prop:= stop x a=stop x b∧∃ f:Course n, f.length ≤ j∧(∀ i∈f,separation x i.1.1≤ R)∧∀ J:Links (Per n) C, linkSum J x a=linkSum J x b + book J f
variable (C)
lemma curves(x: Site n)(a b:Step)(h:a.dir≠b.dir): Mice x [a,b] [b,a] 1 2 C:=by
 let z:= patch x a b; let k:= a.neg.xor b.neg; refine ⟨show x+a.vec+b.vec=x+b.vec+a.vec from (by abel),?_⟩
 rcases lt_or_gt_of_ne h with e|e
 · exact ⟨[((z,⟨(a.dir,b.dir),e⟩),k)],le_rfl,fun i h=> (by simp at h; subst i; exact patch_near ..),fun J=> by rw [rope]; unfold book heat; simp [z,k]⟩
 refine ⟨[((z,(⟨(b.dir,a.dir),e⟩:PlaqAxes)),!k)],le_rfl,fun i h=> (by simp at h; subst i; exact patch_near ..),fun J=>?_⟩
 rw [rope]; unfold book heat; simp; rw [pitch z J a.dir b.dir]; change seal_t k (-(linkSum J z (square b.dir a.dir)))=seal_t (!k) _; cases k<;>simp [seal_t]
end YM.CF.Font

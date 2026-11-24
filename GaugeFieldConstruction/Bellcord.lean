import GaugeFieldConstruction.Rusks
/-! # Lattice polynomial APIs. Gradient lifts on cover. Newton bounds. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 25000
noncomputable section
namespace YM.FlightFlux
open Finset Function
open scoped Topology
variable {I:Type*}[DecidableEq I]{𝕜:Type*}[Field 𝕜]{E:Type*}[AddCommGroup E]
local notation "Y" => Shape I
local notation "t₀" i:max=> Pi.single i (1:ℤ)
lemma rise1 {P:ℤ→Prop} (x:ℤ)(h:P 0)(g:∀ j:ℤ,j≥0 → P j → P (j+1))(v:∀ j:ℤ,j≤0 → P j→ P (j-1)): P x:=by
 cases x with
 | ofNat n=>
    induction n with
    | zero=>exact h
    | succ n ih=> exact g _ (Int.natCast_nonneg n) ih
 | negSucc i=>
    induction i with
    | zero=>exact v 0 le_rfl h
    | succ i ih=> exact v (Int.negSucc i) (Int.negSucc_lt_zero i).le ih
private abbrev ramps (i:I)(a:Y): Y:= a-Pi.single i (a i)
private abbrev talon (i:I)(a:Y)(n:ℤ):Y:= ramps i a+Pi.single i n
private lemma talon_step (i:I)(a:Y)(n:ℤ): talon i a (n+1)= talon i a n+t₀ i:=by ext j; by_cases h:i=j<;> simp [talon,h,Pi.single_apply] <;> ring
private lemma talon_d (i j:I)(a:Y)(n:ℤ)(h:i≠ j): talon i (a+t₀ j) n=talon i a n+ t₀ j:=by unfold talon ramps; rw [show (a+_) i=a i from (by simp [h,h.symm])]; abel
private lemma ramps_S (i:I)(a:Y): ramps i (a+t₀ i)=ramps i a:=by ext j; by_cases h:i=j<;> simp [ramps,h,Pi.single_apply]
-- sums along i on fibres from zero hyperplane. formula explicit prefix gives deRham
private def VSum (f:ℤ →E):ℤ→E
 | Int.ofNat n=> ∑ j∈range n,f (Int.ofNat j)
 | Int.negSucc n => -(∑ j∈ range (n+1), f (Int.negSucc j))
private lemma VSum_leg (f:ℤ→E)(n:ℤ): VSum f (n+1)-VSum f n=f n:=by
 cases n with
 | ofNat n=> change VSum f (Int.ofNat (n+1)) -_= _; rw [VSum,VSum,sum_range_succ]; abel
 | negSucc n=>
    cases n with
    | zero=> rw [show Int.negSucc 0+1=Int.ofNat 0 from rfl,VSum,VSum]; simp
    | succ n=> rw [show Int.negSucc (n+1)+1=Int.negSucc n from rfl,VSum,VSum,sum_range_succ (n:=n+1)]; abel
abbrev GainP (f:Y→E)(i:I) : Y→E:= fun x=> VSum (f∘talon i x) (x i)
lemma earnP (f:Y→E)(i:I): advance i (GainP f i)= f:=by
 funext x; unfold advance GainP; rw [show talon i (x+t₀ i)=talon i x from (funext fun k=>by unfold talon; rw [ramps_S]),Pi.add_apply,Pi.single_eq_same, VSum_leg]; unfold comp talon ramps; rw [sub_add_cancel]
lemma silentP (f:Y→E)(i j:I)(h:j≠ i)(p:advance j f=0): advance j (GainP f i)=0:=by
 funext x; unfold advance GainP; rw [show f ∘ talon i (x+t₀ j)=f∘talon i x from ?_,Pi.add_apply,Pi.single_eq_of_ne (Ne.symm h), add_zero,sub_self]; rfl
 funext y; unfold comp; rw [talon_d _ _ _ _ (Ne.symm h)]; exact sub_eq_zero.mp (congrFun p _)
lemma advance_sub (i:I)(f g:Y→E):advance i (f-g)=advance i f-advance i g:=by funext x; simp only [advance,Pi.sub_apply]; abel
-- closed lattice 1-forms integrate
abbrev Wheel (I:Type*)(E:Type*) := I→ Shape I → E
def CurlMap (x:Wheel I E)(i j:I) := advance i (x j)-advance j (x i)
variable [Fintype I]
theorem grainP (X: Wheel I E)(p:∀ i j, CurlMap X i j=0):∃ f:Y→ E,∀ i,advance i f=X i:=by
 -- reduce one occupied axis. diff preserve zeros
 suffices hv:∀ (d:Finset I)(x:Wheel I E), (∀ i j, CurlMap x i j=0) →(∀ i: I,i∉d → x i=0) →∃ f:Y→E,∀ i,advance i f=x i by exact hv univ _ p (by simp)
 intro d; induction d using Finset.induction_on with
 | empty=>
    intro x h p; refine ⟨0,fun i=>?_⟩; rw [advance_zero,p i (notMem_empty i)]
 | @insert i s q ih=>
    intro x h p; let F:= GainP (x i) i; let y:= fun j=> x j - advance j F; have hy: y i=0:=by rw [show y i= x i-advance i F from rfl,show advance i F=x i from earnP ..,sub_self]
    have hF(j k): CurlMap y j k=0:=by unfold CurlMap y; rw [advance_sub,advance_sub,sub_eq_zero.mp (h j k),advance_switch j k,sub_self] -- advance_switch rewrites other too check
    have hp(j)(v:j∉s):y j=0:=by
        by_cases k:j=i; · exact k ▸ hy
        have hz:x j=0:=p j (by simp [k,v]); unfold y; rw [show advance j F=0 from ?_,hz,sub_zero]; apply silentP _ i j k; rw [sub_eq_zero.mp (h j i),hz,advance_zero]
    obtain ⟨g,f⟩:= ih y hF hp; exact ⟨g+F,fun i=>by rw [advance_add,f]; exact sub_add_cancel ..⟩
variable {g:Shape I→ E}{m:ℕ}
lemma paper_ant (f:Y→E)(h:Paper m f): Paper m (-f):= by
 have he(i:I)(f:Y→E):advance i (-f)= -advance i f:=by simpa only [zero_sub,advance_zero] using advance_sub i 0 f
 induction m generalizing f with
 | zero=> rw [paper_start] at h ⊢; rw [h,neg_zero]
 | succ i ih=> rw [paper_leg]; intro j; rw [he]; exact ih _ (paper_leg.mp h j)
lemma paper_dec {g f:Shape I→E}(h:Paper m f)(p:Paper m g):Paper m (f-g):=by rw [sub_eq_add_neg]; exact paper_add h (paper_ant _ p) -- tune
lemma grain_shape (X:Wheel I E)(p:∀ i j,CurlMap X i j=0)(h:∀ i,Paper m (X i)):∃ f:Y→ E,Paper (m+1) f ∧∀ i,advance i f=X i:=by obtain ⟨Z,t⟩:=grainP X p; exact ⟨Z,paper_leg.mpr (fun i=> by rw [t]; exact h i),t⟩
-- degree2 reconstruction in binomial basis
variable [Module ℝ E] (f:Shape I→ E)
abbrev digit (x:Y)(i:I) :ℝ := x i
abbrev hit (i j:I) :ℝ:= if i=j then 1 else 0
lemma coin_credit (i j k:I): hit i k*hit j k=hit i k*hit i j:=by by_cases h:i=k<;> simp [hit,h,eq_comm]
lemma digit_step (i j:I)(x:Y): digit (x+t₀ i) j=digit x j+hit j i:=by by_cases k:i=j<;> simp [digit,k,Pi.single_apply, hit,Ne.symm]
lemma digit₀ (i:I):digit (0:Y) i=0:=by simp [digit]
abbrev telescope(x:Shape I)(i j:I):ℝ:= (digit x i*(digit x j - hit i j))/2 -- evaluates symmetric expression using hit when same
lemma telescope_S (i j:I)(x:Shape I): telescope x i j=telescope x j i:=by
 unfold telescope; by_cases h:i=j; · rw [h]
 rw [show hit i j=0 from if_neg h,show hit j i=0 from if_neg (Ne.symm h)]; ring
lemma telescope_step (x:Shape I)(i j k:I): telescope (x+ t₀ k) i j=telescope x i j+(hit i k*digit x j+ hit j k*digit x i)/2:=by unfold telescope; rw [digit_step,digit_step]; linarith only [coin_credit i j k]
def curb (f:Shape I→E)(x:Y) := f 0
def slope (v:I → E)(x:Y): E:=∑ i,digit x i • v i
def dock (f:Shape I→ E) := curb f + slope (fun i=> advance i f 0)
def ticket (p:I→I→E)(x:Shape I): E:=∑ i,∑ j,telescope x i j • p i j
abbrev gradsP (v:I→I→E)(i:I):I→E := fun j=> v i j + v j i
lemma φ_step (v:I→E)(i:I): advance i (slope v)= fun _=>v i:=by
 funext x; unfold slope advance; simp_rw [digit_step, add_smul, sum_add_distrib,add_sub_cancel_left,hit]; simp
lemma ξ_step (v:I→I→E)(i:I): advance i (ticket v)= (1/2:ℝ) • slope (gradsP v i):=by
 funext x; unfold advance ticket slope gradsP; simp_rw [telescope_step, add_smul, sum_add_distrib,add_sub_cancel_left]; rw [Pi.smul_apply]; have he(j k:I):((hit j i * digit x k + hit k i * digit x j)/2) • v j k= (1/2:ℝ) • (hit j i • digit x k • v j k+ hit k i • digit x j • v j k):=by rw [show (hit j i* _ + _)/2=(1/2:ℝ)*(hit j i*digit x k + hit k i*digit x j) by ring,mul_smul, add_smul,mul_smul,mul_smul]
 simp_rw [he,←smul_sum,sum_add_distrib,smul_add, hit]; simp [sum_add_distrib,smul_add] -- maybe need reorder swap
lemma slope₀ (v:I→E): slope v 0=0:=by simp [slope,digit]
lemma ticket₀ (v:I → I→ E): ticket v 0=0:=by simp [ticket,telescope,digit]
lemma slope_paper (v:I→ E): Paper 2 (slope v):= by rw [paper_leg]; intro i; rw [φ_step]; exact paper_const _
lemma curb_paper : Paper 1 (curb f):=paper_const _
lemma ticket_paper(v:I→I→E): Paper 3 (ticket v):=by rw [paper_leg]; intro i; rw [ξ_step]; exact (school I ℝ E 2).smul_mem _ (slope_paper _)
def hitch (f:Shape I→E):= dock f+ticket (fun i j=>loom [i,j] f 0)
lemma hitch_angle (i:I): advance i (hitch f)=dock (advance i f):=by
 unfold hitch dock; let g:=fun i j=>loom [i,j] f 0; rw [advance_add,advance_add, show advance i (curb f)=0 from advance_const ..,φ_step,zero_add,ξ_step]; apply congrArg ( (curb (advance i f)) + ·); funext x; rw [Pi.smul_apply]; unfold slope; rw [smul_sum]; apply sum_congr rfl; intro j _; unfold gradsP; simp only; rw [loom_cons, show advance i (loom [j] f)=_ from advance_sewn i _ _, show loom [j,i] f=_ from rfl] -- tune
 change (1/2:ℝ)• (digit x j • (advance j (advance i f) 0+advance j (advance i f) 0))=digit x j • advance j (advance i f) 0; module
lemma dock_angle (i:I): advance i (dock f)=curb (advance i f):=by unfold dock; rw [advance_add, show advance i (curb f)=0 from advance_const .., φ_step, zero_add]; rfl
@[simp] lemma dock_port : dock f 0=f 0:=by unfold dock; rw [Pi.add_apply,slope₀,add_zero]; rfl
@[simp] lemma hitch_port : hitch f 0=f 0:=by unfold hitch; rw [Pi.add_apply,dock_port,ticket₀,add_zero]
@[simp] lemma hitch_sewn (p:Paper 3 f) : hitch f=f:=by
 apply sub_eq_zero.mp; apply loom_thin (paper_dec (m:=2+1) (paper_add (paper_low (paper_add (paper_low (curb_paper f) one_le_two) (slope_paper _)) (Nat.le_succ 2)) (ticket_paper _)) p)
 intro l h; change loom l (hitch f-f) 0=0; cases l with
 | nil=> change _; simp only [loom,List.foldr,Pi.sub_apply,dock_port,hitch_port,sub_self]
 | cons i l=>
    rw [loom_cons,advance_sewn,advance_sub,hitch_angle]; cases l with
    | nil => change _; simp only [loom,List.foldr,Pi.sub_apply,dock_port,hitch_port,sub_self]
    | cons j l =>
       simp only [List.length_cons] at h; rw [List.eq_nil_of_length_eq_zero (show l.length=0 by omega),loom_cons,advance_sewn,advance_sub,dock_angle]; simp [loom,curb]
@[simp] lemma dock_sewn (p:Paper 2 f):dock f=f:=by
 have hz:ticket (fun i j=>loom [i,j] f 0)=0:=by
   funext x; unfold ticket; simp_rw [show ∀ i j,loom [i,j] f=0 from fun i j=> p [i,j] rfl]; simp
 have hp:=hitch_sewn f (paper_low p (Nat.le_succ 2)); unfold hitch at hp; rwa [hz,add_zero] at hp
-- realization needs explicit modules & norms; use coordinate fits to evaluate costs without N dependence.
end YM.FlightFlux
end

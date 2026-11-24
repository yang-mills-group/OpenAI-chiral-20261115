import YM.Work.E01
/-! # Lattice polynomial APIs. Use discrete degree, homogeneous only on graded quotient.
Language of E1,F.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 25000
noncomputable section
namespace YM.FlightFlux
open Finset Function
open scoped Topology
section
variable {I:Type*}[DecidableEq I]{E F:Type*} [AddCommGroup E]
abbrev Shape (I:Type*):= I →ℤ
local notation "Y" => Shape I
local notation "t₀" i:max=> Pi.single i (1:ℤ)
def advance (i:I)(f:Y→E)(x:Y):= f (x+t₀ i) - f x
def loom (i:List I)(f:Y→E) : Y→E:= i.foldr advance f
lemma advance_switch (i j:I)(f:Y→E): advance j (advance i f)=advance i (advance j f):= by
 funext x; unfold advance; rw [add_right_comm x]; abel
@[simp] lemma loom_cons (i:I)(l:List I)(f:Y→E):loom (i::l) f=advance i (loom l f):= rfl
lemma advance_sewn (i:I)(t:List I)(f:Y→E): advance i (loom t f)= loom t (advance i f):=by induction t with|nil=> rfl|cons j t ih=> rw [loom_cons, advance_switch,ih, loom_cons]
lemma advance_add (i:I)(f g:Y→ E):advance i (f+g)=advance i f+advance i g:=by funext x; simp only [advance,Pi.add_apply]; abel
lemma advance_zero (i:I): advance (E:=E) i 0=0:= by ext; simp [advance]
lemma loom_zero (l:List I) : loom (E:=E) l 0=0:=by induction l with|nil=>rfl|cons i l ih=> rw [loom_cons,ih,advance_zero]
lemma loom_add (l:List I)(f g:Y→E): loom l (f+g)= loom l f+loom l g:=by induction l with|nil=>rfl|cons i l ih=> rw [loom_cons,ih,advance_add,loom_cons,loom_cons]
lemma advance_shift (i:I)(f:Y→E)(p:Y): advance i (fun x=>f (x+p))=fun x=> advance i f (x+p):=by funext x; unfold advance; rw [add_right_comm x]
lemma advance_const (i:I)(c:E): advance i (fun x=>c)=0:=by ext; simp [advance]
abbrev stairs (x y:ℤ):ℕ:= (x-y).natAbs
variable [Fintype I]
def lateral (x:Y):ℕ:=∑ i,(x i).natAbs
lemma lateral_zero : lateral (0:Y)=0:=by simp [lateral]
lemma lateral_add (x y:Y) : lateral (x+y) ≤ lateral x+lateral y:=by unfold lateral; rw [← sum_add_distrib]; exact sum_le_sum fun i _=>Int.natAbs_add_le ..
lemma lateral_neg (x:Y):lateral (-x)=lateral x:=by simp [lateral]
lemma lateral_single (i:I) (n:ℤ): lateral (Pi.single i n)=n.natAbs:=by
 unfold lateral; rw [sum_eq_single i, Pi.single_eq_same]; · intro b _ h; simp [h]
 simp
lemma retreat {x:Y}(p:x≠0): ∃ (i:I)(y:Y), lateral x=lateral y+1∧ (x=y+t₀ i∨ y=x+t₀ i):=by
 obtain ⟨i,h⟩:= Function.ne_iff.mp p; change x i ≠ 0 at h
 have hv(l y:Y)(g:∀ j,j≠ i → l j=y j)(h:(l i).natAbs=(y i).natAbs+1): lateral l=lateral y+1:=by
    unfold lateral; rw [←Finset.sum_erase_add _ _ (mem_univ i),←Finset.sum_erase_add univ (fun j=>(y j).natAbs) (mem_univ i),h, Finset.sum_congr rfl (fun j (hj:j∈univ.erase i)=> congrArg Int.natAbs (g j (mem_erase.mp hj).1))]; exact (Nat.add_assoc ..).symm
 rcases lt_or_gt_of_ne h with h|h
 · refine ⟨i,x+t₀ i,hv x _ (fun j w=>by simp [w]) ?_,Or.inr rfl⟩; simp only [Pi.add_apply,Pi.single_eq_same]; omega
 refine ⟨i,x-t₀ i,hv x _ (fun j w=> by simp [w]) ?_,Or.inl (sub_add_cancel x _).symm⟩; simp only [Pi.sub_apply,Pi.single_eq_same]; omega
lemma climb (P:Y→Prop)(x:Y)(h:P 0)(q:∀ i j, lateral j<lateral x → P j → ∀ y, lateral y = lateral j+1 → (j=y+t₀ i∨y=j+t₀ i)→P y): P x:=by
 suffices H:∀ n:ℕ,n≤ lateral x→ ∀ i:Y,lateral i=n→ P i by exact H _ le_rfl _ rfl
 intro n; induction n using Nat.strong_induction_on with
 | h n ih=>
    intro v i p; by_cases f:i=0; · exact f ▸ h
    obtain ⟨j,y,b,g⟩:=retreat f
    have hv:lateral y<n:=by omega
    exact q j y (lt_of_lt_of_le hv v) (ih _ hv (le_of_lt (lt_of_lt_of_le hv v)) _ rfl) _ b g.symm -- Or comm tune
lemma tear (f:Y→E)(v:∀ i,advance i f=0)(x:Y): f x=f 0:= climb (fun x=>f x=f 0) x rfl fun i j k p y t e=> by
    have ht(j):f (j+t₀ i)=f j:= sub_eq_zero.mp (congrFun (v i) j)
    rcases e with h|rfl; rw [←p,h,ht]; exact (ht _).trans p
-- degree LT m; degreeLT zero = only zero. Mark will pay via Newton at zero.
def Paper (m:ℕ)(f: Y→E):Prop:=∀ z:List I,z.length=m → loom z f=0
variable {m n:ℕ}{f:Shape I→ E}
theorem paper_start : Paper 0 f↔ f=0:=by refine ⟨fun p=>p [] rfl, fun p z _=> by rw [p,loom_zero]⟩
theorem paper_leg : Paper (m+1) f↔ ∀ i,Paper m (advance i f):=by
 constructor
 · intro p i l h; rw [←advance_sewn,←loom_cons]; exact p _ (by simp [h])
 intro p l h; cases l
 · simp at h
 next i l=> rw [loom_cons, advance_sewn]; exact p i _ (by simpa using h)
lemma paper_const (c:E):Paper 1 (fun (_:Shape I)=> c):=by rw [paper_leg]; exact fun i=>paper_start.mpr (advance_const ..)
lemma paper_firm (f:Y→E): Paper 1 f ↔ ∃ c:E,f=fun x=>c:=by refine ⟨fun p=> ⟨_,funext (tear _ (fun i=>paper_start.mp (paper_leg.mp p i)))⟩,fun ⟨_,e⟩=> e ▸ paper_const _⟩
lemma paper_low (p:Paper m f)(t:m ≤ n):Paper n f:=by
 have he(j:ℕ)(p:Paper j f):Paper (j+1) f:=by
    intro i h; cases i with
    | nil=>simp at h
    | cons i l=> rw [loom_cons,p l (by simpa using h),advance_zero]
 induction t with | refl=>exact p|step t ih=> exact he _ ih
lemma paper_add{g}(p:Paper m f)(q:Paper m g):Paper m (f+g):=by intro l h; rw [loom_add,p l h,q l h,add_zero]
lemma paper_shift (p: Paper m f)(x:Y): Paper m (fun y=>f (y+x)):=by
 induction m generalizing f with
 | zero=> rw [paper_start]; rw [paper_start] at p; rw [p]; rfl
 | succ m ih=>rw [paper_leg] at p ⊢; intro i; rw [advance_shift]; exact ih (p i)
lemma loom_thin (p:Paper (m+1) f)(h:∀ l:List I,l.length ≤ m→ loom l f 0=0): f=0:=by
 induction m generalizing f with
 | zero=> obtain ⟨c,e⟩:= (paper_firm ..).1 p; exact e.trans (funext (fun x=> (congrFun e (0:Y)).symm.trans (h [] (by simp)))) -- tune dependent
 | succ m ih=>
    have he(i):advance i f=0:=ih (paper_leg.mp p i) (by intro l g; rw [←advance_sewn,←loom_cons]; exact h _ (by simp [g])); funext x; exact (tear _ he x).trans (h [] (by simp))
lemma loom_smaller {E:Type*}[NormedAddCommGroup E](f:Y → E)(x:Y){b:ℕ}{a:ℝ}(u:lateral x ≤ b)(p:f 0=0)(w:∀ t:Y,lateral t≤ b → ∀ j, lateral (t+t₀ j) ≤ b→ ‖advance j f t‖ ≤ a): ‖f x‖ ≤ a*lateral x:=by
 apply climb _ x (by simp [lateral_zero,p]); intro i j h g y q z; change ‖f j‖ ≤ _ at g; change ‖f y‖≤ _;
 have hv:lateral y≤b:=by omega
 have hz: ‖f y-f j‖≤a:=by
    rcases z with rfl|rfl -- careful subst
    · rw [norm_sub_rev]; exact w y hv i (by omega)
    exact w _ (by omega) i hv
 rw [show a*(lateral y:ℝ)= a + a*lateral j from by rw [q]; push_cast; ring]
 exact (norm_le_norm_sub_add ..).trans (add_le_add hz g) -- name norm_sub etc tune
variable {𝕂:Type*}[Field 𝕂][Module 𝕂 E]
lemma advance_smul (a:𝕂)(f:Y→E)(i:I): advance i (a • f)= a • advance i f:=by funext x; simp [advance,smul_sub]
lemma loom_smul (a:𝕂)(l:List I)(f:Y→E): loom l (a • f)= a • loom l f:=by induction l with|nil=>rfl|cons i l ih=>rw [loom_cons,ih,advance_smul,loom_cons]
def school (I 𝕂 E:Type*)[Field 𝕂][AddCommGroup E][Module 𝕂 E][DecidableEq I][Fintype I](m:ℕ): Submodule 𝕂 (Shape I → E) where
 carrier:={i| Paper m i}
 add_mem':=paper_add -- tune
 smul_mem' a f w:= fun i v=>by rw [loom_smul a i f,w i v,smul_zero]
 zero_mem':=fun i _=> loom_zero _ -- no Fintype?
variable (I 𝕂 E m)
private lemma finiteP : ∀ n:ℕ,Finite {l:List I// l.length ≤ n}:=by
 intro n; let S:Type _ := Σ j:Fin (n+1), List.Vector I j.val
 have h(l:{l:List I//l.length≤n}): l.val.length<n+1:=by have h:=l.property; omega
 exact Finite.of_injective (fun l: {l:List I//l.length ≤ n}=> (⟨⟨l.val.length,h l⟩,⟨l.val,rfl⟩⟩:S)) (fun i j k=> Subtype.ext (congrArg (fun x:S=> x.2.val) k)) -- instance synth tune
instance school_F  [FiniteDimensional 𝕂 E] : FiniteDimensional 𝕂 (school I 𝕂 E m):=by
    let J:= {l:List I//l.length ≤ m}; haveI : Finite J:=finiteP I m
    let V: school I 𝕂 E m→ₗ[𝕂] (J → E) := {
      toFun :=fun x j=> loom j.val x.val 0
      map_add' :=fun a b=>funext (fun i=>congrFun (loom_add i.val a.val b.val) _)
      map_smul':=fun z a=>funext (fun i=>congrFun (loom_smul z i.val a.val) _) }
    apply FiniteDimensional.of_injective V; intro i j h; have ht:V (i-j)=0:=by rw [map_sub,h,sub_self]
    apply sub_eq_zero.mp; apply Subtype.ext; exact loom_thin (paper_low (f:=(i-j).val) (m:=m) (n:=m+1) ((i-j).property) (Nat.le_succ m)) (fun l h=> congrFun ht (⟨l,h⟩:J)) -- binder Finite duplicated
end
end YM.FlightFlux
end

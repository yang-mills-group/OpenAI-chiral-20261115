import YM.CF.BProof.Strip
import YM.CF.BProof.Face

/-! Closed temporal widths, horizontal & normal link parameterizations. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular
open Function Lattice Set Mag Gauge SU MeasureTheory Wilson
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
local notation "G" => SU.group
variable {s : Side} (U : Config G s)(a x : Per s)(p : Space s)(i : TAxis)

abbrev Bond (s : Side) := Edge (Site s)
def vert : Bond s := (join x p,0)
def horiz : Bond s := (join x p,i.succ)
def face (i j : Axis)(h:i<j) : Lattice.Face (Per s) := (join x p,⟨(i,j),h⟩)
def nf := face x p 0 i.succ (Fin.succ_pos i)
def hf := face x p (f₁ i).succ (f₂ i).succ (by fin_cases i <;> decide)
abbrev Slat (s : Side) := Space s × TAxis

theorem whichBond (b:Bond s) : (∃ x p,b=vert x p) ∨ ∃ x p i,b=horiz x p i := by
 rcases b with ⟨b,i⟩; refine Fin.cases ?_ (fun i=>?_) i
 · left; exact ⟨_,_,show (b,0)=vert (time b) (space b) by rw [vert,join_time_space]⟩
 right; exact ⟨_,_,i,show (b,i.succ)=horiz (time b) (space b) _ by rw [horiz,join_time_space]⟩
private lemma axes : ∀ a : PlaqAxes, (∃ i : TAxis,a.val=(0,i.succ)) ∨ ∃ i:TAxis,a.val=((f₁ i).succ,(f₂ i).succ):=by unfold TAxis; exact (of_decide_eq_true rfl) -- local Classical may block
theorem whichFace (b:Lattice.Face (Per s)) : (∃ x p i,b=nf x p i) ∨ ∃ x p i,b=hf x p i:=by
 obtain ⟨b,a⟩:=b; rcases axes a with ⟨i,hi⟩|⟨i,hi⟩
 · left; exact ⟨time b,space b,i,Prod.ext (join_time_space b).symm (Subtype.ext hi)⟩
 right; exact ⟨time b,space b,i,Prod.ext (join_time_space b).symm (Subtype.ext hi)⟩
@[simp] lemma time_h : time (horiz x p i).1=x := rfl
@[simp] lemma time_ht : time ((horiz x p i).1 + step (horiz x p i).2)=x:=by change time (join x p+step i.succ)=x; rw [← step_join]; rfl
@[simp] lemma time_v : time (vert x p).1=x:=rfl
@[simp] lemma time_vt : time ((vert x p).1 + step (vert x p).2)=x+1:=by change time (join x p+step 0)=x+1; rw [← join_step]; rfl
variable {x p i}
abbrev Wet (l:ℕ) (b : Bond s) := b.1∈ strip a l ∧ b.1+step b.2∈strip a l
@[simp] lemma wet_h (l:ℕ) : Wet a l (horiz x p i) ↔ along a x≤l:=by rw [Wet,mem_strip,mem_strip,time_h,time_ht,and_self]
lemma wet_v (l:ℕ) (h:l+1<s.val) : Wet a l (vert x p) ↔ along a x<l :=by
 simp only [Wet,mem_strip,time_v,time_vt]
 constructor
 · rintro ⟨g,e⟩; rw [along_succ (by omega)] at e; omega
 intro g; exact ⟨g.le,by rw [along_succ (by omega)]; exact g⟩

variable (x p i)
/-- Wire pull on one face. -/
def sheet : CF.BProof.Face.Sheet s:=fun b=> U (horiz x b.1 b.2)
lemma sheet_gauge (t:Site s→E) : sheet (Lattice.gauge t U) x = CF.BProof.Face.react (fun p=>t (join x p)) (sheet U x):=by
 ext1 ⟨p,i⟩; unfold CF.BProof.Face.react sheet Lattice.gauge; simp only [horiz,step_join]

@[fun_prop] lemma sheet_m : Continuous (fun U : Config G s=> sheet U x):=by unfold sheet; fun_prop
lemma sheet_eq {V:Config G s} (l:ℕ) (h: Agrees (↑(strip a l)) U V)(hz:along a x≤l) : sheet U x=sheet V x:=by
 ext1 ⟨p,i⟩; have e:= (wet_h (p:=p) (i:=i) a _).mpr hz; exact h _ e.1 e.2

lemma price_eq (x:Site s)(d d':Axis)(h:d<d') : faceValue U (x,⟨(d,d'),h⟩) = curl (U (x,d)) (U (x+step d,d')) (U (x+step d',d)) (U (x,d')):=by
 unfold faceValue curl square; simp only [travel,Step.pos_read,Step.vec_pos,Step.vec_neg,Step.neg_read,mul_assoc,mul_one]
 rw [show x+step d+step d'-step d=x+step d' by abel, show x+step d+step d'+-step d-step d'=x by abel]
lemma nfc : faceValue U (nf x p i)=curl (U (vert x p)) (sheet U (x+1) (p,i)) (U (vert x (p+tstep i))) (sheet U x (p,i)):=by unfold nf face sheet horiz vert; rw [price_eq,join_step,step_join]
lemma hfc : faceValue U (hf x p i)= CF.BProof.Face.read (sheet U x) p i:=by unfold hf face CF.BProof.Face.read; dsimp only [sheet,horiz]; rw [price_eq,step_join,step_join]
end YM.CF.BProof.Angular

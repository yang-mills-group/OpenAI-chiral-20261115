import YM.SU5.LitCurrent.Source
import Zephyr.Chern.Tile
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
open Buffered _root_.Zephyr.Chern
abbrev chTag:= _root_.Zephyr.Chern.tag
abbrev turntable (N:Side)(t:ℝ): Pane N:= petals (stream N) t
section coil
/- Record finite participating cover-site layout, duplicates including the half faces. -/
-- cover lift variant of cubelet/rake with contacts
def stair (G:Cover→List Cover)(i:Axis)(x: Cover): ℕ→ List Cover
 | 0=>[]
 | r+1=>stair G i x r ++ G (x+r • step i) ++ G (x-r • step i) ++ G (x+(r+1) • step i) ++ G (x-(r+1) • step i)
def layout (r:ℕ)(x:Cover): List Axis→ List Cover
 | []=>[x]
 | i::L=> stair (fun x=>layout r x L) i x r
lemma stair_nonempty {G:Cover→List Cover}(p:∀ x,G x≠ [])(x:Cover)(r:ℕ)(g:0<r)(i:Axis): stair G i x r ≠[]:=by cases r; omega; simp [stair,p]
lemma layout_nonempty (r:ℕ)(p:0<r)(x:Cover)(L:List Axis):layout r x L≠[]:=by
 induction L generalizing x with | nil=> simp [layout]| cons i L h=> exact stair_nonempty h x r p i
lemma stair_sum {T:Type*}[AddCommGroup T](i:Axis)(x:Cover)(G:Cover→List Cover)(F:Cover→T)(U:Site N→T)(h:∀ x:Cover,U (wrap N x)=((G x).map F).sum)(r:ℕ):
    ((stair G i x r).map F).sum=StressExchange.rake (step i) U r (wrap N x):=by
 have he(c: Cover)(u:ℕ): wrap N (c+u • step i)=wrap N c+u • step i:=by rw [map_add,map_nsmul]; simp
 have hp(c: Cover)(u:ℕ): wrap N (c-u • step i)=wrap N c-u • step i:=by rw [map_sub,map_nsmul]; simp
 induction r with | zero=> rfl| succ r e=>unfold stair StressExchange.rake; simp only [List.map_append,List.sum_append]; rw [e,←h,←h,←h,←h,he,he,hp,hp]
lemma layout_eq (r:ℕ)(x:Cover): ((layout r x arcOrder).map (fun z=>houseW (wrap N z))).sum=roomW (wrap N x) r:=by
 unfold roomW; generalize arcOrder=L; induction L generalizing x with
 | nil => simp [layout,cubelet]
 | cons i L h=> exact stair_sum i x _ _ _ (fun x=>(h x).symm) r
lemma house_trace (F: Op I)(x:Cover):Matrix.trace (F * houseW (wrap N x))=∑ i:IS,F (chTag N x i) (chTag N x i):=by
 change (∑ i:Single N,(F*houseW (wrap N x)) i i)=_
 trans ∑ i∈ inhabit (wrap N x),F i i
 · unfold inhabit; rw [sum_filter]; apply sum_congr rfl; intro i h; unfold houseW cutM; rw [Matrix.mul_diagonal]; by_cases i.1.1=wrap N x <;> simp [*,inhabit]
 symm; refine Finset.sum_bij (fun i _=> chTag N x i) (by simp [chTag,_root_.Zephyr.Chern.tag,inhabit]) ?_ ?_ (fun i _=>rfl)
 · rintro ⟨i,j⟩ _ ⟨s,m⟩ _ h; simpa [chTag,_root_.Zephyr.Chern.tag] using h
 rintro ⟨⟨y,i⟩,j⟩ h; have hx:y=wrap N x:=(mem_filter.mp h).2; subst y; exact ⟨(i,j),mem_univ _,rfl⟩
lemma tax_stairs (r:ℕ)(x:Cover)(P:SOp N)(A:Pane N) : let L(y):= legTax (P (profile A)) (tickA N) (houseW (wrap N y))
    Matrix.trace (taxKernel P (wrap N x) r (profile A))=((layout r x arcOrder).map L).sum:=by
 rw [tax_eq]; intro L; let W(X:Op I):=legTax (P (profile A)) (tickA N) X; rw [←layout_eq];
 change W (List.sum (List.map _ _))= _; generalize layout r x arcOrder=T
 induction T with
 | nil=> unfold W legTax; simp
 | cons y L h=>
    simp only [List.map_cons,List.sum_cons] at *
    rw [show W (_+_)= _ from (show ∀ i j,W (i+j)=W i+W j from (fun i j=>by unfold W legTax; rw [mul_add,Matrix.trace_add])) _ _,h]

abbrev tracer (P:SOp N)(r:ℕ)(x:Cover)(t:ℝ):ℂ:= Matrix.trace (taxKernel P (wrap N x) r (profile (turntable N t)))
abbrev localLevel (P:SOp N)(x:Cover)(t:ℝ):ℂ:= legTax (P (profile (turntable N t))) (tickA N) (houseW (wrap N x))
lemma hike_local (x:Cover)(P:SOp N) (t:ℝ): localLevel P x t=sprig P (stream N) x t-Matrix.trace ((tickA N)* houseW (wrap N x)):=by
 unfold localLevel legTax; rw [sub_mul,Matrix.trace_sub,house_trace]; rfl

abbrev Stakes (f:ℝ→ℂ)(d:ℝ):Prop:=Bud f ∧ d≤(bud f 2).re
lemma cash_add {f g:ℝ→ℂ}{x y:ℝ}(p:Stakes f x)(q:Stakes g y): Stakes (fun u=>f u+g u) (x+y):=by
 have h:=p.1.bloom.add q.1.bloom; exact ⟨h.1, (add_le_add p.2 q.2).trans_eq (by rw [h.bud_eq]; rfl)⟩
lemma receive_tax (P:SOp N)(x:Cover)(b:ℝ)(r:ℕ)(p:∀ i∈layout r x arcOrder,Stakes (localLevel P i) b):
    Stakes (tracer P r x) ((layout r x arcOrder).length*b):=by
 let G(L:List Cover)(t:ℝ):ℂ:=(L.map fun x=>localLevel P x t).sum
 have hu:tracer P r x=G (layout r x arcOrder):= funext fun y=>tax_stairs r x P _
 rw [hu]
 generalize hx:layout r x arcOrder=L at *
 clear hu hx
 induction L with
 | nil=> have hv:G []=fun _=>0:=rfl; rw [hv,List.length_nil,Nat.cast_zero,zero_mul]; have hz:=_root_.Zephyr.Chern.Bloom.constant 0; exact ⟨hz.1, (le_of_eq (by rw [hz.bud_eq]; rfl))⟩
 | cons i L h=>
    have ht := cash_add (p i List.mem_cons_self) (h fun j l=> p j (List.mem_cons_of_mem _ l)); rw [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul, add_comm];
    rw [show G (i::L)=(fun x=>localLevel P i x+G L x) from funext fun t=>by simp [G]]; exact ht
end coil
end YM.CF.LitCurrent

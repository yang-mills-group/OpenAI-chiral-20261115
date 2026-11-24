import Merino.Salon
import YM.CF.Tye.Spin
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Hem
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n

open Window Buffered StressExchange Dial

def rim (n:Side)(s:Signed):Sweep n:=⟨s,0,detX s⟩
lemma rim_cast (n)(s): castX (rim n s) = (⟨s,0⟩:Shape):=by simp [castX,rim]
def slash (s:Signed):ℝ:=if detX s then -1 else 1
lemma slash_mul (s t:Signed): slash (s*t)=slash s*slash t:=by
 unfold slash; rw [det_p]; cases detX s<;>cases detX t<;>norm_num
def offing (s:Signed): Cover → Cover:=Shape.flee ⟨s,0⟩


lemma millstock (x:Site n): millQ x=Tye.stock (node x):=by
 have hi:Injective (node (N:=n)):=fun _ _ e=>(assembly n).embed_injective (add_right_cancel e)
 ext ⟨⟨y,i⟩,b⟩ ⟨⟨z,j⟩,c⟩
 by_cases hx:y=x <;> by_cases hy:z=x <;> by_cases hu:i=j <;> by_cases hv:b=c <;>
    simp [millQ, panel,Matrix.sum_apply,Matrix.diagonal_apply,Matrix.one_apply,
      Tye.stock, place_x,hi.eq_iff, *, Ne.symm, ite_and]

lemma mill_back (s:Signed)(z:Cover):
    ech (rim n s)⁻¹ (millQ (wrap n z)) =
      millQ (wrap n (offing s z)):=by
 let a:=rim n s
 have hc:boxA a (node (wrap n z))=node (wrap n (offing s z)):=by
   change (castX (rim n s)).anon _ _=_
   rw [rim_cast,←Shape.nodex,Shape.mill,offing]
 have h:=Tye.proM (boxA a) (boxA a).injective a.charge (γS a)
   (fun i j=>Tye.birth_l i j (castX a) _ a.charge) (node (wrap n z))
 rw [hc,←millstock,←millstock] at h
 change ech a _=_ at h
 change ech a⁻¹ _=_
 rw [← h,Sour.paceK,mul_inv_cancel,beat_x]

open Rush Peaks

lemma ech_rev (s:Sweep n)(X:Op (Single n)): ech s⁻¹ (ech s X)=X:=by rw [Sour.paceK,mul_inv_cancel,beat_x]
lemma ech_real (s:Sweep n)(X:Op (Single n)): (ech s X).trace.re=X.trace.re:=by
 unfold ech; rw [singT,trace_twist,win_trace]; cases s.charge <;>rfl
lemma jul_rep (s:Sweep n)(X:SOp n)(V:Pane n): julStep s X (profile V)=ech s⁻¹ (X (profile (flashA s V))):=by
 rw [←julius s X V,ech_rev]
lemma e_sub (s:Sweep n)(X Y:Op (Single n)): ech s (X-Y)=ech s X-ech s Y:=by
 simp [ech]
lemma e_mul (s:Sweep n)(X Y:Op (Single n)): ech s (X*Y)=ech s X*ech s Y:=by simp [ech]

/-- Even on an improper sweep, and even if the AP chart
is cut through the block. -/
lemma full_slide (s:Sweep n)(W:Op (Single n))(V:Pane n)(j:ℕ)(M:Tulip.Male)(h:1≤j)(e:ℝ)
    (H:∀ x:Bkg (More n),Guard x e→ Safe (dome n (profile x))∧∀ M:Tulip.Male,Safe (art n j M.val (profile x)))
    (g:Guard V e):
    julStep s (fun U=>(funde j M n U-tickA n)*W) (profile V) =
      (slash s.s:ℂ) • ((funde j M n (profile V)-tickA n)*ech s⁻¹ W):=by
 let S:=funde j M n (profile (flashA s V))
 have ht:ech s (funde j M n (profile V)-tickA n)=swapX (detX s.s) S-swapX (detX s.s) (tickA n):=by
   rw [e_sub,tick_move]
   exact congrArg (·-swapX _ _) (funde_f (castX s) (xtra s.charge) _
     (spinZ s.charge s.s) V j h M e H g)
 rw [jul_rep,e_mul,← ech_rev s (funde j M n (profile V)-tickA n),ht]
 change ech s⁻¹ (S-tickA n)*_=_
 cases hq:detX s.s
 · simp [swapX,slash,hq]
 have hn:(1-S)-(1-(tickA n))= -(S-tickA n):=by abel
 simp only [slash,hq, swapX,if_true,hn,ech,singT,win_n,map_neg,neg_mul,Complex.ofReal_neg, Complex.ofReal_one,neg_smul,one_smul,neg_neg]

lemma slash_abs (s:Signed): |slash s|=1:=by unfold slash; split<;>norm_num

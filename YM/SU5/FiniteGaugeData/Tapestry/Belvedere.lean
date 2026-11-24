import YM.SU5.FiniteGaugeData.Tapestry.NimbusSpan
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Interval.Finset.Nat
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
/-!
# Linear projection to finish at a chosen resolution

No multiplicativity of `surge` is assumed. Build the projections at any height,
and on the WHOLE ambient (even on heights beyond the chosen resolution, purely
formally). If you're within the height limit, the projection doesn't use the `Pad`
at all. This allows us to compose with a finite observer's budget and proves e.g.
independence of the expression for the product on the indicated subalgebra.
Whatever we extend to the Cloud in these files, ONLY its restrictions to the
subalgebra of resolution polynomials shall be used physically, and further only
at levels where all factors are funded.
-/
namespace YM.CF.Buffered.Afterglow.Tapestry.Altitude
open Function Filter Finset TensorProduct
open scoped BigOperators Classical
open PiTensorProduct (tprod)
variable (A:Type*)[CommRing A][Algebra ℂ A]
variable (E:ℕ→Type*)[∀ i,CommRing (E i)][∀ i,Algebra ℂ (E i)]

structure Decking where
 perceive(i:ℕ): A→ₐ[ℂ] E i
 surge (i:ℕ) : E i→ₗ[ℂ]E (i+1)
 starry (i): surge i 1=1

-- sample auxiliary for unfunded heights. independent from the particular chain.
structure Pad where
 zeroTemp : A→ₗ[ℂ]ℂ
 oneT : zeroTemp 1=1
variable {A E}
variable (n i j:ℕ)(v:Pad A)(f g:ℕ→A)(x y:A)(c:ℂ)
variable (D:Decking A E)
lemma Enough.replace [DecidableEq ℕ] (p:Enough n f)(h:i≤n): Enough n (update f i x):= by
  intro j t; rw [update_of_ne (by omega),p j t]
lemma pref_replace [DecidableEq ℕ]: PreFinite (update f i x) ↔ PreFinite f:=by
  constructor
  · rintro ⟨k,p⟩; apply Exists.intro (max k i)
    intro j t; rw [← (update_of_ne (a:=j) (a':=i) (by omega) x f)]; exact p j (by omega) -- tune order args
  rintro ⟨k,p⟩; exact ⟨max k i, Enough.replace _ i f x (p.taller (le_max_left ..)) (le_max_right ..)⟩ -- field names include D?

namespace Decking
variable {f g}
def finish (D:Decking A E) : (k:ℕ)→(ℕ→A)→ E k | 0,f=> D.perceive 0 (f 0) | k+1,f=> D.surge k (finish D k f)*D.perceive (k+1) (f (k+1))
-- arguments order; unsupported projection uses λ h.
@[simp] lemma finish_one (n): D.finish n 1=1:=by induction n with| zero=> exact map_one _| succ k ih=> rw [finish,ih,D.starry]; change _*D.perceive (k+1) 1=1; rw [map_one,mul_one]
lemma finish_agrees {f g:ℕ→A}(h:∀ i,i≤n → f i=g i): D.finish n f=D.finish n g:=by
  induction n with
  | zero => rw [finish,finish,h 0 le_rfl]
  | succ i ih=> rw [finish,finish,ih (fun j t=>h j (by omega)),h (i+1) le_rfl]
lemma finish_pass [DecidableEq ℕ] {f:ℕ→A} (h:n<i): D.finish n (update f i x)=D.finish n f:=finish_agrees n D fun j t=>update_of_ne (by omega) _ _ -- .. as explicit tune
lemma finish_add [DecidableEq ℕ]{f:ℕ→ A}(p:i≤n): D.finish n (update f i (x+y))=D.finish n (update f i x)+D.finish n (update f i y):=by
  induction n with
  | zero=> rcases Nat.eq_zero_of_le_zero p with rfl; simp [finish]
  | succ n ih=>
    rcases p.eq_or_lt with rfl|h
    · rw [finish,finish,finish, finish_pass n _ (x+y) D (by omega),finish_pass n _ x D (by omega),finish_pass n _ y D (by omega)]; simp [mul_add]
    simp only [finish, update_of_ne h.ne', ih (by omega), map_add,add_mul] -- simp finish rec under n?
lemma finish_scale [DecidableEq ℕ]{f:ℕ→ A}(p:i≤n): D.finish n (update f i (c • x))= c • D.finish n (update f i x):=by
  induction n with
  | zero=> rcases Nat.eq_zero_of_le_zero p with rfl; simp [finish]
  | succ n ih=>
    rcases p.eq_or_lt with rfl|h
    · rw [finish,finish,finish_pass n _ (c • x) D (by omega),finish_pass n _ x D (by omega)]; simp [Algebra.mul_smul_comm]
    simp only [finish,update_of_ne h.ne',ih (by omega),map_smul,Algebra.smul_mul_assoc]

lemma finish_alone (i:ℕ)(v:ℕ→A)(h:∀ n,n<i→v n=1): D.finish i v=D.perceive i (v i):=by
 cases i with
 | zero=>rfl
 | succ n=> rw [finish,D.finish_agrees n (g:=1) (fun x p=>h x (by omega)),finish_one, D.starry, one_mul]
end Decking

-- noncapturing product over the *tail* after `n`. This only concerns linear extensions.
namespace Pad
def fill (v:Pad A)(n j:ℕ)(f:ℕ→ A) : ℂ:= ∏ i∈Finset.Ioc n j, v.zeroTemp (f i)
lemma fill_enough {i j}(u:i≤j)(h:Enough i f): fill v n i f=fill v n j f:= Finset.prod_subset (fun x p=>mem_Ioc.mpr ⟨(mem_Ioc.mp p).1,(mem_Ioc.mp p).2.trans u⟩) fun x a b=> by rw [h x ?_, v.oneT]; exact lt_of_not_ge (fun v=> b (mem_Ioc.mpr ⟨(mem_Ioc.mp a).1,v⟩))
@[simp] lemma fill_one {n}(h:Enough n f): fill v n j f=1:= Finset.prod_eq_one fun x p=>by rw [h x ((mem_Ioc.mp p).1), v.oneT]
lemma fill_constant [DecidableEq ℕ] {n i:ℕ}(h:i≤n): fill v n j (update f i x)=fill v n j f:= Finset.prod_congr rfl fun k p=> by have t:= (mem_Ioc.mp p).1; rw [update_of_ne (by omega)]
-- avoid diamond DecidableEq ℕ in the sum update
lemma fill_success [DecidableEq ℕ] {i j:ℕ}(h:n<i)(p:i≤j): fill v n j (update f i x)= v.zeroTemp x * ∏ k∈ (Finset.Ioc n j).erase i,v.zeroTemp (f k):=by
  unfold fill; rw [← Finset.mul_prod_erase _ _ (mem_Ioc.mpr ⟨h,p⟩),update_self]; apply congrArg; exact Finset.prod_congr rfl fun k p=>by rw [update_of_ne (mem_erase.mp p).1]
lemma fill_add [DecidableEq ℕ](h:n<i)(p:i≤j): fill v n j (update f i (x+y))= fill v n j (update f i x)+fill v n j (update f i y):=by simp_rw [v.fill_success n f _ h p]; rw [map_add,add_mul]
lemma fill_scale [DecidableEq ℕ](h:n<i)(p:i≤j): fill v n j (update f i (c • x))=c*fill v n j (update f i x):=by rw [v.fill_success n f _ h p,v.fill_success n f _ h p,map_smul,smul_eq_mul, mul_assoc]
end Pad

namespace Decking
def watch (D:Decking A E)(v:Pad A)(n:ℕ)(f:ℕ→A) : E n := if h:PreFinite f then v.fill n h.choose f • D.finish n f else 0
lemma watch_paid (h: Enough j f): watch D v n f=v.fill n j f • D.finish n f:=by
  let p:PreFinite f:=⟨j,h⟩; unfold watch; rw [dif_pos p]; apply congrArg (· • D.finish _ _); rcases le_total p.choose j with t|t; exacts [v.fill_enough n f t p.choose_spec,(v.fill_enough n f t h).symm]
lemma watch_absent (h:¬PreFinite f): watch D v n f=0:= dif_neg h
lemma multilinearOne [DecidableEq ℕ]: watch D v n (update f i (x+y))=watch D v n (update f i x)+watch D v n (update f i y):=by
  by_cases h:PreFinite f
  · let u:=max h.choose i; have hu:i≤u:=le_max_right ..; have he(z:A):Enough u (update f i z):= Enough.replace u i f z (h.choose_spec.taller (le_max_left ..)) hu
    simp_rw [D.watch_paid n u v _ (he _)]
    rcases le_or_gt i n with p|p
    · rw [finish_add n i x y D p,smul_add]; simp_rw [v.fill_constant _ _ _ p]
    simp_rw [finish_pass n i _ D p]; rw [v.fill_add n i u f x y p hu,add_smul]
  have ht(z:A):watch D v n (update f i z)=0:=watch_absent n v _ D (mt (pref_replace i f _).mp h)
  simp_rw [ht]; rw [zero_add]
lemma multilinearTwo [DecidableEq ℕ]: watch D v n (update f i (c • x))=c • watch D v n (update f i x):=by
  by_cases h:PreFinite f
  · let u:= max h.choose i; have hu:i≤u:=le_max_right ..; have he(z:A): Enough u (update f i z):= Enough.replace u i f z (h.choose_spec.taller (le_max_left ..)) hu
    rw [watch_paid n u v _ D (he _),watch_paid n u v _ D (he _)]
    rcases le_or_gt i n with p|p
    · rw [finish_scale n i x c D p,v.fill_constant _ _ _ p,v.fill_constant _ _ _ p, smul_comm]
    rw [v.fill_scale n i u f x c p hu, finish_pass n i _ D p, finish_pass n i _ D p, mul_smul]
  have ht(z:A):watch D v n (update f i z)=0:=watch_absent n v _ D (mt (pref_replace i f _).mp h)
  simp_rw [ht]; rw [smul_zero]

def observers : MultilinearMap ℂ (fun _:ℕ=>A) (E n) where
 toFun f:= watch D v n f
 map_update_add' := fun {d f} i x y=> multilinearOne n i v f x y D
 map_update_smul':= fun {d f} i c x=> multilinearTwo n i v f x c D
def crown (D:Decking A E)(v:Pad A) (n:ℕ): Cloud A →ₗ[ℂ] E n := PiTensorProduct.lift (observers n v D)
lemma reckon (h:Enough j f): crown D v n (tprod ℂ f)=v.fill n j f • D.finish n f:= by rw [crown,PiTensorProduct.lift.tprod]; exact D.watch_paid n j v f h
@[simp] lemma reckon_paid {f:ℕ→A}(h:Enough n f): crown D v n (tprod ℂ f)= D.finish n f:= by rw [D.reckon n n v f h, v.fill_one n f h, one_smul]
lemma reckon_unsupported (h:¬PreFinite f): crown D v n (tprod ℂ f)=0:=by rw [crown,PiTensorProduct.lift.tprod]; exact D.watch_absent n v f h
lemma solely (c:Cloud A)(q:c∈shorter A n)(w:Pad A): crown D v n c=crown D w n c:=by
 apply boarded (P:={f| Enough n f}) (M:=fun x=> crown D v n x=crown D w n x) (fun f h=> by rw [reckon_paid _ _ _ h,reckon_paid _ _ _ h]) (by rw [map_zero,map_zero]) (fun x y _ _ u h=>by rw [map_add,map_add,u,h]) (fun z x _ p=>by rw [map_smul,map_smul,p]) q
lemma crown1 (n): crown D v n 1=1:= (reckon_paid _ _ _ (enough1 n)).trans (D.finish_one n)
lemma outcrop (i:ℕ)(x:A): crown D v i (pinhole A i x)=D.perceive i x:=by
  rw [pinhole_apply]; change crown _ _ _ (tprod ℂ (update (1:ℕ→ A) i x))=_; rw [reckon_paid _ _ _ (enough_slot i x),D.finish_alone i (update (1:ℕ→A) i x) (fun n h=>update_of_ne h.ne _ _),update_self]
end Decking
end YM.CF.Buffered.Afterglow.Tapestry.Altitude
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Altitude.Decking.crown1
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Altitude.Decking.solely
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Altitude.Decking.outcrop

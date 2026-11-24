import YM.CF.Mew.Terms
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Drift
open Finset Function
open scoped Topology BigOperators
open Mew
abbrev PairKey (I:Type):= Lex (I× Bool)
abbrev pick {I:Type}(i:I)(k:Bool): PairKey I:=(i,k)
abbrev yard {I:Type}(i:PairKey I):I:=i.1
abbrev altQ {I:Type}(i:PairKey I):Bool:= i.2
variable {I:Type}[Fintype I][LinearOrder I]
local notation "Kb"=> Key (PairKey I)
abbrev entry (k:Bool→ℂ)(i:I)(z:Key (PairKey I)):= k false*z (pick i false)+k true*z (pick i true)
abbrev fiber (C:Bool→Bool→ℂ)(z:Kb):Kb:=fun i=>entry (C (altQ i)) (yard i) z
#print instDecidableEqLex
-- D permitted root set fine.In addition to Hush.Does not look through tag id.$ used pressure.Q.Scope.A
variable {E:Type*}[AddCommGroup E][Module ℂ E]
attribute [-instance] instDecidableEqLex
inductive Grain (D:Finset I): (Key (PairKey I)→E) → Prop
  | zero : Grain D (0: Kb→E)
  | chip (t:Finset (PairKey I))(F:PairKey I→Bool→ℂ)(v:E)(p:t.Nonempty)(ht:Set.InjOn yard (t:Set (PairKey I)))(u:∀ i∈t,yard i∈D):Grain D (fun z=> (∏ i∈t, entry (F i) (yard i) z) • v)
  | add {f g:Kb→E}(p:Grain D f)(u:Grain D g):Grain D (fun z=>f z+g z)
namespace Grain
variable{D:Finset I}{f g:Key (PairKey I)→E}
lemma neg' (p:Grain D f):Grain D (fun z=> -f z):=by
 induction p with
 | zero=>simp only [Pi.zero_apply,neg_zero]; exact zero
 | chip t F v p ht u=>exact (by simpa only [smul_neg] using Grain.chip (D:=D) t F (-v) p ht u)
 | add _ _ ih ip=>exact (by simpa [add_comm] using ih.add ip)
lemma sum' {α:Type*}(s:Finset α)(f:α→ Kb→E)(p:∀ a∈s,Grain D (f a)): Grain D fun z=>∑ i∈s,f i z:=by
 classical
 induction s using Finset.induction_on with
 | empty=>simp only [sum_empty]; exact zero
 | insert i s h ih=> simp_rw [sum_insert h]; exact add (p _ (mem_insert_self ..)) (ih fun a ha=>p _ (mem_insert_of_mem ha))
lemma precomp (p:Grain D f)(C:Bool→Bool→ℂ):Grain D (fun z=>f (fiber C z)):=by
 induction p with
 | zero=>exact zero
 | chip t F v p ht u=>
   let G(i)(k):= F i false*C false k + F i true*C true k
   convert chip (D:=D) t G v p ht u using 1
   ext z
   exact congrArg (· • v) (prod_congr rfl fun i _=>by simp only [fiber,pick,entry,G]; change F i false*(C false false*z (pick i.1 false)+C false true*z (pick i.1 true))+ F i true*(C true false*z (pick i.1 false)+C true true*z (pick i.1 true))=(F i false*C false false+F i true*C true false)*z (pick i.1 false)+(F i false*C false true+F i true*C true true)*z (pick i.1 true); ring)
 | add _ _ l L=>exact add l L
lemma sill (p:Grain D f){z w:Kb}(s:∀ i:I,i∈D→∀ k,z (pick i k)=w (pick i k)): f z=f w:=by
 induction p with
 | zero=>rfl
 | add _ _ x y => change _+_=_+_; rw [x,y]
 | chip t F v _ _ u=> exact congrArg (· • v) (prod_congr rfl (fun i hi=>by unfold entry; rw [s _ (u i hi),s _ (u i hi)]))
abbrev pulse (i:I)(k:Bool)(v:ℂ):Kb:=update (0:Kb) (pick i k) v
abbrev duo (i:I)(a b:ℂ):Kb:= pulse i false a+pulse i true b
@[simp] lemma pulse_self (i:I)(k:Bool)(v:ℂ): pulse i k v (pick i k) = v:= update_self ..
@[simp] lemma pulse_oth (i:I)(k j:Bool)(u:j≠k)(v:ℂ): pulse i k v (pick i j)=0:=update_of_ne (fun h=>u ((congrArg (altQ (I:=I))) h)) ..
@[simp] lemma duo_selfU (i:I)(a b:ℂ): duo i a b (pick i false)=a:=by simp [duo,Pi.add_apply]
@[simp] lemma duo_selfV (i:I)(a b:ℂ): duo i a b (pick i true)=b:=by simp [duo,Pi.add_apply]
lemma entry_off (t o:I)(k:Bool)(p:t≠o)(B:Bool→ℂ)(v:ℂ): entry B t (pulse o k v)=0:=by
 have u (q):pick t q≠pick o k:=fun u=>p (congrArg yard u)
 simp only [entry,pulse,update_of_ne (u _),Pi.zero_apply,mul_zero,add_zero]
lemma mono (D:Bool→ℂ)(t:I)(a b:ℂ):entry D t (duo t a b)=D false*a + D true*b:=by unfold entry; rw [duo_selfU,duo_selfV]
-- Radical support = excluded co-leaf powers. Only first derivative!
lemma radios (p:Grain D f)(t:I)(a b:ℂ): f (duo t a b)=a • f (pulse t false 1) + b • f (pulse t true 1):=by
 induction p with
 | zero=>simp only [Pi.zero_apply,smul_zero,zero_add]
 | add _ _ l k=>
   change _+_= _+_; rw [l,k,smul_add,smul_add,add_add_add_comm]
 | chip q F v p L Q=>
   simp only
   by_cases h: ∃ i∈q,yard i≠t
   · obtain ⟨i,g,k⟩:=h
     have hp(x:ℂ)(j:Bool): entry (F i) (yard i) (pulse t j x)=0:=entry_off _ _ j k ..
     have he:entry (F i) (yard i) (duo t a b)=0:=by
       unfold duo; have h:=hp a false; have e:=hp b true; unfold entry; simp only [Pi.add_apply,mul_add]; rw [add_add_add_comm]; exact (congrArg₂ (·+·) h e).trans (zero_add _)
     rw [Finset.prod_eq_zero g he, Finset.prod_eq_zero g (hp 1 false),Finset.prod_eq_zero g (hp 1 true), zero_smul, smul_zero, smul_zero, zero_add]
   push_neg at h
   obtain ⟨i,hi⟩:=p; have e:q={i}:=Finset.eq_singleton_iff_unique_mem.mpr ⟨hi,fun _ k=> L k hi ((h _ k).trans (h i hi).symm)⟩
   simp only [e,prod_singleton,h i hi,mono,entry]
   simp only [pulse_self, pulse_oth (k:=Bool.false) (j:=Bool.true) _ (by decide), pulse_oth (k:=Bool.true) (j:=Bool.false) _ (by decide),mul_one,mul_zero,add_zero,zero_add,add_smul,smul_smul]; ring_nf
lemma crop (t:I)(x y:ℂ)(j:I)(p:j≠t)(g:Bool):duo t x y (pick j g)=0:=by
 have v(k):pick j g≠pick t k:=fun u=>p (congrArg yard u)
 simp only [duo,pulse,Pi.add_apply,update_of_ne (v _),Pi.zero_apply,zero_add]
lemma singleU(t:I)(k:Bool)(x:ℂ):pulse t k x=duo t (if k then 0 else x) (if k then x else 0):=by
 have h(i:I)(k):pulse i k 0=0:=funext fun j=>by by_cases u:j=pick i k; subst j; rw [pulse_self,Pi.zero_apply]; exact update_of_ne u ..
 cases k<;> simp[duo,h]
lemma rad1(p:Grain D f)(t:I)(k:Bool)(x:ℂ):f (pulse t k x)= x • f (pulse t k 1):=by rw [singleU t k x,radios p]; cases k<;>simp
lemma dawnQ(p:Grain D f): f 0=0:=by
 induction p with
 | zero=>rfl
 | chip q F v p h L=> obtain ⟨i,g⟩:=p; simp only; rw [Finset.prod_eq_zero g (by simp [entry]),zero_smul]
 | add _ _ l k=> change _+_= _; rw [l,k,zero_add]
#print axioms dawnQ
#print axioms sum'
end Grain
end YM.CF.Drift
end

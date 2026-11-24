import Velour.Escutcheon.Frilling
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2800
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


open Boundary Probe
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin


variable {S}{b:Axis}(h:a≠b)
def silk : Cross a:= ⟨basis b,by change basis b a = _;simp [basis,h]⟩
def sewnOut (p:E4):Cross a:= (SEP a p)-(p b) • (silk h)
def sheer (t u:ℝ)(p:E4):E4:=board (silk h) t u (sewnOut h p)

lemma sheer_turn (t u:ℝ)(p:E4): sheer h t u p=sheer h.symm u t p:=by
  change ((p-p a • basis a)-p b • basis b)+u • basis b+t •basis a
    = ((p-p b • basis b)-p a • basis a)+t • basis a + u • basis b
  abel

lemma sheer_self(p:E4):sheer h (p a) (p b) p =p:=by
 change _-(_ • _)-p b •basis b+p b •basis b+p a •basis a=p
 abel

variable (S) in
abbrev Tiles : Type:=Shelf S (silk h)
-- abbrev?


end YM.OS.Semigroup
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis}{S:Semigroup H a}
open Boundary Probe
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

variable {H':Hilbert}{b:Axis}{T:Semigroup H' b}
variable {κ:Type}(L:S.Livery κ)(J:T.Livery κ)
   (h:a≠b)(A:S.Tiles h)(B:T.Tiles (Ne.symm h))
variable {n:ℕ}
local notation "ℓ"=> Fin n→ℝ
local notation "ℒ"=> Fin n→ℂ
local notation "σ"=> Equiv.Perm (Fin n)
variable (u:Fin n→κ)(X:Fin n→E4)
namespace Livery

/-- Axis-side price. g is chronological order indicated as permutation. -/
def penny (g:σ)(z w:ℒ):ℂ:=
 L.bay (silk h) A (u ∘ g) (z ∘ g) (w ∘ g) ((sewnOut h ∘ X)∘g)
local notation "R"=>L.penny h A u X
local notation "Q"=>J.penny h.symm B u X

def posed (s v:ℓ): Fin n→E4:=fun i=>sheer h (s i) (v i) (X i)
lemma posed_turn (s v:ℓ):
 posed h X s v=posed h.symm X v s:= funext fun _=>sheer_turn ..

lemma free_cut (s:ℓ)(i:Fin n)(v:ℓ): posed h X s v i a=s i :=
 bclock ..

lemma stamps (g:σ)(s v:ℓ)
 (p:StrictMono (s ∘ g)):
 R g (soaked s) (soaked v)= L.glade (u∘g) ((posed h X s v)∘g) (Each n):=
   (meanR S L.Ω.val (silk h) A ((sewnOut h ∘ X)∘g)
    (L.G ∘ u ∘ g) (L.m ∘ u ∘ g) (s ∘ g) (v ∘ g)
    L.vacU p).symm

lemma swap_coin (P:Pact L J)(g f:σ)(s v:ℓ)
 (p:StrictMono (s ∘ g))(r:StrictMono (v ∘ f)):
 R g (soaked s) (soaked v)= Q f (soaked v) (soaked s):=by
 rw [L.stamps h A u X g s v p,J.stamps h.symm B u X f v s r, ←posed_turn h X s v]
 apply P
 · simp_rw [free_cut]; exact p
 rw [posed_turn]; simp_rw [free_cut]; exact r

lemma neat {s:ℓ}{g f:σ}
    (p:StrictMono (s ∘ g))(r:StrictMono (s ∘ f)): g=f:=by
 let e:=f.symm ∘ g
 have y:StrictMono e:=by
    intro i j a
    apply r.lt_iff_lt.mp
    simpa [e] using p a
 ext1 x
 have t:e x=x:= le_antisymm (y.le_id _) (y.id_le _)
 simpa only [e,comp_apply,Equiv.apply_symm_apply] using congrArg f t



variable (g:Equiv.Perm (Fin n))
def Chipped (g:σ)(d E:ℝ)(z w:ℒ):=
 Flourish d E (z ∘ g) (w ∘ g)

lemma shellac (d:ℝ)(e:0<d):
 ∃c:ℝ,0<c∧∀N:ℝ,1≤N → ∀z w:ℒ,Chipped g d N z w→
   ‖R g z w‖≤ c*N^(L.modes u):=by
 obtain ⟨c,p,y⟩:= L.marge (silk h) A (u ∘ g) d e
 rw [L.modes_order] at y
 exact ⟨c,p,fun _ q _ _ t=>y _ q _ _ t _⟩

lemma Chipped.pay {g:σ}{d E:ℝ}{z w:ℒ}
 (v:Chipped g d E z w)(p:0<d)(y:0<E): Radial (z ∘ g) (w ∘ g):=
   fun _ _ t=>sub_pos.mp (pos_of_mul_pos_right (p.trans_le (v _ _ t)) y.le)

lemma penny_marble (z w:ℂ→ℒ)(r:ℂ)
    (p:Radial (z r ∘ g) (w r ∘ g))
    (t:∀i,AnalyticAt ℂ (fun u=>z u i) r)(v:∀i,AnalyticAt ℂ (fun u=>w u i) r):
 AnalyticAt ℂ (fun u'=> R g (z u') (w u')) r:=
   mellA S _ _ _ _ _ (fun j=> z j ∘ g) (fun j=>w j ∘ g) (fun _=> L.G ∘ u ∘ g) _
        p (fun _=>t _) (fun _=>v _) (fun _=>analyticAt_const)
#print axioms shellac
#print axioms penny_marble
#print axioms swap_coin


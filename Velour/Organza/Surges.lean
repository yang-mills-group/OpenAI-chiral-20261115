import Velour.Organza.Muslin
/-!
Graph convergence *stable under forming words*. Principle will apply twice:
width first (fixed heat, actual smeared prices), padding removal second
(continuum prices).
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight

def Surges {ι:Type} (p:Filter ι) (f:ι→Module.End ℂ D) (x:Module.End ℂ D) : Prop:=
 ∀ v:ι→D, ∀ w, S.Ruffles p v w → S.Ruffles p (fun i=> f i (v i)) (x w)

namespace Surges

variable {S}
variable {ι : Type} {p:Filter ι}
variable {f g : ι→Module.End ℂ S.muslin} {x y : Module.End ℂ S.muslin}

lemma at_one (h:S.Surges p f x)(w:D): S.Ruffles p (fun i=>f i w) (x w):= h _ _ (Ruffles.lean_on _)
lemma mul (h:S.Surges p f x)(k:S.Surges p g y):
 S.Surges p (fun i=>f i*g i) (x*y):= fun _ _ l=>h _ _ (k _ _ l)
@[simp] lemma one : S.Surges p (fun _=>1) 1:=fun _ _ h=>h

lemma consent (h:S.Surges p f x)(e:f=ᶠ[p] g):
 S.Surges p g x:= by
   intro v w k n
   exact (h _ _ k n).congr' (e.mono fun i l=>by dsimp only; rw [l])

lemma per_word {κ:Type} {F: κ→ι→Module.End ℂ S.muslin} {X:κ→Module.End ℂ S.muslin}
   (l:List κ) (h:∀b∈l, S.Surges p (F b) (X b)):
 S.Surges p (fun i=>(l.map (fun b=>F b i)).prod) (l.map X).prod:=by
 induction l with
 | nil=> exact one
 | cons z l ih=>
   simp only [List.map_cons,List.prod_cons]
   exact (h _ (List.mem_cons_self ..)).mul (ih fun b t=>h b (List.mem_cons_of_mem _ t))

lemma idle (g:∀n,∃m T,S.Refines x m n T):
 S.Surges p (fun _=>x) x:=fun _ _ h=>h.reach _ g
end Surges

variable {ι:Type} {p:Filter ι}
lemma surges_warm {d:ι→ℝ≥0} (e:Tendsto d p (𝓝 0)):
  S.Surges p (fun i=> S.heatL (d i)) 1:=fun _ _ h=>Ruffles.warm S h e

#print axioms Surges.per_word
#print axioms Surges.consent


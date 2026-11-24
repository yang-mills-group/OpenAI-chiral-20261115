import Merino.Corolla.Stems

set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 360000
noncomputable section
namespace YM.CF.Merino.Corolla
open Finset Lattice RG Scree Skye Vow
open scoped Topology Classical Matrix Matrix.Norms.L2Operator
open Cadre Sour Push.AbsoluteSums.Trees Vow.TreasuryFog

open Neon Py Mew Stax Rill Cube

open Bake Roots Push.AbsoluteSums
variable {N B:Side}{I:Type}[LinearOrder I][Fintype I]
variable {n:Side}{P:BudgetPoint}{h a b w:ℝ}{q L:ℕ}
def long (P:BudgetPoint)(L:ℕ)(y:Bag n):Prop:=∀ X, (coverNumber P.B X.val)^3 < L → y X=0
lemma markLong(o:Seat n)
  (sz:2*(postL L*P.B)<(More n).val)
  {y:Bag n}
  (v:Barrage P q (guardX P o L).val h y (eighth P.B) a b):
  long P L y := by
  obtain ⟨_,_,_,p,_⟩:=v.price
  intro X t
  apply (p X ?_).1
  intro u
  have hv:=railgo P o L X u sz
  exact (not_le.mpr t) (hv.trans (Nat.le_self_pow (show (3:ℕ)≠0 from by decide) _)) -- check lemma
local notation "M"=>mid N B
variable {o:I→Site (mid N B)}{y:I→Bag (mid N B)}
variable {c d:I→Aura (mid N B)→ℝ}
lemma rest (k:Sep P q h (node ∘ o) y c d)(i:I)(l:long P L (y i))(τ:Ids M)(X:Scree.Hub M)
   (p:Moto.chose L P X):
   stems k τ i X=0 :=by
 unfold stems; split; swap; rfl

 have z:=l (lagE X) p
 have eg:Bias.αt (lagE X) (lagE X) ∅ (cipherK q):=⟨le_rfl, empty_subset _,by simp [Lattice.halo]⟩
 funext v; apply Subtype.ext; unfold nerve
 rw [(k.biasH i).truth _ _ _ _ eg, z]; simp [coll_T,Sault.rind]

theorem crowned (k:Progress P q h (node∘o) y c d a b)
 (t:P.supportExponent≤1)(u:3≤P.B)(v:0≤h)(i:I)
 (l:long P L (y i))(τ:Ids M)(m:nectar P*b ≤ w):
    Axon L (o i) P (stems k.toSep τ i) h w 0:=by
 refine ⟨?_,fun j p=>if_neg p,fun j p=>?_⟩
 · obtain ⟨⟨f,r,s⟩,z⟩:=hive k.toSep τ i u v t
   exact ⟨⟨f,r,fun x=> (s x).trans ((mul_le_mul_of_nonneg_left (k.wedge i).2 (nectar_n _)).trans m)⟩,z⟩
 rw [rest _ _ l _ _ p,ite_self]
 have e:= Moto.stillQ (o i) P
 exact ⟨e.1,Prod.ext e.2.1 e.2.2⟩

def sluice (P:BudgetPoint)(z:Seat n)(b:Bag n):Prop:=
  ∀X:Aura n,X.val⊆arbour P z → b X=0
lemma flush (z:Seat n)(L:ℕ)
 (sz:2*(postL L*P.B)<(More n).val)
 {y:Bag n}
 (v:Barrage P q (guardX P z L).val h y (eighth P.B) a b):
 sluice P z y:= by
 obtain ⟨_,_,_,p,_⟩:=v.price
 exact fun _ t=>(p _ fun r=>beyond P z L sz (r.trans t)).1

def brim (P:BudgetPoint)(x:Seat n)(e:RegBudget n): Prop:=
  ∀j:Scree.Hub n,j.val.2⊆arbour P x →e j=0
lemma hemmed (k:Sep P q h (node ∘ o) y c d)(i:I)
 (g:sluice P (node (o i)) (y i))(τ:Ids M):
 brim P (node (o i)) (stems k τ i):=by
 intro X p
 unfold stems; split; swap; rfl
 have z:=g (lagE X) p
 have eg:Bias.αt (lagE X) (lagE X) ∅ (cipherK q):=⟨le_rfl, empty_subset _,by simp [Lattice.halo]⟩
 funext v; apply Subtype.ext; unfold nerve
 rw [(k.biasH i).truth _ _ _ _ eg, z]; simp [coll_T,Sault.rind]

end YM.CF.Merino.Corolla

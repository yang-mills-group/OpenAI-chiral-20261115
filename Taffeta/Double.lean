import Taffeta.Taper
import Taffeta.Fissure
-- duplicate name import Sparkle.Gaps to use
import Sparkle.Gaps
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Mew
open Drift Py.Dyad Function Finset Metric Set
variable {I:Type}[Fintype I][LinearOrder I]
attribute [-instance] instDecidableEqLex
local notation "P"=>PairKey I
def strip (b:P):P:= pick b.1 false
abbrev bill (l:List P):List P:=l.map strip -- local notation lemma l expansion.D.Card.
def portal (L:Finset P)(i:I):P:= if pick i false∈L then pick i false else pick i true
def agentX (L:Finset P)(i:P): Option P:=if i.2 then none else some (portal L i.1)
lemma div_X(L:Finset P)(i j:P)(h:agentX L i=some j):strip j=i:=by
 unfold agentX at h; split at h; contradiction; rename_i e; have ht:i.2=false:=Bool.eq_false_iff.mpr e; have hp:=Option.some_inj.mp h
 unfold strip; rw [←hp,portal]; split<;> exact Prod.ext rfl ht.symm
lemma port_i(L:List P)(h:(L.map yard).Nodup): Set.InjOn (yard:PairKey I→I) (L.toFinset:Set P):=by
 -- lemma list_nodup_map_iff_injOn
 induction L
 case nil=> simp
 case cons i l ih=>
    obtain ⟨hw,h⟩:= List.nodup_cons.mp h
    intro x hx y hy p; simp only [Finset.mem_coe,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset] at hx hy
    rcases hx with rfl|a <;> rcases hy with rfl|b
    · rfl
    · exact (hw (p.symm ▸ List.mem_map_of_mem b)).elim -- naming hw type due replacing y? check
    · exact (hw (p ▸ List.mem_map_of_mem a)).elim
    exact ih h (List.mem_toFinset.mpr a) (List.mem_toFinset.mpr b) p
lemma navG(L:List P)(h:(L.map yard).Nodup)(i:P)(u:i∈ L): agentX L.toFinset (strip i)=some i:=by
 unfold agentX strip; change (if false=true then none else some (portal L.toFinset i.1))=some i
 simp only [Bool.false_eq_true,↓reduceIte,Option.some_inj]
 unfold portal; split
 next t=> exact port_i L h t (List.mem_toFinset.mpr u) rfl
 next t=> cases he:i.2; · exact (t ((Prod.ext (β:=Bool) rfl he : (i:I×Bool)=pick i.1 false) ▸ List.mem_toFinset.mpr u)).elim
          exact Prod.ext rfl he.symm
lemma port_s(L:List P)(h:(L.map yard).Nodup)(z:Key P)(p:sparse L.toFinset z): fiber duplicate z=channel (agentX L.toFinset) z:=by
 funext i; cases ht:i.2; swap
 · rw [voidMl _ _ _ (show agentX L.toFinset i=none from (by simp [agentX,ht]))]; simp [fiber,Drift.entry,duplicate,altQ,ht]
 let a:=i.1
 let j(k):=pick a k
 rw [relay _ _ _ (show agentX L.toFinset i=some (portal L.toFinset a) by simp [agentX,ht,a])]; unfold fiber entry duplicate; simp only [altQ,ht,Bool.false_eq_true,↓reduceIte,one_mul]; change z (j false)+ z (j true) = z (portal _ _)
 unfold portal; split
 next v=> have hv:j true∉ L.toFinset:=fun e=> Bool.noConfusion (congrArg altQ (port_i L h (show j false∈ (L.toFinset:Set P) from by exact v) (show j true∈(L.toFinset:Set P) from e) (show yard (j false)=yard (j true) from rfl))); rw [p _ hv,add_zero]
 next v=> rw [p _ v,zero_add]
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
lemma terseQ(L:List P)(h:(L.map yard).Nodup)(f:Key P→E):tipI (fun z=>f (fiber duplicate z)) L=tipI f (bill L):=(tip_sparse L _ _ (t:=fun z p _=> congrArg f (port_s L h z p))).trans (tip_relay _ strip (div_X _) L f (navG L h))
-- Full formula ``divide`` using reduced support. Cong lemma for subset lists
lemma divide_C(c:P→ℂ)(L:List P)(f g: List P→ℂ)(p:∀ l:List P,l.Sublist L→f l=g l):divide c L f=divide c L g:=by
 induction L generalizing f g with
 | nil=>exact p [] (.refl _)
 | cons i L ih=>
   unfold divide; exact congrArg₂ (·+·) (congrArg (c i • ·) (ih _ _ (fun l h=>p l (.cons i h)))) (ih _ _ (fun l h=>p _ (.cons_cons i h)))
lemma seize_T (c:P→ℂ)(L:List P)(p:(L.map yard).Nodup)(f:Key P→ℂ)(h:River f): tipI (fun z=> abrupt c z * f (fiber duplicate z)) L=divide c L (fun s=>tipI f (bill s)):=by
 let g:Key P→ℂ:=fun z=> f (channel (agentX L.toFinset) z)
 have hv:River g:= river_relay _ strip (div_X _) _ h
 refine (tip_sparse L _ (abrupt c * g) (fun z p_ _=> congrArg (fun Q=> abrupt c z* f Q) (port_s L p z p_))).trans ((tip_abrupt c g hv L (.of_map _ p)).trans ?_)
 exact divide_C c L _ _ (fun l h=> tip_relay _ strip (div_X _) l _ (fun i hi=> navG L p _ (h.subset hi)))
#print axioms seize_T
end YM.CF.Mew
end

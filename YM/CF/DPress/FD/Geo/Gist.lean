import YM.CF.DPress.FD.Geo.Gest
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Finset Cash Bifold Deck Hue
open scoped Topology BigOperators ENNReal NNReal Classical
variable {n:Side} {q l m F:ℕ} {i j:Site n}
namespace Geo
variable (c:ColorT q n) (D W:Support n)
abbrev Score (l t:ℕ):Prop:=2*l ≤ t ∧ t≤ 4*l
abbrev NormW(n:Side):=Site n→ℕ
abbrev Advise(f:NormW n)(l m:ℕ)(c:ColorT q n)(D:Support n)(i:Site n)(w:ℕ):Prop:= Score l w ∧ ∀ j∈D, close l i j→ c j<c i → Agree m i j w (f j)
def fly (f:NormW n)(l m:ℕ)(c:ColorT q n)(D:Support n)(i:Site n):ℕ := if h:∃ t:ℕ, Advise f l m c D i t then Nat.find h else 0
def jitter (D:Support n)(c:ColorT q n)(l m:ℕ):ℕ→ NormW n
| 0=> fun _=> 0
| k+1=> fun i=> if (c i).val=k then fly (jitter D c l m k) l m c D i else jitter D c l m k i
lemma fly_t{f g:NormW n}{c e:ColorT q n}{i j: Site n}{D W:Support n}(p: ∀ k:ℕ, Advise f l m c D i k↔ Advise g l m e W j k): fly f l m c D i=fly g l m e W j:=by
 have he: (fun k=>Advise f l m c D i k)=(fun k=>Advise g l m e W j k):=funext fun k=> propext (p k); unfold fly; by_cases h: ∃ k, Advise f l m c D i k; swap
 · rw [dif_neg h,dif_neg (fun t=> h ((exists_congr p).2 t))]
 have hp: ∃ x, Advise g l m e W j x:= (exists_congr p).mp h; rw [dif_pos h,dif_pos hp]; exact (Nat.find_eq_iff _).mpr ⟨(p _).2 (Nat.find_spec hp),fun i t v=>Nat.find_min hp t ((p i).1 v)⟩ -- statement p part Nat.find_eq_* orientation?
variable (e:ColorT q n)
abbrev sees {I:Type*}[Fintype I] [DecidableEq I] (X Y:Finset I)(F:Set I):Prop:=∀ i ∈F, (i∈ X↔ i∈Y)
local notation "F'"=> fly
lemma seesP {I:Type*}[Fintype I][DecidableEq I]{X Y:Finset I}{F G:Set I}(h:F⊆ G)(p:sees X Y G):sees X Y F:= fun i t=> p i (h t)
lemma self_z (u:ℕ): i∈ cell n i u:= (cellP ..).2 (by simp)
lemma cell_z (i j:Site n): close l i j ↔ j∈cell n i (s10 l):= (cellP ..).symm
lemma fly_v {f g:NormW n} (p: sees D W (cell n i (s10 l)))(h:Set.EqOn f g (cell n i (s10 l)))(u:Set.EqOn c e (cell n i (s10 l))) : fly f l m c D i=fly g l m e W i:=by
 apply fly_t; intro w; unfold Advise; apply and_congr_right; intro _
 constructor
 · intro x j v hP; have hl:= (cell_z (l:=l) i j).1 hP; rw [← u (self_z _),← u hl,← h hl]; exact x _ ((p j hl).2 v) hP
 intro x j v hP; have hl:= (cell_z (l:=l) i j).1 hP; rw [u (self_z _),u hl,h hl]; exact x _ ((p j hl).1 v) hP
local notation "Y"=> jitter
lemma jitterP(k:ℕ)(t: sees D W (↑(cell n i (k*s10 l)):Set _))(u:Set.EqOn c e (cell n i (k*s10 l))) : Y D c l m k i=Y W e l m k i:=by
 induction k generalizing i with
 | zero=>rfl
 | succ k h=>
   let C:= cell n i ((k+1)*s10 l); let S:=cell n i (s10 l); have hv:S⊆ C:= scene _ _ (by rw [add_mul,one_mul]; omega); have hp:=Finset.coe_subset.mpr hv
   have he: Set.EqOn (Y D c l m k) (Y W e l m k) S:=by
     intro j v; have ht: cell n j (k*s10 l)⊆ C:= by unfold C; rw [add_mul,one_mul]; exact closer ((cell_z ..).mpr v)
     exact h (seesP (Finset.coe_subset.mpr ht) t) (u.mono (Finset.coe_subset.mpr ht)) -- implicit induction i
   unfold jitter; rw [show c i=e i from u (self_z _)]; split; · exact fly_v c D W e (seesP hp t) he (u.mono hp)
   exact he (self_z _)
lemma jitterR(k:ℕ)(s:Signed)(x:Site n)(h:2*s10 l<n.val)(p:c=e ∘ aura s x)(v:∀ i: Site n,i∈D↔ aura s x i∈W):Y D c l m k i=Y W e l m k (aura s x i):=by
 induction k generalizing i with
 | zero=>rfl
 | succ k ih=>
   let V:=aura s x; have ht(i):c i=e (V i):=congrFun p i; unfold jitter; rw [ht i]; split; swap; · exact ih
   apply fly_t; intro w; unfold Advise; apply and_congr_right; intro _; constructor
   · intro t j q hg; obtain ⟨j,rfl⟩:= V.surjective j; intro r; have he:close l i j:=(around s x i j).symm.trans_le hg; change Agree _ (aura s x i) (aura s x j) w _; rw [←ih (i:=j)]; apply (agree_rot he h s x).2; exact t _ ((v _).2 q) he (by rw [ht i,ht j]; exact r) -- rw ih
   intro t j q he v'; apply (agree_rot he h s x).1; rw [ih]; apply t _ ((v _).1 q) ((around s x i j).trans_le he); rwa [ht i,ht j] at v'
variable {k:ℕ}
abbrev WinsC (m l:ℕ)(F:ℕ):Prop:= 0<m∧m≤ l∧ pack 10≤F∧ Wide F m l
lemma advise (f: NormW n)(p:WinsC m l F)(t:Lonely D l)(i:Site n): Advise f l m c D i (fly f l m c D i):=by
 let A:=D ∩ cell n i (s10 l); have hv:A.card ≤ F:= (bill l _ (p.1.trans_le p.2.1) D t i).trans p.2.2.1; obtain ⟨v,x,y,w⟩:= loan F p.1 p.2.2.2 A hv f i; have he:∃ s, Advise f l m c D i s:= ⟨v,⟨x,y⟩,fun j u t _=>w _ (mem_inter.mpr ⟨u,(cell_z (l:=l) i j).1 t⟩)⟩; rw [fly,dif_pos he]; exact Nat.find_spec he
lemma known (p: (c i).val < k) : Y D c l m (k+1) i=Y D c l m k i:=if_neg p.ne
-- after color v the final width satisfies Advise
lemma advise_end (i:Site n)(p:WinsC m l F)(t: Lonely D l)(h:(c i).val < k) : Advise (Y D c l m k) l m c D i (Y D c l m k i):=by
 induction k with
 | zero=>omega
 | succ k ih=>
   let g:=Y D c l m k; have he (j:Site n)(v:c j<c i) : Y D c l m (k+1) j=g j:= known c D (by have he:(c j).val<(c i).val:=v; omega)
   by_cases v:(c i).val=k; swap; · have ht:(c i).val<k:=(by omega); rw [known c D ht]; exact ⟨(ih ht).1,fun j x q t=>he j t ▸ (ih ht).2 j x q t⟩ -- rw known accidental initial application (Y not app first) tactic
   let w:=fly g l m c D i; have ht: Y D c l m (k+1) i=w:=if_pos v; have hv:= advise c D g p t i; rw [ht]; exact ⟨hv.1,fun j x q t=>he j t ▸ hv.2 j x q t⟩
lemma agree_end (p:WinsC m l F)(t: Lonely D l)(u: Tight c l)(y: i∈D)(x:j∈D)(e:i≠j)(r: close l i j)(z:2*s10 l<n.val) : Agree m i j (Y D c l m q i) (Y D c l m q j):=by
 cases lt_or_gt_of_ne (u _ _ e r) with
 | inl h=> apply agreeV (show close l j i from (separation_comm ..).trans_le r) z; exact (advise_end c D j p t (c j).isLt).2 _ y ((separation_comm ..).trans_le r) h
 | inr h=> exact (advise_end c D i p t (c i).isLt).2 _ x r h
end Geo
end YM.CF.DPress.FD

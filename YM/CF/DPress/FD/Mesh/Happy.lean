import YM.CF.DPress.FD.Mesh.Bloom
import YM.CF.DPress.FD.Law.Sat
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Finset Cash
open scoped Topology BigOperators ENNReal NNReal Classical
variable {n:Side} {r k:ℕ}
open Bifold Deck
namespace Hue
variable {d:ℕ}(m:2*Koran d r<n.val)(p:sizeQ≤ d)
local notation "L"=> Site n
local notation "Or"=> Equiv.Perm (Site n)
abbrev Smile (n:Side):= (Support n)→ Equiv.Perm (Site n)
abbrev Theatre (m:2*Koran d r<n.val):= Deck.X m × Smile n -- implicit d,r infer
abbrev Moon(m:2*Koran d r<n.val):Vision n (Koran d r) (Theatre m) := (Role m).pair (Sat.pool _ Sat.key _)
variable (V: Theatre m)
private def kn(s:Equiv.Perm (Site n)):Equiv.Perm (Equiv.Perm (Site n)):= Equiv.mulRight s -- Perm notation multiplication? mathlib (s*t) x=s(t x) . rank map -> original.
lemma kn_v(s a:Equiv.Perm (Site n)) (i:Site n): kn s a i= a (s i):=rfl
abbrev role(s:Signed)(x:Site n): Equiv.Perm (Theatre m):= Equiv.prodCongr (light m s x) (Sat.bonus (Sat.hull (aura s x)) (fun i=> kn (aura s x)))
lemma γ_m (s:Signed)(x:Site n) : Chooses (Moon m).c (role m s x):= by intro i; apply congrArg₂ (·*·) (Deck.w_L m s x i.1) (Sat.chooseB (Koran d r) Sat.key _ i.2) -- tune
abbrev pr(V:Smile n)(t:Support n) (i:Site n):= Fintype.equivFin L ((V t) i) -- parse
abbrev timbres (V:Smile n)(t:Support n)(i:Site n) := t.filter fun j=> pr V t j< pr V t i
abbrev unitK (V:Smile n)(t:Support n)(i:Site n):= (timbres V t i).card
-- cost cardinal < cos.K.
lemma sees_p{t:Support n}(Y V:Smile n)(x:Y t=V t)(i: Site n): unitK Y t i=unitK V t i:=by unfold unitK timbres pr; rw [x]
lemma pocket (V:Smile n){t:Support n}{i:Site n}(v:i∈ t) : unitK V t i < t.card:=by refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _,?_⟩); intro h; have hg:=h.symm ▸ v; apply lt_irrefl (pr V t i); exact (Finset.mem_filter.mp (show i∈ _ from hg)).2
lemma rank_z(V:Smile n){t:Support n}{i j:Site n}(v:i∈t)(h:pr V t i < pr V t j) : unitK V t i < unitK V t j :=by
 refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨fun x w=> Finset.mem_filter.mpr ⟨(mem_filter.mp w).1,lt_trans (show pr V t x<_ from (mem_filter.mp w).2) h⟩,?_⟩)
 intro w; have he:i∈timbres V t i:= w ▸ mem_filter.mpr ⟨v,h⟩; exact lt_irrefl _ ((mem_filter.mp he).2)
abbrev Vcolor(d r:ℕ):= Finset (Deck (Koran d r)) × Fin d -- instead of size κ
abbrev κV(i:Site n):= heap m V.1 i
local notation "Dx"=>ψ m V.1
include p
abbrev kappa (v:Site n) : Vcolor d r:= (Dx v,⟨unitK V.2 (heap m V.1 v) v,(pocket V.2 (head (Dx) d)).trans_le (compact m V.1 p _)⟩) -- p is arg in statement via explicit? abbrev proof field.Lean may omit.
lemma different (i j:Site n)(g:i≠j)(w:separation i j≤r):kappa m p V i≠kappa m p V j:=by
 intro t; have h:Dx i = Dx j:=congrArg Prod.fst t; have k:=congrArg (fun x:Vcolor d r=> x.2.val) t; let f:=heap m V.1; have he:f i=f j:= herd m V.1 p ⟨w,h⟩; change unitK V.2 (f i) i=unitK V.2 (f j) j at k; rw [←he] at k; have hv: j ∈ f i:= he ▸ head Dx d
 have hp:pr V.2 (f i) i=pr V.2 (f i) j:= Classical.byContradiction fun q=> ?_; exact g ((V.2 (f i)).injective ((Fintype.equivFin _).injective hp)) -- tune alternatives
 cases lt_or_gt_of_ne q with
 | inl h=> exact (rank_z V.2 (head Dx d) h).ne k
 | inr h=> exact (rank_z _ hv h).ne' k
lemma readκ(i:Site n)(Y: Theatre m)(h:(Moon m).looks (cell n i (d*r)) V Y): kappa m p V i= kappa m p Y i:=by
 let S:= cell n i (d*r); let D:= heap m Y.1 i; have hp:D.Nonempty:= ⟨i,head (ψ m Y.1) d⟩; have he : heap m V.1 i=D:= comp_cost m V.1 Y.1 i h.1; have hv:d*(1:ℕ)*r=d*r:=by ring
 refine Prod.ext (congrArg pal (sees m S V.1 Y.1 h.1 i ((cellP ..).2 (by simp)))) (Fin.ext ?_); change unitK V.2 (heap m V.1 i) i=unitK Y.2 D i; rw [he]; apply sees_p V.2 Y.2 _; exact Sat.single_p _ V.2 Y.2 D ((cellP ..).mpr ((side_C (ψ m Y.1) d (Sat.key D) (Sat.tithe D hp)).2)) h.2
lemma movement(s:Signed)(x:Site n)(i:Site n): kappa m p (role m s x V) i= kappa m p V (aura s x i):=by
 let l:= aura s x; let T:= role m s x V; let U:= heap m T.1 i; let J:= heap m V.1 (l i); have h:U.image l=J:= transportT m V.1 i s x; refine Prod.ext (lightT ..) (Fin.ext ?_)
 have hp(x): pr T.2 U x=pr V.2 J (l x):= by change Fintype.equivFin L (kn l (V.2 (Sat.hull l U)) x)=_; rw [Sat.eqV,h,kn_v]
 change unitK T.2 U i= _; change _=unitK V.2 J (l i); let D:=timbres T.2 U i
 have hv:D.image l=timbres V.2 J (l i):=by ext j; obtain ⟨j,rfl⟩:= l.surjective j; rw [mem_filter,←hp,←hp,←h]; simp [D,timbres] -- loops
 unfold unitK; rw [←hv]; exact (Finset.card_image_of_injOn l.injective.injOn).symm -- tune
end Hue
end YM.CF.DPress.FD

import Bay.D.Skin
import Zephyr.Chern.Decay
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff

variable {N:Side}{o:Seat N}{k:ℕ}
abbrev alpha:ℝ:=1+(Fintype.card Pureton:ℝ)
lemma ton : (0:ℝ)<alpha:=by unfold alpha;positivity
lemma cardM : (↑(Lagoon k o).card:ℝ) ≤ alpha*(8*(1+(k:ℝ)))^4:=by
 have h: (roost (k+3) o).card ≤ ((k+3)+(k+3)+1)^4:=by simpa only [card_singleton, one_mul] using Corona.halo_size {o} (k+3)
 have l: (↑(roost (k+3) o).card:ℝ) ≤ (8*(1+(k:ℝ)))^4:=by
   exact_mod_cast (h.trans (Nat.pow_le_pow_left (by omega : k+3+(k+3)+1 ≤8*(1+k)) _))
 rw[Lagoon,fen,card_product,card_univ,Nat.cast_mul,mul_comm alpha]
 have hn:0≤(Fintype.card Pureton:ℝ):=Nat.cast_nonneg _
 exact mul_le_mul l (by unfold alpha;linarith) hn (by positivity)

/-- Price scale (units of rent). -/
structure Calcite(a d D r V:ℝ) : Prop extends Twine 3 d D r where -- syntax?
 earn:D≤ V
 age:0<a
 big:{N:Side}→(S:Sa N)→2*alpha^2*D*(8*(1+(S.card:ℝ)))^10 ≤ V*Branch.rent a S

variable {a d D V r:ℝ}
lemma calcites (u:0<a)(h:0<d):∃ D r V,Calcite a d D r V:=by
 obtain ⟨D,r,q⟩:=twining 3 h
 obtain ⟨t,ht,hu⟩:=Zephyr.Chern.poly _ 10 u
 let v:=2*alpha^2*D*8^10
 have hv:0<v:=by unfold v;have := ton;have:=q.dp;positivity
 refine ⟨D,r,max D (v*t),⟨q,le_max_left ..,u,fun {N} S=>?_⟩⟩
 have hd:=hu (S.card:ℝ) (Nat.cast_nonneg _)
 calc
   _ = v*(1+(S.card:ℝ))^10:=by unfold v; rw[mul_pow];ring
   _ ≤ (v*t)*Branch.rent a S:= (mul_le_mul_of_nonneg_left hd hv.le).trans_eq (mul_assoc ..).symm
   _ ≤ _:=mul_le_mul_of_nonneg_right (le_max_right ..) (Real.exp_pos _).le
namespace Calcite
lemma pos(q:Calcite a d D r V):0<V:=q.dp.trans_le q.earn
lemma dust(q:Calcite a d D r V){S:Sa N}:
    melt D S.card ≤ V*Branch.rent a S ∧
    2*melt D S.card*(Lagoon S.card o).card^2≤ V*Branch.rent a S:=by
 let w:ℝ:=8*(1+S.card)
 have hd:=q.dp
 have ha:1≤2*alpha^2:=by unfold alpha; nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card Pureton)]
 have hw:1≤w:=by unfold w; linarith [Nat.cast_nonneg (α:=ℝ) S.card]

 constructor
 · apply le_trans _ (q.big S)
   change D*w^2 ≤ _ *w^10
   exact mul_le_mul (le_mul_of_one_le_left hd.le ha) (pow_le_pow_right₀ hw (by decide)) (by positivity) (by positivity)
 apply le_trans _ (q.big S)
 refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) cardM 2) (show 0≤2*melt D S.card by unfold melt; positivity)).trans_eq ?_
 unfold melt; ring

end Calcite

variable {p:BudgetPoint}
structure Shallow(p:BudgetPoint)(k:ℕ)(N:Side)(r:ℝ):Prop where
 paid:k+1≤p.B
 period:2*(k+1)<(More N).val
 quick:frosty k p.threshold ≤ iceR r

variable {F:Plank N d}{S:Sa N}{C:Toll (Single N)}
lemma rind
    (h:Calcite a d D r V)(l:Shallow p k N r)
    (m:Pane N→Pane N)(e:∀v, profile (m v) ∈GateR N d)
    (g:∀v∈setAwning p o,Agrees (roost k o) (m v) v)
    (q:Essay S C F)(j:C≠0→ o ∈ S ∧ S.card ≤ k):
    ∃ A, Skin p o k r (V*Branch.rent a S*ledgerV C)
      (fun v=>picP F (m v)) (picL F 0) A:=by
 by_cases b:C=0
 · have hx:ledgerV C=0:=by simp [b,ledgerV]
   have hv:picP F = 0:=funext fun z=> norm_le_zero_iff.mp ((bad_pay q z).trans_eq hx)
   rw[hx,mul_zero,picL,hv]; exact ⟨0,Skin.zero⟩
 obtain ⟨i,u⟩:=j b
 have hj(x)(t:x∈S):separation o x≤ S.card:= le_of_lt ((f_then q b).lim o i x t)
 have hs:S⊆roost k o:=fun x t=>halo_spec.mpr ⟨o, mem_singleton_self _, (hj x t).trans u⟩

 have w : 2*(S.card+1)<(More N).val:= lt_of_le_of_lt (by gcongr) l.period
 obtain ⟨A,a₁,a₂⟩:=myrtle h.toTwine q hj w
 obtain ⟨h₁,h₂⟩:=h.dust (o:=o) (S:=S)
 have hc:=credit_pos q
 refine ⟨A,a₁.widen (lake_mono u) (le_trans ?_ (mul_le_mul_of_nonneg_right h₂ hc)),?_,?_⟩
 · exact le_of_eq (by ring)
 · intro v t
   have he: Healthy p.threshold (roost p.B o) v := ping_le t
   have ht : Healthy p.threshold (roost (S.card+1) o) v := he.mono_left (roost_expand (show S.card+1≤p.B from le_trans (by gcongr) l.paid))
   have hv := bright h.toTwine q (e v)
     (agrees_mono (g v t) (Finset.coe_subset.mpr hs)) hj ht p.threshold_pos.le ((frost_inc u p.threshold_pos.le).trans l.quick) w
   refine hv.trans (le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₁ hc) (sq_nonneg p.threshold)))
   exact le_of_eq (by unfold melt frosty;ring)
 intro v y t hh hy
 have hv:= (h.pay F q _ hh).2
 have hp:Agrees S (m v) (represent y):=fun i m n=> (g v t _ (hs m) (hs n)).trans (hy i (hs m) (hs n))
 rw [←a₂,pic_eq q (e v) hv hp]
 have hb:D*ledgerV C≤ V*Branch.rent a S*ledgerV C:=
   mul_le_mul_of_nonneg_right (h.earn.trans (le_mul_of_one_le_right h.pos.le (Branch.rent_one h.age.le _))) hc

 exact ((touch h.toTwine q).step hh).1.trans ((half_le_self (mul_nonneg (mul_nonneg h.dp.le hc) (pow_nonneg (norm_nonneg y) 3))).trans (mul_le_mul_of_nonneg_right hb (by positivity)))

variable {K:Scree.Loom N}{X:SOp N}{b:ℝ}
abbrev litP(K:Scree.Loom N)(p:BudgetPoint)(o:Seat N)(X:SOp N):Pane N→ℂ:=Matrix.trace ∘ bayonet K p o X
lemma dawn
    (h:Calcite a d D r V)(l:Shallow p k N r)
    (t:Trunk o X k a b d)(q:Clearance p K k d):
    Vinyl p o k d b (litP K p o X) ∧
    ∃c A, Skin p o k r (V*b) (litP K p o X) c A:=by
 obtain ⟨F,T,u,g,v,w⟩:=t.home
 let W(v:Pane N):Orbit N:=(v,Classical.arbitrary _)
 let m:= K ∘ W
 choose A H using fun S=>rind h l m (fun x=> (doPort q (W x)).property) (o:=o) (fun x t=>q.light (x:=W x) t)
    (u S) (fun p=>⟨(g S p).1,(g S p).2.le⟩)
 have he:=Skin.fin _ _ _ _ univ (fun j _=>H j)
 let G:Pane N→ℂ:=∑S, fun x=>picP (F S) (m x)
 have hm(x)(t:x∈setAwning p o):litP K p o X x=G x:=by
   rw[litP,Function.comp_apply,bayonet,Set.indicator_of_mem t]
   change Matrix.trace (X (doPort q (W x)).val)=_
   unfold G
   rw[w,Matrix.trace_sum,Finset.sum_apply]
   exact sum_congr rfl fun i _=> (in_pic (F:=F i) (x:=doPort q (W x))).symm

 have ht:=he.more (show _≤ V*b from
   le_trans (le_of_eq <| by rw[mul_sum];simp only [mul_assoc]) (mul_le_mul_of_nonneg_left v h.pos.le))
 refine ⟨Vinyl.color (saleAwning q (boxSeal t h.age.le)), ∑ i,picL (F i) 0, ∑i,A i,ht.rake,?_,?_⟩
 · intro v t;rw[hm v t];exact ht.small v t
 intro v y t z a;rw[hm v t];exact ht.turns t z a

variable {f:Pane N→ℂ}{c:ℂ}{A:Icey (Cella (More N))}
lemma repDawn : (represent (0:Lag N))=1:=funext fun i=> by rw[Work.F03.represent_link]; change SU.group.lieExp 0=1; exact group.mat_lieExp_zero -- ?
lemma dawnPing(p:BudgetPoint)(o:Seat N):(1:Pane N) ∈ setAwning p o:=by
 intro i _
 rw[WilsonStartup.face_one,group.chord_one];exact p.threshold_pos

lemma Skin.wakes(s:Skin p o k r b f c A)(h:0<r): f 1=c:=by
 have hu:=s.turns (y:=0) (dawnPing p o) (by simp [h.le]) (by rw[repDawn];exact fun _ _ _=>rfl)

 have he(i:Cella (More N)):brine 0 i=0:=by
   have hd : canal univ 0 i=brine 0 i:=if_pos (mem_univ _)
   rw [←hd,map_zero];rfl
 exact sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa [splash,swirl,he] using hu))

end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.dawn

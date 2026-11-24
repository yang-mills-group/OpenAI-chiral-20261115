import YM.SU5.FiniteGaugeData.Maypole.Jubil
/-! # Long gaps. Eu point operations, joins and priced measures -/
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Mink General Lorentz Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
open Poin Celeritas Land Leal Breve Poin.Gem
open Boundary Probe
namespace Folio
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(Ω:H)(hp:∀ x:E4,M S x Ω=Ω)
-- chronology.Braces
variable {α:Type}(A:α→H.Op)(ν:α→ℕ)
local notation "Ι"=> Item α
local notation "Ω°"=> wordValue S Ω A ν
local notation "Φ"=> legis S A ν
local notation "δ"=> gapK S ν
local notation "η"=> timesA a
local notation "Γ"=> leanX S
-- real shift of strip. used for density.
variable (p:E4)(t:ℝ)(n:ℕ)(L:List (Item α))
lemma comfy_u (W:H.Op): Commute (M S p) W → optx S W p=W:=fun g=>by unfold optx; rw [g.eq,mul_assoc,tgo,add_neg_cancel,tini,mul_one]
local notation "u°"=> SEP a p
lemma headL' (g:LaneE a t L): LaneE a (t+p a) (shifted p L):=by
 refine ⟨awakens p L g.1,?_⟩; intro z h; obtain ⟨x,t',rfl⟩:= List.mem_map.mp h; change _<(p+x.2) a; rw [PiLp.add_apply,add_comm t]; exact add_lt_add_right (g.2 x t') _ -- tune orientation
lemma tailL' (g:BackE a t L): BackE a (t+p a) (shifted p L):=by
 refine ⟨awakens p L g.1,?_⟩; intro z h; obtain ⟨x,t',rfl⟩:= List.mem_map.mp h; change (p+x.2) a <_; rw [PiLp.add_apply,add_comm t]; exact add_lt_add_right (g.2 x t') _
lemma frontPrice(k:LaneE a t L): Front S A ν (t+p a) (shifted p L)= optx S (Front S A ν t L) (SEP a p).val:=by
 unfold Front; rw [respire S A ν p L k.1,travel S ((u°).val)]; congr 1; cases L with
 | nil=> exact (law_unit S _).symm
 | cons x L=> rw [shifted,List.map_cons,budgetFoot,budgetFoot,show timesA a (shift p x)-(t+p a)=η x-t from (by unfold shift timesA; simp; ring)]; exact (comfy_u S (u°).val _ (by rw [laneslot]; exact (comm_u S _ _ (sub_pos.mpr (k.2 x List.mem_cons_self))).symm)).symm
lemma tailPrice(k:BackE a t L): Back S A ν (t+p a) (shifted p L)= optx S (Back S A ν t L) ((u°).val):=by
 unfold Back; rw [respire S A ν p L k.1,travel S ((u°).val)]; congr 1; cases L using List.reverseRecOn with
 | nil=> exact (law_unit S _).symm
 | append_singleton L x=> rw [shifted,List.map_append,List.map_singleton,budgetBack,budgetBack,show t+p a-timesA a (shift p x)=t-(η x) from (by unfold shift timesA; simp; ring)]; exact (comfy_u S (u°).val _ (by rw [laneslot]; exact (comm_u S _ _ (sub_pos.mpr (k.2 x (by simp)))).symm)).symm -- tune label
include hp
lemma vfront (k:LaneE a t L): face S Ω A ν (t+p a) (shifted p L)= M S ((SEP a p).val) (face S Ω A ν t L):=by rw [face,frontPrice S A ν p t L k]; change M S _ (Front S A ν t L (M S _ Ω))= _; rw [hp]
lemma vlatter (k:BackE a t L): role S Ω A ν (t+p a) (shifted p L)= M S ((SEP a p).val) (role S Ω A ν t L):=by rw [role, tailPrice S A ν p t L k, versX]; change M S _ (star (Back S A ν t L) (M S _ Ω))=_; rw [hp]
omit hp
-- reflection. labels not forced equal-dual here (avoid A-star closure in b). 
variable (B:α→α)(q:∀ i, ν (B i)=ν i)
def orbitT(a:Axis)(p:E4):E4:= p - (2*p a) • basis a
lemma Θa: orbitT a p a= -p a:=by simp [orbitT]; ring
lemma Θv : SEP a (orbitT a p)=SEP a p:=Subtype.ext (by change orbitT a p -(orbitT a p a) • basis a=p-p a • basis a; rw [Θa,orbitT,neg_smul,two_mul,add_smul]; abel)
def mirrorsK (a:Axis)(B:α→α)(x:Item α):Item α:= (B x.1,orbitT a x.2)
abbrev oddSpin (L:List (Item α)) (a:Axis)(B:α→α):= (L.map (mirrorsK a B)).reverse
local notation "τ"=> mirrorsK a B
lemma movetime(x:Item α): timesA a (τ x)= -timesA a x:= Θa x.2
lemma fore_a (k:LaneE a t L): BackE a (-t) (oddSpin L a B):=by
 constructor; swap; · intro i v; obtain ⟨x,p,rfl⟩:=List.mem_map.mp (List.mem_reverse.mp v); rw [movetime]; exact neg_lt_neg (k.2 x p)
 apply List.pairwise_reverse.mpr (List.pairwise_map.mpr (k.1.imp fun {i j} t=> ?_)); rw [movetime,movetime]; exact neg_lt_neg t -- tune
variable (v:∀ i, star (A i)=A (B i))
include v
lemma stamp_star(i:Item α): star (stamps S A i)=stamps S A (mirrorsK a B i):= by unfold stamps coreSp; rw [versX,v,show SEP a ((τ i).2)= SEP a i.2 from Θv i.2]; rfl
include q
lemma art_star (k:ahead a L): legis S A ν (oddSpin L a B)= star (legis S A ν L):= by
 cases L with
 | nil=> exact (star_one (R:=H.Op)).symm
 | cons x L=>
    induction L generalizing x with
    | nil=> change Φ [τ x]= _; unfold legis; rw [solitary,solitary,stamp_star S A B v x];
    | cons y L ih=>
       obtain ⟨w,h⟩:=List.pairwise_cons.mp k; have ht:=ih y h; let W:= oddSpin (y::L) a B; let Y:= oddSpin L a B; have hw:W= Y++[τ y]:=by unfold W oddSpin; rw [List.map_cons,List.reverse_cons]; -- tune
       change _=star (Film (stamps S A) (δ) (x::y::L)); rw [twoF,star_mul,star_mul,← show Φ W= _ from ht,stamp_star S A B v x]; change Φ (oddSpin (x::y::L) a B)=Φ W*(star (δ x y)* stamps S A (τ x)); rw [show oddSpin (x::y::L) a B=W++[τ x] from (by rw [oddSpin,List.map_cons,List.reverse_cons]),hw, show Φ ((Y++[τ y])++[τ x])= _ from joiningF _ (δ) Y [] (τ y) (τ x), solitary, ←mul_assoc (Φ (Y++[τ y])) (star (δ x y)) (stamps S A (τ x))];
       have he:0< timesA a y-timesA a x:=sub_pos.mpr (w _ List.mem_cons_self)
       rw [show δ (τ y) (τ x) = star (δ x y) from ?_] -- tune notation
       change leanX S ((η) (τ x)-(η) (τ y)) (ν (B y.1)+ν (B x.1))=star (leanX S ((η) y-(η) x) _); rw [q,q,movetime,movetime,warm_a S _ he, add_comm (ν _), neg_sub_neg]
lemma ok_back (k: LaneE a t L): role S Ω A ν (-t) (oddSpin L a B) = face S Ω A ν t L:=by
 unfold role Back; rw [art_star S A ν L B q v k.1,star_mul,star_star]; apply congrArg (fun f=> (f* _ : H.Op) Ω); cases L with
 | nil=> exact star_one _ -- signature
 | cons i L=> rw [oddSpin,List.map_cons,List.reverse_cons,budgetBack,budgetFoot, movetime,neg_sub_neg, show ν ((τ i).1)= ν i.1 from q i.1,add_zero,zero_add,warm_a]; exact sub_pos.mpr (k.2 i List.mem_cons_self)
end Folio
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp

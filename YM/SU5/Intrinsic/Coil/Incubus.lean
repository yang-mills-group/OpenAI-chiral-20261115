import YM.SU5.Intrinsic.Coil.Cobble
import YM.CF.Vp929.Contour.Hues

/- Give travel charges under any declared awake. Restore mass not forgotten
  even by the COMPONENT stitch (not free-compatible overlap stitch). -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 420000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Coil.Chart.Stoke
open Function Lattice Finset Filter Stilo Palot RG Scree Skye Fock Tulip Sour
open Cube Pastry Vow Rue Stax Sault
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {I:Type}[DecidableEq I][Fintype I]{n:Side} {F:ForceBudget n}{P:BudgetPoint} {H:ℝ} {δ:ℕ}
local notation "Υ"=> Support (More n)
variable {b:Force n→ℝ}{V:I→ Firing n}{a:I→ℝ}{B:Chart I (Seat n)}
variable (C:B.Stoke δ P H V a) (T:Blizzard F P H δ b)(L:Finset (I⊕ Force n))(S:Aura n)(D:Support (More n)) (l:List I)(t:0≤ H)(w: 3≤ P.B)
-- note F explicit parameter separate (often with T only lemma use). canonical recipe synchronized by only bearing touches.
def lot (F:ForceBudget n)(S:Aura n)(D:Support (More n))(l:List I): Copy n:= if h:Pun B L S D ∧ halo δ D⊆S.val then C.roll h.1 h.2 (∏ i∈L.toRight,F i) l else 0
include T in
lemma gust (h:Pun B L S D)(x:Orbit n)(v:x.1∈σX P S D) : C.lot L F S D l x=sail (C.gives x) L.toLeft l (∏ i∈L.toRight,F i x):=by
 unfold lot; split; next s=>rw [C.roll_eq _ _ _ _ _ v,Finset.prod_apply]
 next s=>
    have hz : ∏ i∈L.toRight,F i x=0:=by by_contra g; exact s ⟨h,(Pun.oldHas T h x g).1⟩ -- order
    rw [hz,map_zero]; rfl
-- above T must include

private lemma zero_fray {n:Side} {X:Aura n}{D:Support (More n)}{P:BudgetPoint}(q:ℝ)(v:0≤q)(H:ℝ)(δ:ℕ): Fray P H δ X D 0 q:= ⟨Medal.zeroT.big v,fun _ p=> (p rfl).elim⟩
include T t w
lemma toll (d:l.Nodup)(z:l.toFinset=univ): Fray P H δ S D (C.lot L F S D l) (Season.bookL B.ledger (Sum.elim a b) 0 L S D):=by
 let Ξ:= B.ledger
 have hΛ: (∏ i∈L.toLeft,a i)* ∏ i∈L.toRight,b i=∏ i∈ L,Sum.elim a b i:=by nth_rw 3 [← splitK L]; rw [Finset.prod_disjSum]; rfl -- tune
 by_cases u:Pun B L S D
 · rw [Season.bookL,if_pos ⟨Nat.zero_le _,u.2.2,u.1,u.2.1⟩,Season.leafCost,←hΛ]; unfold lot; split
   next p=> have he:= C.rollFray p.1 p.2 _ _ (u.oldFuel T t) l d w t; rwa [z,inter_univ] at he
   exact zero_fray _ (mul_nonneg (prod_nonneg fun i _=> C.rate i) (prod_nonneg fun i _=> T.rate i)) _ _
 unfold lot Season.bookL; rw [dif_neg (fun p=>u p.1),if_neg (fun p=>u ⟨p.2.2.1,p.2.2.2,p.2.1⟩)]; exact zero_fray _ le_rfl _ _
omit T t w
lemma turf (x:Orbit n)(τ:Ids n) : C.lot L F S ∅ l x=C.lot L F S ∅ l (x.1,τ):=by
 unfold lot; split; swap; rfl
 next u=> exact C.rollHat _ _ _ x τ rfl (by rw [u.1.no_old rfl, prod_empty]; rfl) l

abbrev cutL (E:I→ℂ)(L:Finset (I⊕ Force n)):= ∏ i∈L.toLeft,E i
abbrev transit (S:Aura n)(D:Support (More n))(x:Orbit n)(τ: I→ℂ):= (∑ L:Finset (I ⊕ Force n), cutL τ L • C.lot L F S D l) x
lemma sail_cost(Tau:I→ℂ)(Z:I→ Cipher n →ₗ[ℂ] Cipher n)(J:Finset I)(d:l.Nodup)(e:Cipher n) : sail (fun i=>Tau i • Z i) J l e=(∏ i∈ J∩l.toFinset, Tau i) • sail Z J l e:=by
 induction l with
 | nil=>rw [List.toFinset_nil,inter_empty,prod_empty,one_smul]; rfl
 | cons i l ih=>
    obtain ⟨f,q⟩:= List.nodup_cons.mp d; by_cases g:i∈J
    · rw [sail,List.foldr_cons,if_pos g,sail,List.foldr_cons,if_pos g,List.toFinset_cons, inter_insert_of_mem g, prod_insert (fun p=> f (List.mem_toFinset.mp (mem_inter.mp p).2)), mul_smul]
      rw [LinearMap.comp_apply,LinearMap.smul_apply]; unfold sail at ih; rw [ih q,map_smul,LinearMap.comp_apply] -- tune
    rw [sail,List.foldr_cons,if_neg g,sail,List.foldr_cons,if_neg g,List.toFinset_cons, inter_insert_of_notMem g]; exact ih q
lemma mellow (T:Chart I (Seat n))(U:I→Cipher n→ₗ[ℂ] Cipher n)(p:T.Mild U)(a:I→ℂ): T.Mild (fun i=>a i • U i):=by
 refine ⟨fun i X g h t=>?_ ,fun i X e f h t=>?_⟩
 · exact (p.nearT i _ _ h t).smul (a i) -- tune
 simp only [LinearMap.smul_apply]; rw [p.farT _ _ _ _ h t]; exact (smul_mul_assoc ..).symm -- check

include C
variable (Deck:List (Force n))(hd:l.Nodup)(hz:l.toFinset=univ)(p0:Deck.Nodup)(pq:Deck.toFinset=univ)(φ:I→ℂ)(x:Orbit n)(hq:Rue.FleetS P.threshold x.1) -- dummy
local notation "Ω"=> flags P.threshold x.1
include hd hz p0 pq hq
-- compute price at that consult (keep T too)
include T
lemma accrues : B.script l Deck (Ω) (fun i=> φ i • C.gives x i) (fun i=>F i x) S.val = C.transit l S (Ω∩S.val) x φ (F:=F):=by
 unfold script Album.compact mintF transit; rw [Finset.sum_apply]; refine Finset.sum_congr rfl fun L _=> ?_
 unfold Album.read; split
 next h=>
    let D:= Ω ∩ S.val; have u: Pun B L S D:= ⟨h.1,h.2.allowed, (by
       have hm:B.ledger.foot L=S.val:= by rw [←Album.tune,h.1,bay_beam]
       rw [← h.2.known, hm, inter_comm])⟩
    have h': x.1∈ σX P S D:= ⟨?_,inter_subset_left⟩; swap
    · apply (Rue.shoreK _ _ hq _).mp; unfold Healthy; exact Finset.disjoint_left.mpr fun i t p=> (mem_sdiff.mp t).2 (mem_inter.mpr ⟨p,(mem_sdiff.mp t).1⟩)
    rw [Pi.smul_apply,C.gust T _ _ _ _ u x h']
    have he:= sail_cost l φ (fun i=> C.gives x i) L.toLeft hd (∏ i∈ L.toRight,F i x); rw [hz,inter_univ] at he
    have hh:= execute L.toLeft L.toRight (fun i=>φ i • C.gives x i) (fun i=>F i x) l Deck p0 (by convert pq using 2 <;> congr!); rw [splitK] at hh
    exact hh.trans he
 next h=>
    rw [lot,dif_neg, Pi.smul_apply,Pi.zero_apply,smul_zero]; intro h'; have he:=h'.1.tuneSpace; apply h; refine ⟨h'.1.1,h'.1.2.1,?_⟩; rw [he,h'.1.2.2,inter_comm]

end YM.CF.Coil.Chart.Stoke
open YM.CF.Coil.Chart.Stoke
#print axioms accrues
#print axioms toll

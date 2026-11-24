import YM.SU5.Intrinsic.Coil.Still
import YM.CF.Mew.Tube
import YM.CF.Rive.Boil

/- Pin API. price late polynomials via actual aperture pressures. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Coil.Chart.Stoke
open Function Lattice Finset Filter Stilo Palot RG Scree Skye Fock Tulip Sour
open Cube Pastry Vow Rue Stax Sault
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {I J:Type}[DecidableEq I][Fintype I]{n:Side} {F:ForceBudget n}{P:BudgetPoint} {H:ℝ} {δ:ℕ}
variable {b:Force n→ℝ}{V:I→ Firing n}{a:I→ℝ}{B:Chart I (Seat n)}
variable (C:B.Stoke δ P H V a) (T:Blizzard F P H δ b)(L:Finset (I⊕ Force n))(S:Aura n)(D:Support (More n)) (l:List I)
open Push.AbsoluteSums Push.AbsoluteSums.Trees
variable (Deck:List (Force n))(d:l.Nodup)(z:l.toFinset=univ)(p0:Deck.Nodup)(pq:Deck.toFinset=univ)
local notation "W"=> B.ledger
variable (x:Orbit n)
include T d z
lemma realizes (u:I→ℂ)(t:FleetS P.threshold x.1) : let F' := C.issueK F l u; B.reading (fun i=> (u i) • C.gives x i) l (fueled P F x)= hGas (flags P.threshold x.1) (keyL P F' (kiosk F') x):=by
 intro F'; classical
 let deck:Finset (Force n):=univ; let A:=deck.toList; have hz:A.toFinset=univ:= toList_toFinset _
 obtain hz':A.Nodup:= nodup_toList _
 let U(i:I):= (u i) • C.gives x i; let Ω:= flags P.threshold x.1
 rw [B.settles P U F l A hz' (by convert hz using 2) (mellow B (C.gives x) (C.modest x) u) x t (fun i=> (T.costs i).merit.lit x)]; apply congrArg (hGas (E:= Cipher n) _)
 funext i; let v:= i.val; have ht:C.transit l i (Ω∩i.val) x u (F:=F)= F' i (Ω∩i.val) x:=rfl
 rw [(C.accrues T i l A d z hz' (by convert hz using 2) u x t),ht]; unfold keyL; split; next h=> rw [Finset.disjoint_iff_inter_eq_empty.mp h]
 rfl
omit T d z
variable [LinearOrder J][Fintype J] (σ:J→Seat n)(ρ:I→J)(g:B.anchor=σ ∘ ρ)
open Mew
abbrev furnish (F : ForceBudget n)(q:Key J): Cusp n:= C.issueK F l (q ∘ ρ)
def pin (F:ForceBudget n)(j:J):Pax n:= fun s=>∑ i:I with ρ i=j, C.firstAt s F l i
private lemma term_at (i:Finset (I⊕ Force n)) (v:Pun B i S D): B.offices i.toLeft:= (B.season_iff _ _).mp ((splitK i).symm ▸ v.2.1) |>.1
private lemma when_zero (u: Finset (I⊕ Force n)) (z:u.toRight=∅)(v:u.toLeft=∅): C.lot u F S D l=0:=by
 unfold lot; rw [dif_neg]; rintro ⟨t,a⟩; obtain ⟨x,h,-⟩:= only_old _ _ _ t v; rw [h] at z; exact notMem_empty _ (z ▸ mem_toRight.mpr (mem_singleton_self _))
include g
private lemma keyset (v:Pun B L S D) : Set.InjOn ρ (L.toLeft:Set I):= by
 intro i u j w p; apply term_at S D L v u w -- order tuner
 rw [g]; simp [p]
lemma pin_single (z:ℂ)(j:J) : kiosk (C.furnish l ρ F (update 0 j z))= z • C.pin l ρ F j:=by
 let u:I→ℂ:= update (0:Key J) j z ∘ ρ
 let f: I→ Finset (I⊕ Force n):= fun i=> {Sum.inl i}
 funext S
 let M:= (univ:Finset I).filter fun i=>ρ i=j
 let L(i:Finset (I ⊕ Force n)):= cutL u i • C.lot i F S ∅ l
 change (∑ i,L i)= z • ∑ i∈M,C.firstAt S F l i
 rw [←Finset.sum_subset (f:=L) (subset_univ (M.image f)) ?_,sum_image]; rotate_left
 · intro i _ x _ a; exact Sum.inl.inj (singleton_injective a)
 · intro i _ k; by_cases q:Pun B i S ∅; swap; · unfold L; rw [lot,dif_neg (fun g=>q g.1),smul_zero]
   have h:= q.no_old rfl
   unfold L; unfold cutL; by_cases g':i.toLeft.Nonempty; swap; · rw [when_zero C S ∅ l _ h (not_nonempty_iff_eq_empty.mp g'),smul_zero]
   obtain ⟨a,b⟩:=g'
   by_cases w:∃ x∈i.toLeft, ρ x≠j
   · obtain ⟨x,p,h⟩:=w; rw [prod_eq_zero p (show u x=0 from update_of_ne h ..),zero_smul]
   push Not at w
   apply False.elim; apply k
   have hx:i.toLeft={a}:=Subset.antisymm (fun x e=> mem_singleton.mpr (keyset _ _ _ σ ρ g q e b ((w x e).trans (w a b).symm))) (singleton_subset_iff.mpr b)
   have he:i={Sum.inl a}:=by nth_rw 1 [← splitK i]; rw [h,hx]; ext x; cases x <;>simp
   rw [he]; exact mem_image_of_mem f (mem_filter.mpr ⟨mem_univ _,w _ b⟩)
 rw [Finset.smul_sum]; refine sum_congr rfl fun i p=>?_ ; unfold L cutL f; rw [show (toLeft ({Sum.inl i}:Finset (I⊕Force n)))={i} from Finset.ext fun i=>by simp, prod_singleton, show u i=z from (by unfold u Function.comp; rw [(mem_filter.mp p).2]; exact update_self ..)]; rfl
-- locality in key; no analytic assumption elsewhere.
lemma hush_f : Rive.Hush σ S.val (fun i:Key J=> C.furnish l ρ F i S D):=by
 intro v hv x hx e; unfold furnish issueK; refine Finset.sum_congr rfl fun i _=>?_; unfold lot; split; next h=>
     apply congrArg (· • _); refine prod_congr rfl fun j t=>e _ ?_; rw [← comp_apply (f:=σ), ← g]; exact C.active h.1 h.2 j t (B.here j)
 rw [smul_zero,smul_zero]
omit g
lemma operates : River (fun z:Key J=> C.furnish l ρ F z S D x):=by
 unfold furnish issueK; simp_rw [Finset.sum_apply,Pi.smul_apply]; apply Mew.tip_bank univ _ _|>.1; intro i _
 let F':= C.lot i F S D l x
 change River (fun z=>cutL (z∘ρ) i • F')
 apply κscale _ (Mew.zeroR _)
 unfold cutL; apply (show River (fun z:Key J=>∏ j∈toLeft i, z (ρ j)) from ?_)
 apply Rive.cost_R _ (fun i (z:Key J)=>z (ρ i)); intro i _; exact (Mew.pine_r ({ρ i}:Finset J)).cong (fun z _=> (Finset.prod_singleton ..).symm)
lemma operatingT (u:Key J): Bake.Turf (kiosk (C.furnish l ρ F u)):=by
 intro i x t; unfold kiosk furnish issueK; simp_rw [Finset.sum_apply,Pi.smul_apply]; exact sum_congr rfl fun j _=>congrArg (_ • ·) (C.turf ..)
#print axioms realizes
#print axioms operates
#print axioms pin_single
end YM.CF.Coil.Chart.Stoke

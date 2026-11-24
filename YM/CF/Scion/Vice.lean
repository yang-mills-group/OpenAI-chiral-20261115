import YM.CF.Scion.Zest
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Scion
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
variable {ι A n M: Type*}[LinearOrder n][Fintype n][LinearOrder M][Fintype M]
local notation "bay"=>Stilo.bay
variable {C:Type*}[Fintype ι][DecidableEq ι][Fintype A][DecidableEq A]
variable (J:n→ A)(D:LeanV M→A)(X:ι→leaf A)(P Q:Finset ι)(S T:Crowd A)
-- bundle even at each climate; reading restricted by partial charge incidence
abbrev hearth(J:n→A)(S:Finset A):Set (Twig n):={x|J (twigS x).2∈S}
abbrev cluster (P:Finset ι) : Crowd A:=Finset.sup P fun i=> Stilo.beamH (X i).val
structure ModeW(J:n→A)(D:LeanV M→ A)(X:ι→leaf A)(P: Finset ι) where
 knots: Crowd A→ Weave n M
 voice : FC (LeanV n)
 rhythm : Crowd A→ FC n -- CAR may depend on queried grouping only until charge labels fixed
 diet : Crowd A → FC (LeanV M)
 forP i: cluster X P ≤ i → Pitch put (lipV (hearth J (bay i))) 0 voice
 capP i: cluster X P ≤ i → Pitch bell (lipF (hearth J (bay i))) 0 (rhythm i)
 dapP i: cluster X P ≤ i → Pitch put (D ⁻¹' bay i) 0 (diet i)
 localP i: cluster X P ≤ i → ∀ j∈ hearth J (bay i),∀ t, (knots i).seats j t≠0→ D t∈ bay i
section
open scoped Classical
variable {J D X P Q}
variable (F:ModeW J D X P)
def tempo (i:Crowd A): FC (LeanV M):= if cluster X P ≤ i then (issue (F.knots i) F.voice (F.rhythm i))* F.diet i else 0
lemma token(i:Crowd A): Flour (univ.filter fun j=>D j ∈ bay i) (tempo F i):=by
 unfold tempo; split_ifs with h
 · apply fry_p (b:=0) _ (Even.zero)
   let U:= bay i; let V:Set (LeanV M):= D ⁻¹' U; let X':= lofty (F.knots i) (F.forP _ h) (F.capP _ h) (R:=V) (F.localP i h); exact (X'.mu (F.dapP _ h)).rise (fun j v=> mem_filter.mpr ⟨mem_univ _,v⟩)
 exact Flour.trivial
def vig(i:Crowd A):ribbon M:=⟨tempo F i,(token F i).lift (subset_univ _)⟩
def vigor : Crowd A→ ribbon M:=reconL.symm (vig F)
lemma vig_all(i:Crowd A): (vigor F i).val=reconL.symm (tempo F) i:=by
 symm; apply congrFun _ i; exact solve (tempo F) (fun i=> (vigor F i).val) (fun i=> Eq.trans (congrArg Subtype.val ((recon (vig F) i).symm)) (map_sum (Dough _).val _ _)) -- tune
lemma grill(i:Crowd A): Flour (univ.filter fun j=>D j∈bay i) (vigor F i).val:=by
 rw [vig_all]; let f:=tempo F; let Z(S:Crowd A):= univ.filter fun j:LeanV M=>D j∈bay S; let H:=reconL.symm f
 -- view inversion local
 change Flour (Z i) (H i); induction hp:(deckX i).card using Nat.strong_induction_on generalizing i with
 | h m ih=>
    have he: i∈ deckX i:=(deckH ..).mpr le_rfl; let W:= (deckX i).erase i; have hx:f i=H i+ ∑ j∈ W,H j:= (recon f i).symm.trans (Finset.add_sum_erase _ H he).symm
    rw [show H i=f i -∑ j∈W,H j from by rw [hx,add_sub_cancel_right],sub_eq_add_neg]
    have hy:Flour (Z i) (∑ j∈ W,H j):=by
       apply Flour.sum; intro j t; have hj:= (deckH ..).mp (mem_of_mem_erase t); apply (ih _ ?_ j rfl).lift ?_; rw [←hp]; apply card_lt_card; exact Finset.ssubset_iff_subset_ne.mpr ⟨fun k v=> (deckH ..).mpr (((deckH ..).mp v).trans hj), fun p=> (ne_of_mem_erase t) (le_antisymm hj ((deckH ..).mp (p.symm ▸ he)))⟩
       exact fun k v=> mem_filter.mpr ⟨mem_univ _,bay_m hj (mem_filter.mp v).2⟩
    exact (token F i).add (by simpa using hy.smul (-1))
lemma fuelFit (Q:Crowd A)(p:vigor F Q≠0) : fits X P Q:=by
 by_cases h: cluster X P≤ Q; exact fun i t=>(Finset.le_sup (f:=fun z=> beamH ((X z).val)) t).trans h
 exfalso; apply p; apply Stilo.proves (f:=vigor F) (g:=0)
 intro i t; unfold vigor; rw [view_zero,recon (vig F)]; apply Subtype.ext; exact if_neg fun l=> h (l.trans t)
local notation "η"=> hearth J
variable  (V:ModeW J D X P)(W:ModeW J D X Q)(U: ModeW J D X (P∪Q))
structure Grown (i:Crowd A):Prop where
 source : U.voice = V.voice*W.voice
 ranky : U.rhythm i=V.rhythm (i⊓ S) * W.rhythm (i⊓T)
 purse : U.diet i= V.diet (i⊓ S)* W.diet (i⊓ T)
 arcsL j (p:j∈η (bay (i⊓S))):(U.knots i).seats j=(V.knots (i⊓ S)).seats j
 arcsR j (p:j∈η (bay (i⊓T))):(U.knots i).seats j=(W.knots (i⊓ T)).seats j
 windL j (p:j∈η (bay (i⊓S))) t (v:t∈η (bay (i⊓S))): (U.knots i).pals j t=(V.knots (i⊓S)).pals j t
 windR j (p:j∈η (bay (i⊓T))) t (v:t∈η (bay (i⊓T))): (U.knots i).pals j t=(W.knots (i⊓T)).pals j t
 winds j (p:j∈η (bay (i⊓S))) t (v:t∈η (bay (i⊓T))): (U.knots i).pals j t=0 ∧ (U.knots i).pals t j=0
lemma growth(i:Crowd A) (p:Grown S T V W U i)(l:cluster X P≤ S)(r:cluster X Q≤T)(g:cluster X (P∪Q)≤ i) : vig U i = vig V (i⊓ S)* vig W (i⊓T):=by
 apply Subtype.ext; have hh:=g; unfold cluster at hh; rw [sup_union] at hh; obtain ⟨t,v⟩:=sup_le_iff.mp hh; let A:= i⊓S; let B:= i⊓T; have ht: cluster X P ≤ A:= le_inf t l; have hv: cluster X Q ≤ B:= le_inf v r
 change tempo U i=tempo V A *tempo W B; rw [tempo,if_pos g,tempo,if_pos ht,tempo,if_pos hv,p.source,p.ranky,p.purse,crossY _ p.winds (V.forP _ ht) (W.forP _ hv) (V.capP _ ht) (W.capP _ hv),paid_u _ _ (V.forP _ ht) (V.capP _ ht) p.arcsL p.windL,paid_u _ _ (W.forP _ hv) (W.capP _ hv) p.arcsR p.windR];
 let Wb:= issue (W.knots B) W.voice (W.rhythm B); have he: Flour (univ:Finset (LeanV M)) Wb:= fry_p ((lofty (W.knots B) (W.forP _ hv) (W.capP _ hv) (R:=((Finset.univ:Finset (LeanV M)):Set (LeanV M))) (fun _ _ _ _=> mem_univ _))) (by simp); have hu: Flour univ (V.diet A):= fry_p ((V.dapP _ ht).rise (fun j v=>mem_univ _)) (by simp)
 simp_rw [mul_assoc]; rw [← mul_assoc Wb, he.comm hu,mul_assoc] -- tune
lemma engine (d:Disjoint (bay S) (bay T))(l:cluster X P ≤ S)(r:cluster X Q≤ T)(p:∀ i:Crowd A,i ≤ S ⊔ T → cluster X (P∪Q) ≤ i → Grown S T V W U i) : vigor U (S ⊔ T )=vigor V S * vigor W T:=by
 apply localizes d; intro i t; rw [show view _ (vigor V)= _ from recon .., show view _ (vigor W)=_ from recon .., show view _ (vigor U)= _ from recon ..]; by_cases h:cluster X (P∪Q) ≤ i; exact growth S T V W U i (p _ t h) l r h
 apply Subtype.ext
 change tempo U i=tempo V (i⊓ S)*tempo W (i⊓ T); rw [tempo,if_neg h,tempo,tempo]; split_ifs with a b c
 · exfalso; apply h; rw [cluster,sup_union]; exact sup_le (a.trans inf_le_left) (b.trans inf_le_left)
 all_goals simp
end
end YM.CF.Scion

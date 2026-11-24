import YM.CF.Hake.Hula
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hake
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{ι n A:Type*}[LinearOrder n][Fintype n][SemilatticeSup A][OrderBot A][Fintype A][DecidableEq A]{k:ℕ}{x:E}
variable {B:Raid n}
lemma season(c d:Track A (Raid n))(p:0≤c)(g:0≤d):0 ≤ Lay c d:= sum_nonneg fun i _=> sum_nonneg fun j _ t=>by rw [Pi.single_apply]; split_ifs; exact skirtPos _ _ (p i) (g j); exact le_rfl
lemma silver:0 ≤ Loan n A:= fun i=>by unfold Loan; rw [Pi.single_apply]; split_ifs; intro j; rw [Pi.single_apply]; split_ifs; exact zero_le_one; exact le_rfl; exact le_rfl
section
variable (L:ι→Track A (Raid n))(G:ι→ι→ Track A (Raid n))
def shadeB :ℕ→ List ι→ Track A (Raid n)
 | 0,_=> Loan n A
 | _+1, []=> Loan n A
 | b+1,i::l=> Lay (L i) (shadeB b l) + ((picks l).map fun x=>Lay (G i x.front) (shadeB b x.back)).sum
lemma sPays (b:ℕ)(l:List ι)(F:ι→Track A (E→FC n))(V:ι→ι→Track A (E→FC n))(f:∀ i∈ l, Course k (F i) x (L i))(v:∀ i∈ l,∀ j∈ l,Course k (V i j) x (G i j)): Course k (timetable F V b l) x (shadeB L G b l):=by
 induction b generalizing l with
 | zero=> exact Course.coinT _
 | succ b ih=> cases l with
            | nil=> exact Course.coinT _
            | cons i l=>
                have he: l⊆i::l:= fun t w=>List.mem_cons_of_mem _ w; have hp: i∈ i::l:=List.mem_cons_self
                have ht(y:List ι)(p:y⊆i::l):=ih y (fun i e=>f i (p e)) fun i e j u=> v i (p e) j (p u)
                refine Course.fit (Course.link (f i hp) (ht l he)) (Course.ListS _ (fun x=>_) _ (fun y m=>?_))
                obtain ⟨hy,hx⟩:=pick_wear l m; apply Course.link ?_ (ht _ (List.Subset.trans hx he)); have hy':= v i hp _ (he hy); split_ifs; simpa using hy'.ride (-1) (by simp); exact hy'
variable [LinearOrder ι][Fintype ι](u:∀ i,0≤ L i)(g:∀ i j,0≤ G i j)
include u g
lemma sPos (b:ℕ)(l:List ι):0 ≤ shadeB L G b l:=by
 -- via Course at zero easier list pos
 induction b generalizing l with
 | zero=> exact silver
 | succ b ih=> cases l with
            | nil=> exact silver
            | cons i l=>
                rw [shadeB]; apply add_nonneg (season _ _ (u _) (ih _)); apply List.sum_nonneg; intro j p; obtain ⟨x,-,rfl⟩:=List.mem_map.mp p; exact season _ _ (g _ _) (ih _)
lemma picksSub (l:List ι)(x:Bout ι)(p:x∈ picks l):x.back.Sublist l:=by
 clear *- p; induction l generalizing x with| nil=> simp [picks] at p| cons i l ih=> rw [picks,List.mem_cons] at p; rcases p with rfl|w; exact List.sublist_cons_self _ _; obtain ⟨z,p,rfl⟩:=List.mem_map.mp w; exact (ih z p).cons_cons _
lemma sWear (Q:ι→ Track A ℝ)(p: Turner B)(ℓ:∀ i,ownH ℝ A ≤ Q i)(e:∀ i,rateT B (L i)+∑ j:ι,rateT B (G i j)≤Q i)(b:ℕ)(l: List ι)(m:l.length≤b)(w:l.Nodup):rateT B (shadeB L G b l)≤ payH Q l:=by
 induction b generalizing l with
 | zero=> rw [show l=[] from List.eq_nil_of_length_eq_zero (by omega)]; exact tZero p
 | succ b ih=> cases l with
            | nil=> exact tZero p
            | cons i l=>
                rw [shadeB,tFit]; have hs(t):0 ≤ Q t:= coinH.trans (ℓ t); have hp:=(List.nodup_cons.mp w).2; simp only [List.length_cons,add_le_add_iff_right] at m
                let S:= rateT B (L i); let H:=payH Q l; have hl:0 ≤ H:= pay_S hs
                have hu: rateT B (Lay (L i) (shadeB L G b l)) ≤ crank S H:= (tFused p (u i) (sPos L G u g b l)).trans (crank_mono _ _ _ (Turn_up p (u i)) (ih l m hp))
                let D(j):= rateT B (G i j); let Bx(x:Bout ι):= Lay (G i x.front) (shadeB L G b x.back); let X:=picks l
                have ht(j):0≤ D j:=Turn_up p (g i j)
                have hc(x:Bout ι)(hx:x∈X):rateT B (Bx x)≤ crank (D x.front) H:=by
                   have he:=picksSub L G u g l x hx
                   apply (tFused p (g i _) (sPos L G u g b _)).trans; apply crank_mono _ _ _ (ht _); apply (ih _ (he.length_le.trans m) (he.nodup hp)).trans
                   exact le_trans (le_of_eq (crank_L ..).symm) (le_trans (crank_r _ _ _ (pay_S hs) (ℓ x.front)) (order_pay _ l hx).symm.le)
                let R:= ∑ j:ι,D j
                have hy : ((X.map Bout.front).map D).sum ≤ R:=by rw [Stilo.deed _ _ (settle l hp)]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> ht i)
                have he:rateT B ((X.map Bx).sum)≤ crank R H:=by rw [tList]; apply (esteem _ _ _ hc).trans; apply le_trans ?_ (crank_r _ _ _ hl hy); rw [crank_list,List.map_map,List.map_map]; exact le_rfl
                exact (add_le_add hu he).trans ((crank_plus ..).symm.le.trans (crank_r _ _ _ hl (e i)))
end
end YM.CF.Hake

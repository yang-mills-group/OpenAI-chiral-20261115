import YM.CF.Roots.Sort
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Roots
open Function Set Metric Mew MeasureTheory Filter Finset
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E F N :Type*}[Fintype I][LinearOrder I][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F]
variable [NormedCommRing N][NormedAlgebra ℂ N][CompleteSpace N]
variable {f g u v:Key I→E}{a b a' b': Key I→N}{s t r:List I}
section storm
variable {J:Type*}[DecidableEq J](σ:I→J)(C: I→ I→ℂ) -- matrix (old index i, new p).
abbrev pipe_ζ(σ:I→J)(i:I):= Finset.univ.filter fun j=> σ j=σ i
def snow(σ:I→J)(C:I→I→ℂ)(F:List I→E): List I→E
 | []=>F []
 | i::l=> ∑ j∈pipe_ζ σ i,C j i • snow σ C (fun s=>F (j::s)) l
abbrev fuelΦ(σ:I→J)(C:I→ I→ℂ)(F:Key I→E): List I→E:=snow σ C (tipI F)
abbrev ψS(σ:I→J)(L:List I):Prop:= (L.map σ).Nodup
lemma uS_b{ι:Type*}(σ:I→ι)(h:ψS σ (s:List I)):s.Nodup:=List.Nodup.of_map σ h
local notation "τ"=> pipe_ζ σ
local notation "wS"=> ψS σ
local notation "Ω"=> fuelΦ σ C
abbrev Storm_C(σ:I→J)(C:I→ I→ℂ)(L:List I)(F G:Key I→E): Prop :=∀ i:List I,i.Sublist L → tipI G i= fuelΦ σ C F i
lemma rer {G W:List I→E}(s:List I)(p:∀ l,l.map σ=s.map σ→G l=W l):snow σ C G s=snow σ C W s:=by
 induction s generalizing G W with
 | nil=> exact p _ rfl
 | cons i s ih=> rw [snow,snow]; exact sum_congr rfl (fun j u=> congrArg (C j i • ·) (ih fun l h=>p _ (by rw [List.map_cons,List.map_cons,h,(mem_filter.mp u).2])))
lemma Storm_C.rim(h:Storm_C σ C s f g)(p:r.Sublist s):Storm_C σ C r f g:=fun i h'=>h i (h'.trans p)
lemma tally_ADD (G W:List I→E)(s:List I):snow σ C (G+W) s=snow σ C G s+ snow σ C W s:=by
 induction s generalizing G W with
 | nil=> rfl
 | cons i s ih=> rw [snow,snow,snow, ←Finset.sum_add_distrib]; refine sum_congr rfl fun j u=> ?_; exact (congrArg (C j i • ·) (ih (fun x=> G (j::x)) (fun x=>W (j::x)))).trans (smul_add ..) -- rw cast
lemma tally_scale (c:ℂ)(G:List I→E)(s:List I): snow σ C (c • G) s=c • snow σ C G s:=by
 induction s generalizing G with
 | nil=> rfl
 | cons i s ih=>
    rw [snow,snow,Finset.smul_sum]; refine sum_congr rfl fun j u=> ?_; exact (congrArg (C j i • ·) (ih fun x=>G (j::x))).trans (smul_comm ..)
lemma tally_l (L:E→L[ℂ]F)(G:List I→E)(s:List I): snow σ C (L∘G) s=L (snow σ C G s):=by
 induction s generalizing G with
 | nil=> rfl
 | cons i s ih=> rw [snow,snow,map_sum]; apply sum_congr rfl; intro j u; exact (congrArg (C j i • ·) (ih fun x=>G (j::x))).trans (map_smul ..).symm
lemma Aζ (h:River f)(v':River u)(p:River g)(q:River v)(t:Storm_C σ C s f g)(u':Storm_C σ C s u v):Storm_C σ C s (fun x=>f x+u x) (fun x=>g x+v x):=by
 intro i hi; rw [tip_A p q,t i hi,u' i hi]; exact ((tally_ADD σ C (tipI f) (tipI u) i).symm.trans (rer σ C i (fun l _=> (tip_A h v' _).symm)))
lemma scope_C (h:River f)(p:River g)(v:Storm_C σ C s f g)(A:E→L[ℂ]F):Storm_C σ C s (A∘f) (A∘g):=by
 intro i t; rw [show tipI (A∘ g) i=A (tipI g i) from sim_H p A i roots,v i t]; exact ((tally_l σ C A (tipI f) i).symm.trans (rer σ C i (fun l _=> Eq.symm (show tipI (A∘ f) l=A (tipI f l) from sim_H h A l roots))))
lemma proper (a:E)(i:I)(l:List I): tipI (fun _ : Key I=>a) (i::l)=0:=by
 have hp':EqOn (cutI (fun _:Key I=>a) i) (fun _=>0) (hill I):= fun x p=> (mitt (zeroR _) p i).deriv.symm.trans (deriv_const ..)
 exact (lace_C l hp' roots).trans (tip_0 l)
lemma women (l:List I):snow σ C (fun _=>(0:E)) l=0:=by
 induction l with| nil=>rfl| cons i s h=>rw [snow]; simp_rw [h]; simp
lemma constant_C (a:E) : Storm_C σ C s (fun _=> a) (fun _=>a):=by
 intro l p; cases l with
 | nil=>rfl
 | cons i l=>
    rw [proper]; unfold fuelΦ; rw [snow]; symm; exact sum_eq_zero (fun j _=> (congrArg (C j i • ·) (show snow σ C (fun s=>tipI (fun _ :Key I=>a) (j::s)) l=0 from (by simp_rw [proper]; exact women ..))).trans (smul_zero _))
local notation "W"=> Storm_C σ C
-- cut operator.X l uses Key chart at full radius.
abbrev Γcut(F:Key I→E)(i:I):Key I→E:= fun x=> ∑ j∈pipe_ζ σ i,(C j i) • cutI F j x
lemma Γsail(h:River f)(i:I): River (Γcut σ C f i):= (tip_bank _ _ fun i _=> River.scale (h.flow _) _).1 -- argument ambiguity
lemma Ω_tip(h:River f)(i:I) : Ω f (i::s) = Ω (Γcut σ C f i) s :=by
 let F:= Γcut σ C f i
 have hp(l):tipI F l=∑ j∈ τ i,(C j i) • tipI f (j::l):=by
    rw [(tip_bank _ (fun j x=> C j i • cutI f j x) (fun j _=>River.scale (h.flow _) _)).2]; simp_rw [tip_C (h.flow _)]; rfl
 have hs(Z:Finset I):snow σ C (fun l=>∑ j∈ Z,C j i • tipI f (j::l)) s=∑ j∈Z,C j i • snow σ C (fun l=>tipI f (j::l)) s:=by
    induction Z using Finset.induction_on with|empty=> simp only [sum_empty]; exact women ..|insert j u h ih=> simp_rw [sum_insert h]; let F:=fun l=>tipI f (j::l); let U:=fun l=>∑ j∈ u,C j i • tipI f (j::l); exact (tally_ADD σ C (C j i • F) U s).trans (congrArg₂ (·+·) (tally_scale σ C (C j i) F s) ih) -- pointwise Pi.add defeq failure
 exact (hs _).symm.trans (rer σ C s fun l _=>(hp l).symm)
lemma cut_l (h:River f)(i:I)(u: W (i::s) f g) : W s (Γcut σ C f i) (cutI g i):=fun j t=> (u (i::j) (List.cons_sublist_cons.mpr t)).trans (Ω_tip _ _ h i)
end storm
end YM.CF.Roots

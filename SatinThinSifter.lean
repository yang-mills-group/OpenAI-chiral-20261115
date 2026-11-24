import SatinThinLeaflet
-- two keys per root. At distinct-key uses can overwrite from old gaps.
set_option maxHeartbeats 700000
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.QuadClock
open Mew Function Finset Py Lattice MeasureTheory
open scoped Matrix BigOperators ContDiff Classical Topology
set_option autoImplicit false
attribute [-instance] instDecidableEqLex
variable {J I E: Type}[Fintype J][Fintype I][LinearOrder J][LinearOrder I][NormedAddCommGroup E] [NormedSpace ℂ E]
variable {h h':Key J→ E}
local notation "Υ" => Article I
local notation "Ξ"=> Key (Article I)
abbrev regards (z:Key J)(l:List J):=∀ i:J,i∉l→ z i=0
lemma blankV (l:List J)(p:∀ z,regards z l→ h z=h' z) : tipI h l=tipI h' l:=by
 induction l generalizing h h' with
 | nil=> exact p 0 (fun _ _=>rfl)
 | cons j l ih=> refine ih fun z w=> integral_congr_ae (ae_of_all _ fun v=>congrArg _ (p _ ?_)); intro x h; rw [update_of_ne (show x≠j from by rintro rfl; exact h (List.mem_cons_self ..))]; exact w _ (fun v=>h (List.mem_cons_of_mem _ v))
local notation "P" i:max=>phaseMark i 0
local notation "Q" i:max=>phaseMark i 1
abbrev toPrin(x:Υ):=phaseMark (host x) 0
abbrev toGap(x:Υ):=phaseMark (host x) 1
def unison (z:Ξ)(i:Υ):ℂ:=if layer i=0 then z i+z (toGap i) else 0
def strike (z:Ξ)(i:Υ):ℂ:=if layer i=0 then -z (toGap i) else 0
lemma noteP(z:Ξ)(i:I): unison z (P i)=z (P i)+z (Q i):=if_pos rfl
lemma noteQ(z:Ξ)(i:I): unison z (Q i)=0:=if_neg (by show (1:Fin 2)≠0; decide)
lemma note_P(z:Ξ)(i:I): strike z (P i)= -z (Q i):=if_pos rfl
lemma note_Q(z:Ξ)(i:I): strike z (Q i)=0:=if_neg (by show (1:Fin 2)≠0; decide)
lemma note_dif : Differentiable ℂ (unison (I:=I)):= differentiable_pi.mpr fun j=> art_fork (p:=fun i:Υ=>Differentiable ℂ (fun z:Ξ=>unison z i)) (fun i=>by simp_rw [noteP]; exact (differentiable_apply _).add (differentiable_apply _)) (fun _=>by simp_rw [noteQ]; exact differentiable_const _) j
lemma strike_dif : Differentiable ℂ (strike (I:=I)):= differentiable_pi.mpr fun j=> art_fork (p:=fun i:Υ=>Differentiable ℂ (fun z:Ξ=>strike z i)) (fun i=>by simp_rw [note_P]; exact (differentiable_apply _).neg) (fun _=> by simp_rw [note_Q]; exact differentiable_const _) j
lemma unison0:unison (0:Key (Article I))=0:=by
 funext j; unfold unison; split; simp; rfl
lemma strike0:strike (0:Key (Article I))=0:=by
 funext j; unfold strike; split; simp; rfl
lemma host_dif{p q:Υ}(t:host p≠host q):p≠q:=fun v=> t (congrArg _ v)
lemma gap_dif(x y:I): Q x ≠ P y:=fun v=> (by decide : (1:Fin 2) ≠0) (congrArg layer v)
lemma together (z:Key (Article I))(v:ℂ)(x:Article I)(p:∀ i:Article I, host i=host x → z i=0): unison (update z x v)=update (unison z) (toPrin x) v:=by
 funext i; refine art_fork (p:=fun i=> _= (update (unison z) (toPrin x) v i)) ?_ ?_ i
 · intro j; rw [noteP]; by_cases t: j=host x; swap; · rw [update_of_ne (host_dif (p:=P j) (q:=x) t),update_of_ne (show Q j ≠ x from host_dif (p:=Q j) (q:=x) t), update_of_ne (host_dif (show host (P j) ≠ host (toPrin x) from t)),noteP]
   subst j; rw [show phaseMark (host x) 0=toPrin x from rfl, update_self]; clear i
   rw [recover_art x]; generalize hk:host x=y; generalize he:layer x=l; have hz (i a):=p i (show host i=host x from a)
   fin_cases l
   · change update z (P y) v (P y)+ update z (P y) v (Q y)=v; rw [update_self,update_of_ne (gap_dif y y),p (Q y) hk.symm,add_zero]
   change update z (Q y) v (P y)+ update z (Q y) v (Q y)=v; rw [update_self,update_of_ne (gap_dif y y).symm,p (P y) hk.symm,zero_add]
 intro j; rw [noteQ,update_of_ne (show Q j ≠ toPrin x from gap_dif j (host x)), noteQ]
lemma strike_update0 (z:Ξ)(i:I)(v:ℂ): strike (update z (P i) v)=strike z:=by
 funext j; unfold strike; split; rw [update_of_ne (show toGap j ≠ P i from gap_dif (host j) i)]; rfl -- toGap reducible?
lemma strike_update1 (z:Ξ)(i:I)(v:ℂ): strike (update z (Q i) v)=update (strike z) (P i) (-v):=by
 funext j; refine art_fork (p:=fun j=>_=update (strike z) (P i) (-v) j) ?_ ?_ j
 · intro j; by_cases t:j=i; subst j; rw [note_P,update_self,update_self]; rw [note_P,update_of_ne (host_dif (show host (Q j) ≠ host (Q i) from t)), update_of_ne (host_dif (show host (P j) ≠ host (P i) from t)),note_P]
 intro j; rw [note_Q, update_of_ne (gap_dif j i), note_Q]
def CasePage(l: List (Article I)) := (l.map host).Nodup
lemma CasePage.keys {l:List (Article I)} (x:CasePage l): l.Nodup:=List.Nodup.of_map _ (show (l.map host).Nodup from x)
lemma CasePage.trim {l l':List (Article I)}(p:CasePage l)(v:l'.Sublist l): CasePage l':=(v.map _).nodup p
lemma united (f:Key (Article I)→E) (l:List (Article I))(p:CasePage l): tipI (f ∘ unison) l=tipI f (l.map toPrin):=by
 induction l generalizing f with
 | nil=> change f (unison 0)=f 0; rw [unison0]
 | cons i l ih=> obtain ⟨hz,h⟩:= List.nodup_cons.mp (show (host i::l.map host).Nodup from p); refine (blankV l (h:=cutI (f∘unison) i) (h':= cutI f (toPrin i) ∘ unison) ?_).trans (ih _ h); intro z t; apply integral_congr_ae; refine ae_of_all _ fun v=>?_ ; dsimp only [Function.comp_apply]; rw [together z (homeB v) i (fun j u=>t _ (fun v=>hz (List.mem_map.mpr ⟨j,v,u⟩)))]
lemma case_fork {l:List Υ}{i:Υ}: CasePage (i::l) ↔ (host i∉l.map host ∧ CasePage l):=List.nodup_cons
#print axioms united
end YM.CF.QuadClock

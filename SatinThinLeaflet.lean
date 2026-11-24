import SatinThinStitch
-- tip formulae (order-specific complex derivatives). Variant Mew.Brook
set_option maxHeartbeats 700000
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.QuadClock
open Mew Function Finset Py Lattice MeasureTheory
open scoped Matrix BigOperators ContDiff Classical Topology
set_option autoImplicit false
attribute [-instance] instDecidableEqLex
variable {J I E: Type}[Fintype J][Fintype I][LinearOrder J][LinearOrder I]{F G: List J→ E}
variable [NormedAddCommGroup E] [NormedSpace ℂ E][CompleteSpace E]
local notation "Υ" => Key J
local notation "Ξ"=> Key (Article I)
variable (w: J→ ℂ) {f h: Key J→E}
def spray (t:List J→ E) : List J→E | []=>t []| j::l=> w j • spray t l+ spray (fun i=> t (j::i)) l
lemma spray_e (l:List J)(p:∀i:List J,i.Sublist l→F i=G i): spray w F l=spray w G l:=by
 induction l generalizing F G with
 | nil=> exact p _ (List.Sublist.refl _)
 | cons i l ih=>rw [spray,spray, ih (fun j p'=>p j (.cons i p')), ih (fun j p'=>p (i::j) (.cons_cons i p'))] -- tune
lemma mixed_river {f: Key J→ℂ}(hp: River f)(h':River h): River (fun x=> f x • h x):= ⟨hp.shore.smul h'.shore,fun i p j x l=> (hp.slope i p j x l).smul (h'.slope i p j x l)⟩
-- formula linear exp
noncomputable def creed (z:Key J):ℂ:=∑ i:J,z i*w i
noncomputable abbrev oath(w:J→ℂ):=Complex.exp ∘ creed w
lemma river_oath : River (oath w):= river_all _ ((show Differentiable ℂ (creed w) from Differentiable.fun_sum (fun i _=> Differentiable.mul_const (differentiable_apply i) _)).cexp) -- naming
lemma height_oath (i:J) (x:Key J): HasDerivAt (fun z=> (oath w) (update x i z)) (w i * oath w (dune i x)) 0:=by
 let r(y:ℂ):= update x i y; have hu(a:J)(l:a∈(univ.erase i)): (fun y=>r y a*w a)= fun _=>x a*w a:=funext fun y=>congrArg (·*w a) (update_of_ne (mem_erase.mp l).1 ..)
 have ht:HasDerivAt (fun y=> ∑ i':J, r y i'*w i') (w i) 0:=by
    simp_rw [← add_sum_erase _ (fun i':J=> _*w i') (mem_univ i), show ∀ y, r y i=y from fun y=> update_self i y x]
    have heφ {Q:Finset J}(p:Q=univ.erase i): (fun y=> ∑ j∈ Q,r y j*w j)=fun _=> ∑ j∈Q,x j*w j:= funext fun y=> sum_congr rfl fun j v=> congrFun (hu j (p ▸ v)) y
    simp_rw [show ∀ y, ∑ j∈univ.erase i,r y j*w j= ∑ j∈univ.erase i, x j*w j from congrFun (heφ rfl)]
    simpa using (((hasDerivAt_id' (0:ℂ)).mul_const (w i)).add_const (∑ j∈univ.erase i,x j*w j))
 change HasDerivAt (fun y=> Complex.exp (∑ i':J, r y i'*w i')) _ _
 rw [mul_comm]; exact ht.cexp
lemma tip_flow (p:River h) (l:List J)(t:l.Nodup): tipI (fun z=> oath w z • h z) l= spray w (tipI h) l:=by
 induction l generalizing h with
 | nil=> change Complex.exp (creed w 0) • _=_; simp [creed]; rfl -- tune
 | cons i l ih=>
    obtain ⟨x,z⟩:= List.nodup_cons.mp t; let y:=mixed_river (river_oath w) p
    let X(k:Υ):= oath w k • h k; let H(k:Υ):= oath w k • cutI h i k
    let H₀(k:Υ):= w i • X (dune i k); let H₁(k:Υ):= oath w (dune i k) • cutI h i k
    have hq:= mixed_river ((river_oath w).stay i) (p.flow i)
    have hf: Set.EqOn (cutI X i) (fun z=>H₀ z+H₁ z) (hill J):=fun k p'=>by
       refine (mitt y p' i).deriv.symm.trans ((height_oath w i k).smul (mitt p p' i)).deriv |>.trans ?_
       dsimp only [H₀,H₁,X]; rw [smul_smul]; dsimp only [dune]; rw [add_comm] -- order tune
    have hp:tipI H₁ l=tipI H l:=by
       have hz(z):cutI h i (dune i z)=cutI h i z:=by unfold cutI; apply integral_congr_ae; refine ae_of_all _ fun _=>?_ ; unfold dune; simp only [update_idem]
       rw [show H₁=H∘dune i from funext fun z=> by simp only [H₁,H,Function.comp_apply,hz]]; exact tip_V i l x -- h implicit?
    change tipI (cutI X i) l=_
    rw [show tipI _ l=tipI (fun z=> H₀ z+H₁ z) l from lace_C l hf roots,tip_A (f:=H₀) (g:=H₁) ((y.stay i).scale (w i)) hq,show tipI H₀ l=w i • tipI (X ∘ dune i) l from tip_C (y.stay i) (w i) l,hp,tip_V _ _ x, spray]; rw [show tipI X l= _ from ih p z, show tipI H l=_ from ih (p.flow i) z]; rfl
lemma tip_constant_nil (a:E): ∀ (l:List J),tipI (fun _:Key J=> a) l=if l=[] then a else 0
 | []=> by rw [if_pos rfl]; rfl
 | i::l=>by
    refine (show tipI _ l=_ from (lace_C l (show Set.EqOn (cutI (fun _:Key J=>a) i) (fun _=>0) (hill J) from fun x hx=> (mitt (zeroR _) hx i).deriv.symm.trans (deriv_const ..)) roots)).trans ((tip_0 l).trans ?_)
    rw [if_neg (List.cons_ne_nil _ _)]
lemma tip_oath (a:E)(l:List J)(t:l.Nodup): tipI (fun z=> oath w z • a) l= (l.map w).prod • a:=by
 rw [tip_flow _ (zeroR _) _ t]; have h(g:List J→E)(i:List J)(p:∀ x,g x=0): spray w g i=0:=by induction i generalizing g with|nil=>exact p _|cons i l ih=> rw [spray, ih g p, ih (fun u=>g (i::u)) (fun u=>p (i::u)), smul_zero,add_zero]
 induction l with
 | nil=>simpa [spray,tipI,lance]
 | cons j l ih=> rw [spray,h (fun i=> tipI _ (j::i)) _ (fun i=> by simpa [tip_constant_nil]),add_zero,ih ((List.nodup_cons.mp t).2),smul_smul,List.map_cons,List.prod_cons]

end YM.CF.QuadClock

import YM.CF.Mew.Lace
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mew
open Function Set Metric Filter MeasureTheory Finset
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E F N :Type*}[Fintype I][DecidableEq I][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F]
variable [NormedCommRing N][NormedAlgebra ℂ N][CompleteSpace N]
variable {f g u v:Key I→E}{a b a' b': Key I→N}{s t:List I}
-- shift by scale coordinates multipliers per marker, NO bound on wabs. 
local notation "sg" i=> i -- trim
abbrev South(w:I→ℂ)(s:List I)(f g:Key I→E):Prop:=∀ i:List I,i.Sublist s → tipI g i = (i.map w).prod • tipI f i
lemma beforeA(w:I→ℂ)(h:t.Sublist s)(p:South w s f g) : South w t f g:=fun i u=>p i (List.Sublist.trans u h)
lemma south_V(i:I)(h:i∉s)(w:I→ℂ)(p:South w s f g): South w s (f∘dune i) (g∘dune i):=fun j q=>by rw [tip_V i j (fun p=>h (q.subset p)),tip_V i j (fun p=>h (q.subset p))]; exact p j q
lemma south_D(h:River f)(i:I)(w:I→ℂ)(p:South w (i::s) f g): South w s (fun x=> w i • cutI f i x) (cutI g i):=by
 intro j q; have he:=p (i::j) (List.cons_sublist_cons.mpr q); change tipI _ _=_; rw [tip_C (h.flow i),smul_smul]; change tipI (cutI g i) j=(List.map w _).prod • tipI (cutI f i) j at he; rw [List.map_cons,List.prod_cons,mul_comm] at he; exact he
lemma southern(w:I→ℂ)(p:South w s f g)(l:South w s u v)(he:River f)(hu:River u)(hg:River g)(hv: River v): South w s (fun x=>f x+u x) (fun x=>g x+v x):=fun j hi=>by rw [tip_A hg hv, tip_A he hu, p j hi, l j hi, smul_add]
lemma south_J(w:I→ℂ)(p:South w s f g)(he:River f)(hu:River g)(L:E→L[ℂ]F): South w s (L∘ f) (L∘ g):=fun i h=> by
 change lance _ _ 0=_
 rw [sim_H hu L i roots,show tipI (L∘f) i=L (tipI f i) from sim_H he L i roots]; change L (tipI g i)=_; rw [p i h,map_smul]
lemma subt_D (w:I→ℂ)(h:s=[]) (p: f 0 =g 0): South w s f g:=fun i v=>by rw [h] at v; rw [List.sublist_nil.mp v]; simp only [tipI,lance,List.map_nil,List.prod_nil,one_smul]; exact p.symm
lemma south_one (w:I→ℂ)(a:E): South w s (fun _=>a) (fun _=>a):=by
 intro i p; cases i
 · simp
 case cons j l =>
   have he:tipI (fun _=>a) (j::l)=0:=by
      have hc:EqOn (cutI (fun _:Key I=>a) j) (fun _=>0) (hill I):= fun u hu=>(mitt (zeroR _) hu j).deriv.symm.trans (deriv_const ..)
      exact (lace_C l hc roots).trans (tip_0 l)
   rw [he,smul_zero]
lemma River.mul_T(ha:River a)(hb:River b) : River (a*b):=⟨ha.shore.mul hb.shore,fun i p j x g=> (ha.slope i p j x g).mul (hb.slope i p j x g)⟩
lemma tip_mul (ha:River a)(hb:River b)(j:I)(l:List I):tipI (a*b) (j::l)= tipI (cutI a j*(b∘ dune j)) l + tipI ((a ∘ dune j)*cutI b j) l:=by
 let Y:= cutI a j*(b∘ dune j); let U:=(a ∘ dune j)*cutI b j; have ht:EqOn (cutI (a*b) j) (fun i=>Y i+U i) (hill I):= fun t hv=>(mitt (ha.mul_T hb) hv j).deriv.symm.trans ((mitt ha hv j).mul (mitt hb hv j)).deriv
 exact (lace_C l ht roots).trans (tip_A ((ha.flow j).mul_T (hb.stay j)) ((ha.stay j).mul_T (hb.flow j)) l)
lemma south_prod (ha:River a)(hb: River b)(hg:River a')(hl:River b')(w:I→ℂ)(p:s.Nodup)(hx: South w s a a')(hy:South w s b b'): South w s (a*b) (a'*b'):=by
 induction s generalizing a b a' b' with
 | nil => exact subt_D w rfl (by have hf:=hx [] (List.Sublist.refl []); have hg:= hy [] (List.Sublist.refl []); simpa [tipI,lance,hf,hg] using congrArg₂ (· * ·) (Eq.symm hf) (Eq.symm hg)) -- tune Pi eval
 | cons i l ih =>
    have hv:=List.nodup_cons.mp p; have hh:=List.sublist_cons_of_sublist i (List.Sublist.refl l); intro j t; cases t with
    | cons _ t=> exact ih ha hb hg hl hv.2 (beforeA _ hh hx) (beforeA _ hh hy) j t
    | cons_cons _ ht=>
       rw [tip_mul hg hl, tip_mul ha hb]; have hf:=ih ((ha.flow i).scale (w i)) (hb.stay i) (hg.flow i) (hl.stay i) hv.2 (south_D ha i w hx) (south_V i hv.1 w (beforeA w hh hy)) _ ht
       have hQ:=ih (ha.stay i) ((hb.flow i).scale (w i)) (hg.stay i) (hl.flow i) hv.2 (south_V i hv.1 w (beforeA w hh hx)) (south_D hb i w hy) _ ht
       rw [show (fun x=>w i • cutI a i x)*(b ∘ dune i)= (fun x=> w i • (cutI a i*(b ∘ dune i)) x) from funext (fun x=>smul_mul_assoc ..), tip_C (f:=(cutI a i)*(b∘dune i)) ((ha.flow i).mul_T (hb.stay i))] at hf
       rw [show (a ∘ dune i)*(fun x=>w i • cutI b i x)= (fun x=> w i • ((a ∘ dune i)*cutI b i) x) from funext (fun x=>mul_smul_comm ..), tip_C (f:=(a ∘ dune i)*(cutI b i)) ((ha.stay i).mul_T (hb.flow i))] at hQ
       rw [hf,hQ,smul_smul,smul_smul,List.map_cons,List.prod_cons,mul_comm,smul_add]
open NormedSpace
lemma River.exp_V(h:River a):River (exp ∘ a):=⟨(continuous_iff_continuousAt.mpr fun x:N=> (hasFDerivAt_exp (𝕂:=ℂ) (x:=x)).continuousAt).comp_continuousOn h.shore,fun i p j k hk=> (hasFDerivAt_exp (𝕂:=ℂ) (x:=a (update i j k))).differentiableAt.comp k (h.slope _ p _ _ hk)⟩
lemma sailE(h:River a)(j:I)(s:List I):tipI (exp ∘ a) (j::s)=tipI (cutI a j*((exp∘ a)∘ dune j)) s:=by
 apply lace_C s (show EqOn (cutI _ _) _ (hill I) from fun i u=>?_ ) roots
 change cutI (exp ∘ a) j i=_
 rw [← (mitt h.exp_V u j).deriv]; change deriv (exp ∘ (fun w=>a (update i j w))) 0=_; rw [(hasFDerivAt_exp (𝕂:=ℂ)|>.comp_hasDerivAt _ (mitt h u j)).deriv]
 change exp (a (update i j 0)) * cutI a j i=_; exact mul_comm ..
lemma south_e (ha:River a)(hg:River a')(w:I→ℂ)(p:s.Nodup)(hx: South w s a a'): South w s (exp∘a) (exp∘a'):=by
 induction s generalizing a a' with
 | nil=> apply subt_D w rfl; apply congrArg exp; have hp:=hx [] (List.Sublist.refl _); simpa [tipI,lance] using Eq.symm hp
 | cons i l ih=>
   obtain ⟨hf,hv⟩:=List.nodup_cons.mp p; have hA:= ih ha hg hv (beforeA w (List.sublist_cons_of_sublist i (List.Sublist.refl l)) hx); intro y v
   cases v with
   | cons _ t=> exact hA _ t
   | cons_cons _ t=>
      rw [sailE hg, sailE ha]
      have hp:=south_prod ((ha.flow i).scale (w i)) (ha.exp_V.stay i) (hg.flow i) (hg.exp_V.stay i) w hv (south_D ha i w hx) (south_V _ hf w hA) _ t
      rw [show (fun x=>w i • cutI a i x)*((exp∘ a) ∘ dune i)= (fun x=> w i • (cutI a i*((exp∘ a) ∘ dune i)) x) from funext (fun x=>smul_mul_assoc ..), tip_C ((ha.flow i).mul_T (ha.exp_V.stay i)),smul_smul] at hp
      rw [hp, List.map_cons,List.prod_cons,mul_comm (_:ℂ)]
end YM.CF.Mew

import YM.CF.Acorn.Reno
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Lattice Cube Broc Drapes Tulip Peaks Brace Paige Rush Matrix Jet
open scoped Topology Matrix BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L B:Side}{ho:Odd L.val}{T:Script Male}{Y:Pricing j L ho T}{e:ℝ}{m:Side}(g:Grasp Y B e)(n:ℕ)(K:ℝ)(R:Repair j)
abbrev Tier(m B:Side)(n:ℕ)(e p K:ℝ):= newX (pWorks m B e p) (partQ m B e p n K) n
abbrev Senso (m:Side)(g:Grasp Y B e):= Brace.Chord m B e g.baseline
def liftC (ha:e≤R.d)(hb:g.baseline≤ R.d)(i:Senso m g): Loom (idrat (CSide m B)) R.d:=⟨couple i.val.1 i.val.2 i.val.2, Gaze.glimp _ _ _ ⟨i.property.1.shrink ha,fun z i'=>(i.property.2 z i').trans_le hb,fun z i'=>(i.property.2 z i').trans_le hb,fun j=>by rw [sub_self,norm_zero]; exact R.pd⟩ R.pd⟩
lemma lx (ha:e≤R.d)(hb:g.baseline≤ R.d): Cop (newX (weave (idrat (CSide m B)) _) (Me n K R.d _) n) (Tier m B n e g.baseline K) (liftC g R ha hb):=by
 refine ⟨rfl,rfl,?_,fun S x y p=> ?_,fun E _ _ _ V h f u x g=>⟨(u x g).1,(u x g).1,(u x g).2,(u x g).2⟩⟩
 · apply Continuous.subtype_mk; let f(x:Senso m g):=x.val; have he:Continuous f:=continuous_subtype_val; have hx:= continuous_snd.comp he; have hp:= continuous_fst.comp he; exact (hp.prodMk hp).prodMk (hx.prodMk hx)
 let G:=idrat (CSide m B); have ht: cloudG G S=S:=by ext; simp [G,cloudG,filed]
 exact ⟨p.1,ht.symm ▸ (p.1),p.2,ht.symm ▸ (p.2)⟩
def plusC(i: Senso m g) : Brace.Chord m B e g.p:=⟨i.val,i.property.1,fun x y=> (i.property.2 x y).trans_le g.small⟩
lemma cop_t : Cop (Tier m B n e g.p K) (Tier m B n e g.baseline K) (plusC g):=⟨rfl,rfl,continuous_subtype_val.subtype_mk _,fun _ _ _ p=>p, fun _ _ _ _ _ _ _ t=> t⟩ -- lambda
lemma flash_d {Y D G:Type}[Fintype Y][DecidableEq Y][TopologicalSpace D]{X:Draw D}{b:Light Y D G}{F:D→ℂ}{a K:ℝ}{k:ℕ}(h:Screen b X k F a K):Wallet (newX b X k) a K F:=by obtain ⟨F,C,h,p,k⟩:=h; exact ⟨F,C,fun i=> ⟨(h i).pos,(h i).travel,(h i).cont,(h i).sumline,(h i).reads,(h i).plot⟩,p,k⟩
lemma Wallet.pull{Y D E:Type}[Fintype Y][DecidableEq Y][TopologicalSpace D][TopologicalSpace E]{X:Master D Y}{b: Master E Y}{F:D→ℂ}{a K:ℝ}(h:Wallet X a K F){A:E→D}(g:Cop X b A):Wallet b a K (F ∘ A):=by obtain ⟨F,C,h,p,l⟩:=h.screen; exact ⟨_,C,fun i=>(h i).cop g,p,fun i=>l _⟩
lemma Wallet.add{Y D:Type}[Fintype Y][DecidableEq Y][TopologicalSpace D]{X:Master D Y}{F G:D→ℂ}{a K c:ℝ}(h:Wallet X a K F)(g:Wallet X a c G):Wallet X a (K+c) (F+G):=by
 obtain ⟨F',C,h,p,l⟩:=h.screen; obtain ⟨G',D,g,s,q⟩:=g.screen; refine ⟨_,_,fun i=>(h i).sum (g i),?_,?_⟩; intro i; simp only [hitE,mul_add,sum_add_distrib]; exact add_le_add (p i) (s i)
 intro i; rw [Pi.add_apply,l,q]; simp [sum_add_distrib]
lemma exc_shop (hn:1≤K):∃ C:ℝ,0≤C∧∀{N P:Side}(G:Ratio N P),G.count=1→ R.n ≤N.val→∀ i:Male, let X:=newX (weave G R.d) (Me n K R.d G) n; let Y:= (curveD G R.d).home; let Z: Loom G R.d→Op (Iota G):=fun x=> repeated j i G (post x.val); let T:Loom G R.d→Op (Iota G):=fun x=>proto i G (post x.val); Plum X Y (fun x=> quantX (Z x) (T x)) (R.a/2) (4*C) ∧ Plum X Y (fun x=> stackX 0 0 (T x)) (R.a/2) C:=by
 obtain ⟨c,d,H⟩:= cue_top n K R.d R.a R.K (zero_le_one.trans hn) R.pd R.pa -- fix
 let v:ℂ:=(2:ℂ)⁻¹; let L:=c*max R.K (quartzK R.a R.K); set C:= ‖v‖*L; have hp:0≤c:=zero_le_one.trans d; have hC:0≤C:=mul_nonneg (norm_nonneg _) (mul_nonneg hp (le_max_of_le_left R.pK.le))
 refine ⟨C,hC,fun {N P} G he p i=>?_⟩; intro X Y Z T
 have ht:= H G true true (@coatL _ i _ _ G) _ _ (R.cap i G he p)
 have he':= H G true false (fluffy j i G) _ _ (R.sweet i G he p)
 have hg:= H G false false (wheat j i G) _ _ (R.room i G he p); have hh:= H G false false (proto i G) _ _ (R.bodyV i G he p)
 constructor
 · have he:= (((ht.scal v).add (he'.scal v)).add ( (he'.scal v).transposeD.nop)).add (hg.scal v); change Plum X _ _ _ (C+C+C+C) at he; rw [show C+C+C+C=4*C by ring] at he
   convert he using 1; ext x r s; rcases r with ⟨a|a,r⟩ <;> rcases s with ⟨b|b,s⟩ <;> simp only [quantX,cue,stackX,Matrix.of_apply,T,Z,ite_false,ite_true,Bool.true_eq_false,Bool.false_eq_true,true_and,false_and,and_self, Matrix.add_apply,Matrix.smul_apply, Pi.neg_apply, Matrix.neg_apply, Matrix.transpose_apply, Matrix.zero_apply, mul_zero, neg_zero,add_zero, zero_add, smul_eq_mul] <;> simp [fluffy,wheat,wash,charge_p,v,driftB,weldB]
 · have he:=hh.scal v; convert he using 1; ext x r s; unfold stackX cue; by_cases l:r.1=true<;>by_cases h:s.1=true <;> simp [l,h,T,v]
end YM.CF.Acorn

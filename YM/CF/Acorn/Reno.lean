import YM.CF.Acorn.Grill
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Lattice Cube Broc Drapes Tulip Peaks Brace Paige Rush Matrix Jet
open scoped Topology Matrix BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra
variable {n Y D E:Type}[LinearOrder n][Fintype n][Fintype Y][DecidableEq Y][TopologicalSpace D][TopologicalSpace E]{X: Master D Y}{Z: Master E Y}{O:n→Y}{A B:D→ Op (I n)}{a d e c V r:ℝ}
def newX {Y D G:Type}(L:Light Y D G)(Q:Draw D)(k:ℕ):Master D Y:=⟨L.frame,L.rel,L.expands,Q,k⟩
lemma Plum.weak(h:Plum X O A a c)(p:c≤ V)(m:e≤a):Plum X O A e V:=by
 obtain ⟨F,C,h,H,u,Y⟩:= h.hit; refine ⟨F,C,h,(H.lowers (fun S i j=>mul_le_mul_of_nonneg_right (rent_up m _) (h S i j).1.pos)).book p,fun i=>?_,Y⟩; exact (Finset.sum_le_sum (fun S _=>mul_le_mul_of_nonneg_right (rent_up m S) (sum_nonneg (fun j _=>sum_nonneg (fun k _=> (h S j k).1.pos))))).trans ((u i).trans p)
lemma Plum.add(h:Plum X O A a c)(p:Plum X O B a d):Plum X O (fun i=>A i+B i) a (c+d):=by
 obtain ⟨F,C,h,H,T,U⟩:=h.hit; obtain ⟨M,D,p,q,k,l⟩:=p.hit
 refine ⟨fun S x=> F S x+ M S x,C+D,fun S i j=>⟨(h S i j).1.sum (p S i j).1,fun t=>?_⟩,H.pairT q,?_,?_⟩
 · by_cases v:C S i j=0; exact (p S i j).2 (by simpa [v] using t); exact (h S i j).2 v
 · intro i; simp only [hitE,ledgerV,Pi.add_apply,sum_add_distrib,mul_add]; exact add_le_add (T i) (k i)
 intro i; simp [U i, l i,sum_add_distrib]
lemma Plum.pull (h: Plum X O A a c) (f:E→D) (g:Cop X Z f): Plum Z O (A ∘ f) a c:= by obtain ⟨F,C,h,K,s,l⟩:=h.hit; exact ⟨_,C,(fun S i j=> show Pro Z S (fun x=>F S (f x) i j) _ ∧ _ from ⟨(h S i j).1.cop g,(h S i j).2⟩),K,s,fun x=>l _⟩ -- meta
lemma Plum.scal(h:Plum X O A a c)(v:ℂ): Plum X O (fun x=> v • A x) a (‖v‖*c):=by
 obtain ⟨F,C,h,H,T,U⟩:= h.hit; refine ⟨fun S x=>v • F S x,fun S i j=>‖v‖*C S i j,fun S i j=>⟨(h S i j).1.sc v, fun p=> (h S i j).2 (right_ne_zero_of_mul p)⟩,H.funds (norm_nonneg _),fun i=>?_,fun i=>?_⟩
 · unfold hitE ledgerV; simp_rw [← Finset.mul_sum,mul_left_comm (Branch.rent ..) ‖v‖ _, ← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (T i) (norm_nonneg v)
 rw [U,smul_sum]
lemma Plum.transposeD(h:Plum X O A a c): Plum X O (fun x=> (A x)ᵀ) a c:=by
 obtain ⟨F,C,h,H,T,U⟩:=h.hit; refine ⟨fun S x=>(F S x)ᵀ,fun S=>Function.swap (C S),fun S i j=>?_,H.flip,?_,?_⟩
 · exact ⟨(h S j i).1,fun p=> And.symm ((h S j i).2 p)⟩
 · intro i; have he(S):ledgerV (Function.swap (C S))=ledgerV (C S):=by rw [ledgerV,sum_comm]; rfl
   simp_rw [he]; exact T i
 intro i; rw [U,Matrix.transpose_sum]

def cue(u v:Bool)(A:Op n) : Op (I n):= Matrix.of fun i j=> if i.1=u∧ j.1=v then A i.2 j.2 else 0
def skewer (i j:Bool)(C:Seal Y → Toll n): Seal Y → Toll (I n):= fun s x y=> if x.1=i ∧ y.1=j then C s x.2 y.2 else 0
lemma ledger_cue (i j:Bool){C: Seal Y → Toll n}(h:Ledger a C c): Ledger a (skewer i j C) c:=by
 refine ⟨h.posP,fun x=>?_,fun y=>?_⟩ <;> cases i <;> cases j
 all_goals first| (obtain ⟨x|x,p⟩:= x; all_goals simp [saleM,Fintype.sum_prod_type,skewer,h.posP]; try exact h.rows p)| (obtain ⟨x|x,p⟩:= y; all_goals simp [saleM,Fintype.sum_prod_type,skewer,h.posP]; try exact h.cols p)
lemma ledger_c (C:Toll n)(i j:Bool): ledgerV (fun x y:I n=>if x.1=i∧y.1=j then C x.2 y.2 else 0)=ledgerV C:=by cases i<;>cases j<;>simp [ledgerV,Fintype.sum_prod_type]
lemma cue_top(k:ℕ)(w e a c:ℝ)(u:0≤ w)(g:0<e)(h:0<a):∃ C:ℝ,1≤C ∧∀ {N P:Side}(G:Ratio N P) i j (A:Bale N P→Op (Iota G))(U V:AxisT), Crown (badge (zoneP G e)) (rope G U e) (rope G V e) a c (fun x=> A x.val)→ Plum (newX (weave G e) (Me k w e G) k) (curveD G e).home (fun x=>cue i j (A (post x.val))) (a/2) (C*(max c (quartzK a c))):=by
 obtain ⟨B,p,H⟩:=blend_r w u k; let t:ℝ:=(1+2^k/e)^k; let v:= max 1 (composeCost k t B); have hx:1≤v:=le_max_left ..; have hv:0≤v:=zero_le_one.trans hx
 refine ⟨v,hx,fun {N P} G i j A U V q=>?_⟩
 obtain ⟨F,C,hF,hC,K⟩:=q; let Y:=Seal (Site (More P))
 let S:= Loom G e; let f(x:S): TopK G e:=⟨post x.val,x.val,x.property,by simpa using g⟩; let T (s:Y)(x:S):= F s (f x)
 have px(s:Y)(i j:Iota G): Pro (newX (weave G e) (Me k w e G) k) s (fun x=> T s x i j) (v*C s i j):=by
    let Φ:= fun x=> F s x i j; let p:= (hF s).expo i j; let K:= C s i j
    refine ⟨mul_nonneg hv p.positive,fun h=> (p.triggered (right_ne_zero_of_mul h)).1,p.connected.comp ((post_c.comp continuous_subtype_val).subtype_mk _),fun x=>(p.bounded _).trans (le_mul_of_one_le_left p.positive hx),?_,?_⟩
    · intro x y e'; have hv:= p.variation (f x) (f y); rw [show (curveD G e).eval s (f x) (f y)=0 from (by change bookK _ _ _ s / _=0; rw [paid_zero G e x y s e',zero_div]),mul_zero] at hv; exact sub_eq_zero.mp (norm_le_zero_iff.mp hv)
    intro E _ _ _ L h d q x l
    let X(y:E):=post (d y).val; have hy: Allows k X x B:= H E _ _ (fun x=>(d x).val) x (q x l).1 (q x l).2.1 (q x l).2.2.1 (q x l).2.2.2
    have hk: ball (X x) e ⊆ zoneP G e:=fun z p=>⟨(d x).val,(d x).property, (mem_ball_iff_norm|>.mp p)⟩
    have ht':Allows k (equalizer Φ ∘ X) x (composeCost k (K*t) B):=(allows_looks (hF s|>.fuel i j) p.connected hk g k p.bounded).comp (f:=X) hy
    refine (ht'.mono ?_).germ ?_
    · rw [show composeCost k (K*t) B=composeCost k t B*K by unfold composeCost; ring]; exact mul_le_mul_of_nonneg_right (le_max_right ..) p.positive
    filter_upwards [] with z; exact dif_pos (f (d z)).property
 let D(s:Y)(r t:I (Iota G)):= if r.1=i ∧ t.1=j then C s r.2 t.2 else 0
 have hL:Ledger a D c:=ledger_cue i j hC
 let Y'(s:Y)(x y):=v*D s x y
 refine ⟨fun S x=>cue i j (T S x),Y',fun S x y=>⟨?_,?_⟩,((hL.funds hv).lowers ?_).book (mul_le_mul_of_nonneg_left (le_max_left ..) hv),fun x=>?_,fun x=>?_⟩
 · by_cases e:x.1=i∧y.1=j; simpa [Y',D,cue,e] using px S x.2 y.2
   simp_rw [cue,Y',D,Matrix.of_apply,if_neg e,mul_zero]; have hk' : ‖(0:ℂ)‖=0:= norm_zero; exact hk' ▸ Pro.nonzero _ (by simp)
 · intro p; unfold Y' D at p; split at p; rename_i ht; exact (((hF _).expo _ _).triggered (right_ne_zero_of_mul p)).2; exfalso; simp at p
 · intro S x y; apply mul_le_mul_of_nonneg_right (rent_up (show a/2≤a from (half_lt_self h).le) _) ; refine mul_nonneg hv ?_; unfold D; split; exact (hF S).nonn _ _; rfl
 · have ht(S):ledgerV (Y' S)=v*ledgerV (C S):=by
      unfold Y' ledgerV; simp only [← Finset.mul_sum]; exact congrArg (fun p=>v*p) (ledger_c (C S) i j)
   unfold hitE; simp_rw [ht,mul_left_comm _ v,←mul_sum]; apply mul_le_mul_of_nonneg_left _ hv; exact (Branch.tall (s:=rope G U e) (P:=F) (fun S=>(hF S).toTicket) hC h (cD G e) quota_p.le x).trans (le_max_right ..)
 have he:= K (f x); change cue i j _=_; rw [show A (post _)= _ from he]; ext b t; by_cases h:b.1=i∧ t.1=j <;> simp [cue,h,Matrix.sum_apply,T]
end YM.CF.Acorn

import YM.CF.Scroll.Vines
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scroll
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable {b r:Bool}{N P: Side}(G:Ratio N P)(ho:Odd G.count.val)(a:Shape)(u:ColorT b)(U:UNI SpinIdx)(p:JetS a.s b r U)
def lotX(x:Sew N P): Sew N P:= (stanza G a u x.1, fume u (a.broad G) x.2.1, fume u a x.2.2)
lemma winK {I J: Type*}[Fintype I][Fintype J][DecidableEq I][DecidableEq J](A:UNI I)(u: UNI J)(b: Bool)(X:Op I)(Y:Op J): let U:UNI (I×J):=⟨A.val ⊗ₖ u.val,Matrix.kronecker_mem_unitary A.property u.property⟩
     congrC U (windX b (X ⊗ₖ Y))= congrC A (windX b X) ⊗ₖ congrC u (windX b Y):=by
 intro V
 unfold congrC; rw [show windX b (X ⊗ₖ Y)=windX b X ⊗ₖ windX b Y from (by cases b; exact (rfl : windX false (X ⊗ₖ Y)=windX false X ⊗ₖ windX false Y); exact (op_cc_kron X Y : windX true (X ⊗ₖ Y)= windX true X ⊗ₖ windX true Y))]; unfold V; dsimp only; rw [←Matrix.kroneckerMap_transpose,op_kron_mul,op_kron_mul]
include p
lemma congL (x: Site N)(v:Ballot): congrC (milU a U u x) (windX b (localPair v.val))=localPair (u.X v).val:=by
 have hx: ∀ Y,congrC (milU a U u x) Y=congrC (spinQ U u) Y:=by
   intro Y; simp only [congrC,milU,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,a.reflex,one_smul]
 rw [hx]; unfold localPair; rw [show congrC (spinQ _ _) _= _ from winK U u.V b spinJ (Pair.fullM v.val),u.facing]
 congr 1; unfold congrC; rw [show windX b spinJ=spinJ from (by cases b; rfl; exact spinJ_real),p.justice,mul_assoc,show cc U.val * U.valᵀ=1 from ?_,mul_one]
 rw [show U.valᵀ=star (cc U.val) by ext; simp]; exact (ccU U).property.2
lemma taxL (k:Bool): sings b (pflux a G U u) (lobe G k)=lobe G (r.xor k):=by
 have he(k:Bool)(i j:Hand G):tap ((lobe G k).submatrix (abbe G).symm (abbe G).symm) i j=if i=j then angle k ⊗ₖ (1:Op Slot) else 0:=by
    ext ⟨x,q⟩ ⟨y,v⟩; unfold lobe; rw [pilesV]; rcases i with ⟨w,a⟩; rcases j with ⟨z,b⟩; change jump (Equiv.refl _) (fun _=>sA k _) (w,a,x) (z,b,y)*_=_ ; by_cases h:w=z <;> by_cases g:a=b <;> simp [g,h,sA,slashA,jump_apply,Fir.s_app] -- tune
    left; rfl
 apply Epin G; rw [port_back]
 let F(i):= (lobe G i).submatrix (abbe G).symm (abbe G).symm
 suffices H:∀ i j:Hand G,tap (sings b (fros a G U u) (F k)) i j=tap (F (r.xor k)) i j from by ext ⟨i,r⟩ ⟨j,w⟩; exact congr_fun (congr_fun (H i j) r) w
 intro i j; unfold fros F; rw [tap_sg,he,he]; by_cases h:i=j; swap; rw [if_neg h,if_neg ((paceU ..).injective.ne h),win_z,mul_zero,zero_mul]
 subst i; simp only [ite_true]; change sings b (milU a U u j.1) _= _; rw [wingM,wingK, angleX p,singT b u.V,win_i,map_one]
include ho
lemma tyL (k:Bool)(x:Sew N P): congrC (pflux a G U u) (windX b (squareD G k (post x)))= squareD G k (post (lotX G a u x)):=by
 let T:= paceU a G; let F(i:Hand G):=(milU a U u i.1).val; let Y:=tableD G k (post x)
 let J:= jump (Equiv.refl (Hand G)) Y; let W:=jump T F
 have he : windX b (squareD G k (post x))=(jump (Equiv.refl (Hand G)) (fun i=> windX b (Y i))).submatrix (abbe G) (abbe G):=by
   cases b <;> ext q r; rfl
   simp only [windX, squareD,readK,ite_true,Matrix.submatrix_apply,cc_apply,jump_apply]; split_ifs <;>first|rfl|simp
 unfold congrC; rw [he]
 change (W.submatrix _ _)*_*((Wᵀ).submatrix _ _)=_ -- tune
 rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
 have ht : Wᵀ=jump T.symm fun i=> (F (T.symm i))ᵀ := by change Wᵀ=_; ext ⟨i,q⟩ ⟨j,v⟩; by_cases h:T j=i <;> simp [h,W,jump_apply,Equiv.symm_apply_eq,Matrix.transpose_apply,eq_comm (a:=j) (b:=T.symm i),eq_comm (a:=i)]; rw [←h,T.symm_apply_apply]
 rw [ht]; simp only [W, jump_mul, Equiv.trans_refl, Equiv.self_trans_symm,Equiv.symm_apply_apply]
 unfold squareD readK; congr 1; congr 1; funext i
 have hK : (a.broad G).anon P (node (isle G i))=node (isle G (paceU a G i)):=by rw [← Shape.nodex,Shape.folds a G ho]; rfl
 cases k
 · change congrC (milU a U u i.1) (windX b (localPair (hook x.2.2 (node ((paceU a G i).1)))))=localPair (u.X (x.2.2 (a.anon N (node i.1)))).val
   rw [← a.nodex]; exact congL a u U p .. -- tune
 change congrC (milU a U u i.1) (windX b (localPair (hook x.2.1 (node (isle G _)))))=localPair (u.X (x.2.1 ((a.broad G).anon P (node (isle G i))))).val; rw [hK]; exact congL a u U p ..
lemma clothing(j:ℕ)(M:Male)(x:Nom N P): sings b (pflux a G U u) (cloth j M G (unionP x))=cloth j M G (unionP (stanza G a u x)):=by
  let f:=tub (brix j G.count); let V:=pflux a G U u; unfold Peaks.cloth; dsimp only
  have hp:=(mosaicS G ho a u U true false f x (BV a.s G.count ho j b U) (cBrix j G.count ho).sumK) -- syntax eta
  unfold f at hp; simp only [singT,win_a,win_m,map_add,map_mul]; simp_rw [←singT _ (pflux a G U u),taxL _ a u U p,hp]
  cases r; rfl; exact add_comm ..
end YM.CF.Scroll

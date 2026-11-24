import YM.CF.Scroll.Mug
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scroll
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable {b r:Bool}{N P: Side}(G:Ratio N P)(ho:Odd G.count.val)(a:Shape)(u:ColorT b)(U:UNI SpinIdx)(p:JetS a.s b r U)
abbrev Glove:= Hand G × QuiltF
def paceU(a:Shape)(G:Ratio N P): Equiv.Perm (Hand G):=(Tofu a N).prodCongr (a.s.actEquiv (R:=Per G.count)).toEquiv
def fros (a:Shape)(G:Ratio N P){p:Bool}(U: UNI SpinIdx)(t:ColorT p): UNI (Glove G):= portX (paceU a G) (fun i=>milU a U t i.1)
def pflux (a:Shape)(G:Ratio N P){p:Bool}(U:UNI SpinIdx)(t:ColorT p): UNI (Iota G) := ⟨(fros a G U t).val.submatrix (abbe G) (abbe G),by apply Matrix.mem_unitaryGroup_iff.mpr; change ((fros ..).val.submatrix _ _)*(star (fros ..).val).submatrix _ _=_; rw [Matrix.submatrix_mul_equiv,(fros a G U t).property.2]; ext; simp [Matrix.one_apply]⟩ -- tune
lemma subPort (A:Op (Glove G)) : sings b (pflux a G U u) (A.submatrix (abbe G) (abbe G))=(sings b (fros a G U u) A).submatrix (abbe G) (abbe G):=by
 set Y:= A.submatrix _ _; have hx:windX b Y=(windX b A).submatrix (abbe G) (abbe G):=by cases b<;>rfl
 rw [singT,singT,hx,twist_formula,twist_formula]; change _*(star (fros a G U u).val).submatrix _ _ = _; unfold pflux; dsimp only; rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
lemma port_back(A:Op (Iota G)):(sings b (pflux a G U u) A).submatrix (abbe G).symm (abbe G).symm= sings b (fros a G U u) (A.submatrix (abbe G).symm (abbe G).symm):=by
 let F:=A.submatrix (abbe G).symm (abbe G).symm
 have hx:=subPort G a u U F; rw [show F.submatrix (abbe G) (abbe G)=A by simp [F]] at hx; rw [hx]; simp [F]
lemma Epin (A B:Op (Iota G))(p: A.submatrix (abbe G).symm (abbe G).symm=B.submatrix (abbe G).symm (abbe G).symm): A=B:=by ext i j; simpa using congr_fun (congr_fun p (abbe G i)) (abbe G j)
include ho
lemma puff : (pflux a G U u).val= foot G (prepU (a.broad G) U u P).val:=by
  apply Epin G; ext ⟨⟨x,v⟩,i⟩ ⟨⟨y,q⟩,j⟩
  let A:= Shape.broad G a
  change (fros _ _ _ _).val (abbe G _) (abbe G _)=(mealU A _ _ _).val _ _; rw [show abbe G _ =_ from Equiv.apply_symm_apply (abbe G) ((x,v),i),show abbe G _=_ from Equiv.apply_symm_apply (abbe G) ((y,q),j)]
  unfold fros mealU portX; dsimp only
  rw [jump_apply,jump_apply]; change (if (a.mills N x,a.s.act v)=(y,q) then _ else _)=(if A.mills P (isle G (x,v))=isle G (y,q) then ((milU ..).val) i j else _); rw [Shape.folds a G ho]; by_cases h:(a.mills N x,a.s.act v)=(y,q); swap; rw [if_neg h,if_neg ((isle G).injective.ne h)]
  rw [if_pos h,if_pos (congrArg (isle G) h)]; unfold milU; change _=((a.broad G).payA (isle G (x,v)) • (spinQ U u).val) i j; rw [Shape.tolls _ G ho]
lemma portFoot (F:Op (Single P)): sings b (pflux a G U u) (foot G F)= foot G (sings b (prepU (a.broad G) U u P) F):=by
 have he:windX b (foot G F)=foot G (windX b F):=by cases b<;>rfl
 rw [singT,singT,he,twist_formula,twist_formula,puff _ ho, show ∀ X:Op (Single P),star (foot G X)=foot G (star X) from fun _=>rfl,←foot_mul,←foot_mul]
omit ho
def stanza (S:Nom N P) : Nom N P:= (stir u (a.broad G) S.1,stir u a S.2)
lemma clampS (F:Op (Single N)): sings b (pflux a G U u) (endorse G F)=endorse G (sings b (prepU a U u N) F):=by
 obtain ⟨F,rfl⟩:= (love N).surjective F
 rw [show (love N).toRingEquiv F=love N F from rfl]; rw [wingX]; apply Epin G; rw [port_back]
 have he(X:Op (Model N))(x y:Hand G): tap ((endorse G (love N X)).submatrix (abbe G).symm (abbe G).symm) x y= if x.2=0∧y.2=0 then tap X x.1 y.1 else 0:=by
    ext i j; change (if en G _∧ en G _ then _ else (0:ℂ))=_; by_cases p:x.2=0∧y.2=0; rw [if_pos p,if_pos (show en G ((abbe G).symm (x,i)) ∧ en G ((abbe G).symm (y,j)) from p)]; rfl
    rw [if_neg p,if_neg (show ¬(en G ((abbe G).symm (x,i)) ∧ en G ((abbe G).symm (y,j))) from p)]; rfl
 let P:=sings b (mealU a U u N) F; let K:= fun X:Op (Model N)=> (endorse G (love N X)).submatrix (abbe G).symm (abbe G).symm
 suffices hx:∀ i j:Hand G,tap (sings b (fros a G U u) (K F)) i j=tap (K P) i j from by ext ⟨i,v⟩ ⟨j,w⟩; exact congr_fun (congr_fun (hx i j) v) w
 intro i j; unfold fros P K; rw [tap_sg,he,he]; have hg(m:Hand G): (paceU a G m).2=0 ↔ m.2=0:=by change a.s.act _=0 ↔ _; nth_rw 1 [← a.s.act_zero (R:=Per G.count)]; exact a.s.act_injective.eq_iff
 by_cases k:i.2=0∧ j.2=0; rw [if_pos ⟨(hg _).mpr k.1,(hg _).mpr k.2⟩,if_pos k]; unfold mealU; rw [tap_sg]; rfl
 rw [if_neg (fun v=>k ⟨(hg _).mp v.1,(hg _).mp v.2⟩), if_neg k,win_z,mul_zero,zero_mul]
end YM.CF.Scroll

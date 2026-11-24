import YM.CF.Vault.Venus
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vault
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip Scroll Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
variable {I:Type*}[Fintype I][DecidableEq I][Nonempty I]
def revY(A:Op I)(C D:UNI I): Op I:=C.val*cc A*star D.val
def ment(v:TickZ)(A:Op I)(C D:UNI I):= A+ ((v.val/2:ℝ):ℂ) • (revY A C D-A)
@[simp] lemma rove(A:Op I)(C:UNI I):revY A C C=sings true C A:=by rw [singT,twist_formula]; rfl
lemma funds_n (A:Op I)(C D:UNI I):ment noneL A C D=A:=by simp [ment,noneL]
lemma wakeM (A:Op I)(p:IsSelfAdjoint A)(C:UNI I)(t:TickZ): IsSelfAdjoint (ment t A C C):=by
 have he: IsSelfAdjoint (cc A):=by rw [isSelfAdjoint_iff,←cc_star,p.star_eq]
 unfold ment; simp only [rove,singT]; exact p.add ((IsSelfAdjoint.smul (by rw [isSelfAdjoint_iff]; simp) ((show IsSelfAdjoint (twist C (cc A)) by rw [isSelfAdjoint_iff,←map_star,he.star_eq]).sub p)))
lemma serene (A:Op I)(p:IsSelfAdjoint A): IsSelfAdjoint (royal A):=by unfold royal; exact (IsSelfAdjoint.smul (by rw [isSelfAdjoint_iff]; simp) p).sub (.one _)
lemma skewCmp (C:UNI I)(p:C.valᵀ= -C.val): cc C.val= -star C.val:=by rw [show cc C.val=star (C.valᵀ) from rfl,p,star_neg]
lemma spinBack (C:UNI I)(p:C.valᵀ= -C.val) : congrC C (cc C.val)=C.val:=by rw [congrC,p,skewCmp C p,mul_neg,mul_neg,neg_mul,neg_neg,C.property.2,one_mul]
lemma revol (C D:UNI I)(p:C.valᵀ= -C.val)(q:D.valᵀ= -D.val)(A:Op I):revY (revY A C D) C D=A:=by
 simp only [revY,cc_mul,cc_star,cc_cc, skewCmp C p, skewCmp D q,star_neg,star_star,mul_neg,neg_mul,neg_mul_neg]; rw [←mul_assoc C.val,←mul_assoc, C.property.2, one_mul,mul_assoc,D.property.2,mul_one]; simp
lemma roofs (C D:UNI I)(p:C.valᵀ= -C.val)(q:D.valᵀ= -D.val)(A:Op I): revY (ment oneL A C D) C D=ment oneL A C D:=by
 have he: star ( ((oneL.val/2:ℝ):ℂ))=(1/2:ℂ):=by norm_num [oneL]
 have hv:( ((oneL.val/2:ℝ):ℂ))=(1/2:ℂ):=by norm_num [oneL]
 let V:=revY A C D
 have hh(B E:Op I)(t:ℂ): revY (B+t • E) C D= revY B C D + (star t) • revY E C D:=by simp [revY,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,mul_add,add_mul]
 have hr(E Q:Op I): revY (E-Q) C D=revY E C D - revY Q C D:=by simp [revY,mul_sub,sub_mul]
 unfold ment; rw [hh,hr,revol C D p q,he,hv]; module
private lemma safe_y (A:Op I)(h:IsSelfAdjoint A)(hp: ‖A*A-1‖ ≤1/2):Safe A:=by
 have hS: IsSelfAdjoint (A*A-1):=by rw [isSelfAdjoint_iff,star_sub,star_mul,h.star_eq,star_one]
 refine ⟨h,?_,?_⟩
 · have hh:‖A‖*‖A‖=‖A*A‖:=by rw [← CStarRing.norm_star_mul_self, h.star_eq]
   have hb:= norm_le_norm_sub_add (A*A) 1; rw [norm_one] at hb; nlinarith
 have hb:= op_ge_neg_scalar hS hp; rw [le_sub_iff_add_le] at hb
 rw [sq]; exact le_trans (le_of_eq (by module)) hb
variable {ι:Type*}{L N P:Side}{A B R: Chop ι}{u:Bool}
def dotB (u:Bool)(G:Ratio N P)(x:Sew N P):UNI (Iota G):=⟨squareD G u (post x),unit_square ..⟩
lemma scrap_x (b:Bool)(i:ι×TickZ)(A:Chop ι)(x:Sew N P)(G:Ratio N P): let Z:=dotB b G x; scrap b A i G (post x)= royal (ment i.2 (A i.1 G (post x)) Z Z):=by intro Z; simp only [scrap,twinX,rentD,charge_p,ment,revY,royal,Z]; rfl
lemma paddle_serene (b:Bool)(G:Ratio N P)(i:ι)(A:Chop ι)(x:Sew N P)(p:IsStarProjection (A i G (post x))): paddle b A (i,noneL) G (post x)=A i G (post x):=by unfold paddle; rw [show scrap _ _ _ _ _=_ from scrap_x b (i,noneL) A x G]; rw [funds_n]; exact royal_c p
lemma pad_safe (ho:Odd L.val)(h:BoxD L (ℒ u) (ℒ u) A)(S:Atrest L A)(p: slateQ L u A): Still L fun G x=>∀ i,Safe (scrap u A i G (post x)):=by
 have he:= pad_top ho h; let T:Chop (ι × TickZ):=fun i N P G x=> scrap u A i G x* scrap u A i G x-1; have hx:BoxD L (ℒ u) (ℒ u) T:=(he.chain he).sub BoxD.one
 obtain ⟨d,m,c,v,k,Y⟩:= pay_small hx (k:=0) (fun i _ _ G t w=> (by unfold T; rw [show scrap _ _ _ _ _=_ from reserve_c S u i G t]; rw [←sq, royal_sq (S i.1 G t).1,sub_self])) (show 0<(1:ℝ)/2 by norm_num)
 let V:= fun {N P:Side} (G:Ratio N P) (x:Bale N P)=>∀ i:ι × TickZ, ‖T i G x‖≤ 1/2
 have hv:Tills L @V:= ⟨m,v,k,fun {N P} G he ht x p i=> (Y i G he ht).lib.boundOp c.le ⟨x,p⟩⟩
 apply ((hv.gilded).plus p).forward; intro N P G he x p' i; apply safe_y _ _ (p'.1 _); rw [show scrap _ _ _ _ _ = _ from scrap_x u i A x G]; exact serene _ (wakeM _ (p'.2 i.1).isSelfAdjoint _ _)
lemma pad_end (b:Bool)(G:Ratio N P)(i:ι)(x:Sew N P)(p:Safe (scrap b A (i,oneL) G (post x))): let Y:=dotB b G x; sings true Y (paddle b A (i,oneL) G (post x))=paddle b A (i,oneL) G (post x):=by
 intro V; let L:= scrap b A (i,oneL) G (post x); have he: sings true V L=L:=by
    unfold L; rw [show scrap _ _ _ _ _=_ from scrap_x b (i,oneL) A x G]; simp only [royal,singT,win_l,win_c,win_i,map_sub,map_one,twist_scalar]
    rw [show cSignX true 2=2 by norm_num [cSignX], ← singT,← rove,show revY _ _ _=_ from roofs V V (skew_square G b x) (skew_square G b x) (A i G (post x))]
 exact fires_h true false V L L p p he
lemma pad_cont (b:Bool)(G:Ratio N P)(i:ι)(x:Sew N P)(p:∀ v:TickZ, Safe (scrap b A (i,v) G (post x))) :Continuous (fun v:TickZ=> paddle b A (i,v) G (post x)):=by
 let X(v:TickZ):= scrap b A (i,v) G (post x); have he: Continuous X :=by unfold X scrap twinX; fun_prop
 exact (continuousOn_projector rho_lt rho_pos.le).comp_continuous he (fun i=> (p i).good)
end YM.CF.Vault

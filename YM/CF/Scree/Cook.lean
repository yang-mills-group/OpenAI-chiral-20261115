import YM.CF.Scree.Form
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scree
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Pastry
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]{r:ℕ}{P Q:Op n}(h:IsStarProjection P)(g:IsStarProjection Q)(b r:Bool)(U:UNI n)(v:sings b U P=swapX r Q)
private lemma eval_putV(S:Poly n m)(i:n): S.eval (put i)=S.term i:= by rw [←show poke {i}=put i from Poly.tag_once .., S.eval_oneT]; exact Poly.tag_once ..
lemma leafU (x:n)(u:Bool) : sauce b r U (wire u x)= ∑ j, ((spice U r).val ((u.xor r),j) (u,x)) • wire (u.xor r) j:=by
 rw [sauce,singT, show windX _ (wire u x)=_ from win_up ..]
 cases r
 · simp only [Bool.xor_false]; rw [show spice U false=closeV U from rfl,thread_in]; simp [closeV,jump_apply] -- tune
 rw [spirit]; cases u <;> simp [spice,jump_apply,opBool] -- tune
private lemma tenor (V:Op n)(Q:Op n)(x:n): create (acts Q (acts V (basisKet x)))= ∑ j,V j x • create (acts Q (basisKet j)):=by nth_rw 1 [←basis_expand (acts V (basisKet x))]; rw [map_sum,map_sum]; refine sum_congr rfl fun j _=> ?_ ; rw [map_smul,map_smul,basis_act]
private lemma voce (V Q:Op n)(x:n):remove (acts Q (acts V (basisKet x)))= ∑ j,(cc V) j x • remove (acts Q (basisKet j)):=by unfold remove; rw [tenor,star_sum]; exact sum_congr rfl fun j _=> by rw [star_smul]; rfl
include h g v
lemma apple(x: LeanV n):(nursery Q g).eval (sauce b r U (put x))=Spire.tourP U b r ((nursery P h).term x):=by
 rcases x with ⟨u,i⟩; rw [leafU b r]; simp_rw [map_sum,map_smul, wire, eval_putV]
 cases r
 · change _=sings b (quantU U) _; change sings b U P=Q at v; simp only [Bool.xor_false]
   have he(T:Bool)(j): (spice U false).val (T,j) (T,i)=(thread U T).val j i:=by simp [spice,closeV,jump_apply]
   simp_rw [he, nursery,drawT]; cases u
   · simp only [Bool.false_eq_true,↓reduceIte,hideF,prong_t,thread]; unfold remove; rw [singT,win_s,stove,dove_acts,dove_base, map_star,twist_create, Fock.swivel,show twist U (windX b P)= Q from v] -- tune v
     exact (voce U.val Q i).symm
   simp only [ite_true,thread,seekF,prong_p]; rw [singT,stove,dove_acts,dove_base, twist_create, Fock.swivel, win_l,map_sub,win_i,map_one]; rw [show twist U (windX b P)=Q from v]; exact (tenor _ _ _).symm
 change _=theta U _; simp_rw [nursery,drawT]; change sings b U P=1-Q at v
 have he(w):acts (invFilm U).val w=Complex.I • acts U.val w:= inv_act U w
 cases u
 · simp only [Bool.false_eq_true, Bool.false_xor, ↓reduceIte,ite_true, hideF,seekF,prong_p,prong_t]
   have ht(j): (spice U true).val (true,j) (false,i)=(invFilm U).val j i:=by simp [spice,jump_apply,opBool,thread] -- tune
   simp_rw [ht]; rw [←tenor, he,map_smul,map_smul,show windX b (remove _) = remove (dove b (acts P (basisKet i))) by unfold remove; rw [win_s,stove], theta_downV,dove_acts,dove_base,Fock.swivel,show twist U (windX b P)=1-Q from v]
 simp only [ite_true,Bool.true_xor,Bool.not_true,Bool.false_eq_true, ↓reduceIte, hideF, seekF,prong_p,prong_t]
 have ht(j): (spice U true).val (false,j) (true,i)=cc (invFilm U).val j i:=by simp [spice,jump_apply,opBool,thread]; rfl
 simp_rw [ht]; rw [←voce, he,map_smul,stove,dove_acts,dove_base, theta_upV,Fock.swivel,win_l,map_sub,win_i,map_one,show twist U (windX b P)=1-Q from v]; unfold remove; rw [map_smul,star_smul]; simp
omit h g v
-- exterior algebra support all parities
abbrev spanP (n:Type*) [LinearOrder n][Fintype n] (F: FC n):Prop:=F=∑ i:Finset n,crumb F i • poke i
private lemma span_sum {F:FC n}(f:Finset n→ℂ)(h:F=∑ i:Finset n,f i • poke i): spanP n F:=by rw [h]; refine sum_congr rfl fun _ _=>?_ ; simp [chip,crumb_sum,crumb_scale,mul_ite] -- tune rw span
lemma snack {ι:Type*}{I:Finset ι}{f:ι→ FC n}(p:∀ i∈I,spanP n (f i)):spanP n (∑ i∈I,f i):=by
 classical
 unfold spanP; simp_rw [crumb_sum,sum_smul]; rw [sum_comm]; exact sum_congr rfl p
lemma spanPt (S:Finset n):spanP n (poke S):=by unfold spanP; simp [chip,ite_smul]
lemma spanS {F:FC n}(p:spanP n F)(x:ℂ):spanP n (x • F):=by unfold spanP; simp_rw [crumb_scale,mul_smul, ←smul_sum]; exact congrArg _ p
lemma spanT {F G:FC n}(p:spanP n F)(q:spanP n G):spanP n (F*G):=by
 rw [p,q,sum_mul]; apply snack; intro i _; rw [mul_sum]; apply snack; intro j _; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,poke,poke,Poly.tag_mul]; apply spanS; apply spanS; split_ifs ; exact spanS (spanPt ..) _; unfold spanP; simp [crumb]
lemma sauceS (s:Finset (LeanV n)): spanP (LeanV n) (sauce b r U (poke s)):=by
 induction s using Finset.induction_on_min with
 | empty=> rw [poke,Poly.tag_void,sauce,singT,win_i,map_one]; exact (Poly.tag_void (cane (LeanV n))) ▸ spanPt ∅ -- tune
 | insert i s k ih=> rw [poke,Poly.tag_min _ _ _ k,sauce,singm]; cases i with| mk u i=> exact spanT (show spanP _ (sauce b r U (wire u i)) by rw [leafU b r]; apply snack; intro j _; apply spanS; exact (show poke {_}= wire (u.xor r) j from Poly.tag_once (cane _) _) ▸ spanPt _) ih
lemma fireT (S: Poly n m){F G:FC n}(p:spanP n F)(q:spanP n G):S.eval (F*G)=S.eval F*S.eval G:=by rw [p,q,sum_mul,map_sum,map_sum,map_sum,sum_mul]; apply sum_congr rfl; intro i _; rw [mul_sum,mul_sum,map_sum]; apply sum_congr rfl; intro j _; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,map_smul,map_smul,map_smul,map_smul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,S.eval_oneT,S.eval_oneT,S.eval_prod]
include h g v
lemma appleT (x:ribbon n): Spire.tourP U b r ((nursery P h).cook x)=(nursery Q g).cook (paintR b r U x):=by
 let H:= nursery P h; let G:=nursery Q g
 change Spire.tourP _ _ _ (H.eval x.val)=G.eval (sauce b r U x.val); let L:=Wheat (univ:Finset (LeanV n)); let W:= sauce b r U
 have hx:x.val=∑ i∈L, crumb x.val i • poke i:=(fineShape x).pin -- apply rw
 rw [hx,map_sum,nutmeg,sauce,singT,win_sum,map_sum,map_sum]; refine sum_congr rfl fun i _=> ?_
 rw [map_smul,cumin,win_c,twist_scalar,map_smul,H.eval_oneT]; congr 1
 change Spire.tourP U b r (H.tag i)=G.eval (W (poke i))
 clear ‹i∈L› -- tune variable
 induction i using Finset.induction_on_min with
 | empty=> rw [poke,Poly.tag_void,Poly.tag_void,show W 1=1 from ?_,G.eval_one]; cases r <;> simp [Spire.tourP,singT,theta_one,win_i]
           unfold W sauce; rw [singT,win_i,map_one]
 | insert j S k ih=> rw [poke,Poly.tag_min _ _ _ k,Poly.tag_min _ _ _ k,nomZ,show W (_*_)=_ from singm ..]; change _=G.eval (W (put (n:=LeanV n) j)*W (poke S)); rw [fireT G (show spanP (LeanV n) (W (put j)) from (show poke {j}=put j from Poly.tag_once (cane _) _) ▸ sauceS b r U {j}) (sauceS b r U S),ih]; congr 1; exact (apple h g b r U v j).symm
end YM.CF.Scree

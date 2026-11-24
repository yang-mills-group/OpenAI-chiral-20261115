import YM.SU5.Relativistic.Caplets
import YM.SU5.FiniteGaugeData.Tapestry.Neutral
/-!
# Actual singlet baryons in finite and calibrated poses
ν exponents may be ugly. Need odd letters.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Lifted Afterglow Tapestry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra

section keels
variable {I A:Type*}[LinearOrder I][Fintype I][Nonempty I]
-- use Abstract det test with FC-valued row
private lemma wedge_s {i:ℕ}(F:Fin i→FC I)(p:∀ a b, F a*F b+F b*F a=0)(u:∀ a,F a*F a=0) {a b: Fin i} (g:a ≠ b)(t:F a=F b) : (List.ofFn F).prod=0:=by
 induction i with
 | zero=> exact Fin.elim0 a
 | succ i ih=>
    rw [List.ofFn_succ,List.prod_cons]
    let X(k:Fin i):= F k.succ; let U:=List.ofFn (@id (Fin i))
    change F 0*(List.ofFn X).prod=0
    have hs (k:Fin i)(h:F 0=F k.succ): F 0*(List.ofFn X).prod=0:=by
       have hU:k∈ U:=by unfold U; simp
       obtain ⟨L,H,e⟩:=List.append_of_mem hU
       rw [show List.ofFn X=U.map X from (by unfold U; rw [List.map_ofFn]; rfl),e,List.map_append,List.map_cons,List.prod_append,List.prod_cons,←mul_assoc, ←mul_assoc (F 0* _) (X k)] -- first assoc rewrites?
       have hm(l:List (Fin i)): F 0*(l.map X).prod*X k=0:=by
          induction l with
          | nil=> rw [List.map_nil,List.prod_nil,mul_one,show X k=F 0 from h.symm]; exact u 0
          | cons a l ih=> rw [List.map_cons,List.prod_cons,←mul_assoc,show F 0*X a= -(X a*F 0) from eq_neg_of_add_eq_zero_left (p ..),neg_mul,mul_assoc,neg_mul,mul_assoc,ih,mul_zero,neg_zero]
       rw [hm,zero_mul]
    rcases eq_or_ne a 0 with e|e; · subst a; obtain ⟨b,rfl⟩:= Fin.eq_succ_of_ne_zero g.symm; exact hs b t
    obtain ⟨a,rfl⟩:= Fin.eq_succ_of_ne_zero e
    rcases eq_or_ne b 0 with e|e; · subst b; exact hs a t.symm
    obtain ⟨b,rfl⟩:= Fin.eq_succ_of_ne_zero e
    rw [ih X (fun i j=> p ..) (fun i=>u _) (fun e=>g (congrArg _ e)) t,mul_zero]

lemma colored {ν:ℕ}(F:(Fin ν→ℂ) →ₗ[ℂ] FC I)(p:∀ a b,F a*F b+F b*F a=0)(v:∀ a,F a*F a=0)(M:Op (Fin ν))(u:M.det=1):
    (List.ofFn (fun i:Fin ν => F (fun j=> M j i))).prod=(List.ofFn (fun i=>F (Pi.basisFun ℂ (Fin ν) i))).prod:=by
 let W:= (MultilinearMap.mkPiAlgebraFin ℂ ν (FC I)).compLinearMap (fun i=> F)
 let B: AlternatingMap ℂ (Fin ν→ℂ) (FC I) (Fin ν) := {W with map_eq_zero_of_eq':=fun V i j v' x=> wedge_s (fun i=>F (V i)) (fun i j=> p ..) (fun i=>v _) x (congrArg F v')}
 let X:Fin ν → (Fin ν→ℂ):=fun i j=> M j i
 let e:= Pi.basisFun ℂ (Fin ν)
 change B X=B e
 ext i j; let Y:FC I →ₗ[ℂ] ℂ:=⟨⟨fun A:FC I=> A i j,fun _ _=>rfl⟩, fun _ _=>rfl⟩; let f:= Y.compAlternatingMap B
 have he:f X=f e:=by
    nth_rw 1 [AlternatingMap.eq_smul_basis_det e f]; rw [AlternatingMap.smul_apply,Pi.basisFun_det_apply]; change f e*(Mᵀ).det= f e; rw [Matrix.det_transpose,u,mul_one]
 exact he

-- interaction algebra five alternating F's. color coefficients W given; star matches removals
private def expandC (b:Bool) (x:Ring5→ Ket I) : (Ring5→ℂ) →ₗ[ℂ] FC I :=
 ∑ i:Ring5,(LinearMap.proj (R:=ℂ) (φ:=fun _ :Ring5=>ℂ) i).smulRight (creed b (x i)) -- tune syntax
lemma dyn (b:Bool)(x:Ring5→Ket I)(f:Ring5→ℂ): expandC b x f=∑ i,f i • creed b (x i) := by simp [expandC] -- tune
lemma dynB (b:Bool)(x:Ring5→Ket I)(f:Ring5→ℂ): Marque b (expandC b x f):=by
 rw [dyn]; cases b; · exact ⟨(∑ i:Ring5,f i • x i),by change _=create _; rw [map_sum]; exact Finset.sum_congr rfl (fun i _=> (map_smul create (f i) (x i)).symm)⟩
 refine ⟨∑ i:Ring5,star (f i) • x i,?_⟩; change _=star (create _); simp_rw [map_sum,map_smul,star_sum,star_smul,star_star]; rfl
lemma enseal (b:Bool)(x y :Ring5→ Ket I)(M:Op Ring5) (h:M.det=1)
    (s:∀ i:Ring5,creed b (y i)= ∑ j,M j i • creed b (x j)) :
    (List.ofFn (fun i=> creed b (x i))).prod = (List.ofFn (fun i=>creed b (y i))).prod:=by
 let V:= expandC b x; have hx(i:Ring5):V (Pi.basisFun ℂ Ring5 i)=creed b (x i):=by unfold V; rw [dyn]; simp -- tune
 have hu(i:Ring5):V (fun j=> M j i)=creed b (y i):=by unfold V; rw [dyn,s i]
 have p(i j): V i*V j+ V j*V i=0:= add_eq_zero_iff_eq_neg.mpr (same_letter (dynB b x i) (dynB b x j))
 have he := colored V p (fun a=> ?_) M h
 simp_rw [hx,hu] at he; exact he.symm
 ext i j; exact add_self_eq_zero.mp (Matrix.ext_iff.mpr (p a a) i j)
variable {S:Finset I}
-- prime product sign
lemma honour {X Y:Ring5→Ket I}(p:∀ i,trim (hand true (cutM S)) (X i)) :
    prime (fun i=>handy false S (X i) (Y i)) = 1+(List.ofFn (fun i=>remove (X i))).prod*(List.ofFn (fun i=> create (cardH false (cutM S) (Y i)))).prod:=by
 let U:= fun i=>remove (X i); let V:= fun i=> create (cardH false (cutM S) (Y i)); let Ω:= fun i=> handy false S (X i) (Y i)
 have hu(i):1-Ω i= -(U i*V i):=by change 1-(1+_)=_; abel
 have h(i j):V i* U j=-(U j*V i):=eq_neg_of_add_eq_zero_left (asGrade (b:=false) S (p j) (Y i))
 have hs(F:List Ring5): (F.map (fun i=>1-Ω i)).prod= (((-1:ℂ)^((F.length*(F.length+1))/2))) • ((F.map U).prod *(F.map V).prod):=by
    induction F with
    | nil=> simp
    | cons i l ih=>
       let k:=l.length; let P:=(l.map U).prod; let Q:=(l.map V).prod
       have hx(l:List Ring5): V i*(l.map U).prod=((-1:ℂ)^l.length) • ((l.map U).prod*V i):=by
          induction l with
          | nil=> simp
          | cons a l ih=> rw [List.map_cons,List.prod_cons,List.length_cons,pow_succ',←mul_assoc,h,neg_mul,mul_assoc,ih,Algebra.mul_smul_comm,←mul_assoc,mul_smul,neg_one_smul]
       rw [List.map_cons,List.map_cons,List.map_cons,List.prod_cons,List.prod_cons,List.prod_cons,List.length_cons,ih,hu]
       have ho(k:ℕ):2 ∣ k*(k+1):=by induction k with|zero=> simp| succ k ih=> rw [show (k+1)*(k+1+1)=k*(k+1)+(k+1)*2 by ring]; exact dvd_add ih (dvd_mul_left ..)
       rw [show (k+1)*(k+1+1)/2=k*(k+1)/2+k+1 from ?_]; swap
       · have hg:(k+1)*(k+1+1)=k*(k+1)+(k+1)*2:=by ring
         have hg0:=ho k
         omega
       rw [neg_mul, Algebra.mul_smul_comm, pow_succ,pow_add]
       change -((-1:ℂ)^(k*(k+1)/2) • (U i*V i*(P*Q)))= _ • ((U i*P)*(V i*Q)); rw [mul_assoc (U i) (V i),←mul_assoc (V i) P,hx l]; change _= ((-1:ℂ)^(k*(k+1)/2)* (-1)^k * -1) • ((U i*P)*(V i*Q)); rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ←mul_assoc, mul_smul, mul_smul]; simp only [smul_neg,neg_one_smul,mul_assoc]; rfl
 let F:= List.ofFn (@id Ring5); unfold prime; change 1-(List.ofFn (fun i=>1-Ω i)).prod= _; have ho:=hs F; unfold F at ho; simp only [List.length_ofFn,List.map_ofFn,Ring5,Function.comp_id] at ho; -- `norm_num`
 rw [ho]; norm_num; rfl
end keels
variable (n:Side)(g:Seat n→SU.E)(a:Cover)(i:SpinIdx)
abbrev barred (d:Fin 3)(k:Ring5):SU.Slot := (d,Sum.inr k)
lemma tradeG (d:Fin 3)(k:Ring5):
 acts (tradew n g).val (basisC n a i (barred d k))=∑ l:Ring5, cc (fund (g (wrap (More n) (nodeC a)))) l k • basisC n a i (barred d l):=by
 rw [turn_basisC]; simp [matter_matrix,triple,each,Join.both,SU.Slot,SU.Sheet,barred, Fintype.sum_prod_type,Fintype.sum_sum_type,Matrix.one_apply,ite_smul] -- tune 1 and zero

-- general Family coefficient from parallel transport. apply engage_det through any external gauge
lemma fixF (d:Fin 3):
 (List.ofFn (fun k:Ring5=>remove (acts (tradew n g).val (basisC n a i (barred d k))))).prod=(List.ofFn (fun k:Ring5=>remove (basisC n a i (barred d k)))).prod :=by
 apply Eq.symm (enseal true (fun k=>basisC n a i (barred d k)) (fun k=>acts (tradew n g).val (basisC n a i (barred d k))) (fund (g (wrap (More n) (nodeC a)))) (fund_det _) _)
 intro k; change star (create _) = _; rw [tradeG,map_sum,star_sum]; apply sum_congr rfl; intro l _
 rw [map_smul,star_smul,cc_apply,star_star]; rfl
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.enseal
#print axioms YM.CF.Pannier.Chancel.ScreeV.fixF

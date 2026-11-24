import YM.CF.BPress.Lute.Sparkle
import YM.CF.Fock.Line
import GaugeFieldConstruction.Flavor
import GaugeFieldConstruction.Oriental
/- Flavor rotations as commutators in extended unitary multiplicities. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.GaugeFieldConstruction.Flavor
open CF BPress.Lute Fock Function Finset Matrix
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
abbrev CrewFe:= Fin 3
abbrev BigFe:= Bool → UNI CrewFe
section mat
local notation "κ"=> CrewFe
private abbrev W(c:κ→ℂ):Op κ:=Matrix.diagonal c
-- A B = H B A choose with cyclic permutation e(i)=i+1; w(i+1)=h(i+1)*w(i)
private def Ξfe : Op (Fin 3):= !![0,0,1;1,0,0;0,1,0]
private lemma κside: Ξfe ∈ unitary _:=(Unitary.mem_iff ..).mpr ⟨by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Ξfe,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ],by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Ξfe,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ]⟩ -- tune iff
private lemma kick(f : κ→ℂ)(p:W f ∈ unitary _)(h: f 0*(f 1*f 2)=1): ∃ D: UNI κ, D.val*Ξfe= W f*(Ξfe*D.val):=by
 let U:κ→ℂ:= ![1,f 1,f 2*f 1]
 have hv(s:κ):star (f s) * f s=1:=by
   have ht:= Matrix.ext_iff.mpr p.1 s s; rwa [Matrix.mul_diagonal, show star (W f) s s= _ from ?_,Matrix.one_apply_eq] at ht
   simp
 have hw(s:κ):star (U s)* U s=1:=by
    dsimp only [CrewFe] at s; fin_cases s
    · change star (1:ℂ)*1=1; simp
    · exact hv 1
    change star (f 2*f 1)*(f 2*f 1)=1
    rw [star_mul]; calc
       _ = (star (f 2)*f 2)*(star (f 1)*f 1) := by ring
       _ = _ := by rw [hv,hv,mul_one]
 have hB:star (W U)*W U=1:=by
    ext i j; rw [Matrix.mul_diagonal,Matrix.star_apply]; by_cases t:i=j
    · subst j; rw [show W U i i= _ from Matrix.diagonal_apply_eq ..,hw]; simp
    have he: j≠i:=Ne.symm t; unfold W; simp [he,t]
 have hU:W U∈ unitary _:=⟨hB,mul_eq_one_comm.mp hB⟩
 refine ⟨⟨_,hU⟩,?_⟩; change W U*Ξfe= _; apply Matrix.ext; intro i j; rw [Matrix.diagonal_mul,Matrix.diagonal_mul, Matrix.mul_diagonal]
 change U i*Ξfe i j= f i* (Ξfe i j * U j)
 generalize_proofs
 dsimp only [CrewFe] at i j; fin_cases i<;>fin_cases j<;>simp [Ξfe,U,mul_comm (f 2) (f 1),h]
lemma commiss (x: UNI κ)(p:x.val.det=1): ∃ a b: UNI κ, a*b=x*(b*a):=by
 obtain ⟨U,f,h⟩:= spectralC_diag_exists x.val x.property
 have hx:W f∈ unitary _:= by
    have hp: W f=twist (star U) x.val:= by rw [h]; exact (twist_inv ..).symm
    rw [hp]; exact (unitary _).mul_mem ((unitary _).mul_mem (star U).property x.property) (star (star U)).property
 rw [h,twist_T] at p; have hprod:f 0*(f 1*f 2)=1:=by simpa [CrewFe,Fin.prod_univ_succ,mul_assoc] using p
 obtain ⟨d,hd⟩:= kick f hx hprod
 refine ⟨(U*d)*U⁻¹,(U*⟨Ξfe,κside⟩)*U⁻¹,Subtype.ext ?_⟩
 change twist U d.val * twist U Ξfe = x.val*(twist U Ξfe*twist U d.val)
 rw [←map_mul,hd,h,map_mul,map_mul]; rfl
end mat

-- signed rotations real UNI
abbrev chipFe (x:proper3):Op CrewFe:= (Signed.matrix x.val).submatrix Fin.castSucc Fin.castSucc |>.map Complex.ofReal
lemma chipFe_v (x:proper3)(j i:CrewFe): chipFe x j i=if leg x i=j then pay (mark x i) (1:ℂ) else 0:=by
 rw [show chipFe x j i=Complex.ofReal (Signed.matrix _ _ _) from rfl,Signed.matrix_at, ← cast_leg]; unfold mark
 split_ifs with e g H<;> cases h:x.val.flip i.castSucc <;> simp_all -- tune
lemma chipDm (x:proper3):(chipFe x).det=1:=by
 let F:=Signed.matrix x.val
 have he:F.det=1:=by
    have hp:=Stage.parity x.val; rw [x.property.2.2,pay_false] at hp; exact hp
 -- determinant minor formula last row. tune

 let i:= Fin.last 3; have hv:x.val.perm i=i:= x.property.1; have hX:x.val.flip i=false:= x.property.2.1
 have hg:=det_succ_column F i; rw [sum_eq_single i] at hg
 · unfold F at hg; rw [Signed.matrix_at,hv,hX] at hg; rw [show F.det=1 from he] at hg -- F naming
   norm_num [i] at hg; change det (Complex.ofRealHom.mapMatrix (F.submatrix Fin.castSucc Fin.castSucc))=1; rw [←RingHom.map_det]; simp [hg]; rfl -- direction
 · intro y u g; unfold F; rw [Signed.matrix_at,hv]; simp [Ne.symm g]
 simp
lemma chip_unit (x:proper3): chipFe x ∈ unitary _:=by
 let f:=leg x; let A:=chipFe x
 have h (i k:CrewFe): f i=f k ↔ i=k:= ⟨fun e=> Fin.castSucc_inj.mp (x.val.perm.injective (Eq.trans ((cast_leg ..).symm) ((congrArg Fin.castSucc e).trans (cast_leg ..)))), congrArg f⟩
 have hX: star A * A= 1:=by
    ext i j; rw [Matrix.mul_apply,sum_eq_single_of_mem (f i) (mem_univ _)]
    · unfold A; rw [star_apply,chipFe_v,chipFe_v]; change star (if f i=f i then _ else _) * (if f j=f i then _ else _)= _; by_cases t:j=i
      · subst j; cases mark x i <;> simp
      simp only [h,if_true,if_neg t,mul_zero]; simp [Ne.symm t] -- tune
    intro y p hy; unfold A; rw[star_apply,chipFe_v]; rw [if_neg (Ne.symm hy),star_zero,zero_mul]
 exact ⟨hX,mul_eq_one_comm.mp hX⟩

def chipUFe (x: Flavor):BigFe:= fun i=> ⟨chipFe (x i),chip_unit _⟩
lemma wrought (x:Flavor):∃ a b:BigFe,a*b=chipUFe x*(b*a):=by
 choose g h p using fun i=> commiss (chipUFe x i) (chipDm _); exact ⟨g,h,funext p⟩
lemma coastOne {I:Type*}[LinearOrder I][Fintype I](P:Op I)(p:IsStarProjection P)(q:Wave I)(v:Sea P q)(A: BigFe→* UNI I)(h:∀ i,twist (A i) P=P)(x:Flavor): acts (quant (A (chipUFe x)).val) q=q:=by
 let W (r:BigFe):= acts (quantU (A r)).val; let s i:= inner ℂ q (W i q)
 have ht(i:BigFe) : W i q=s i • q:=by
    rw[← show acts (lineOp P) (W i q)=s i • q from v.scalar p _]; symm; rw [← h i,line_twist,twist_formula,act_mul,act_mul]; change acts _ (acts (lineOp P) (acts (star (quantU (A i)).val) (acts (quantU (A i)).val q)))= _; rw [act_unit, v.1]
 have g(i:BigFe) : s i≠0:=by
    intro c; have hx:‖W i q‖=1:= (act_unit_norm ..).trans v.2; rw [ht,c,zero_smul,norm_zero] at hx; norm_num at hx
 obtain ⟨a,b,t⟩:=wrought x; let y:=chipUFe x; have hk(i j:BigFe)(q':Wave I): W (i*j) q'=W i (W j q'):=by unfold W; rw [map_mul]; change acts (quant ((A i).val*(A j).val)) _= _; rw [quant_mul,act_mul]; rfl
 apply smul_right_injective (Wave I) (mul_ne_zero (g a) (g b))
 change (s a*s b) • W y q=(s a*s b) • q; rw [← smul_smul, ←smul_smul]; calc
    _=W (y*(b*a)) q:=by rw [hk,hk,ht a,map_smul,ht b,map_smul,map_smul] -- tune nth use map
    _= W (a*b) q:=by rw [t]
    _= _:= by rw [hk,ht b,map_smul,ht a]; exact smul_comm ..
#print axioms coastOne
end YM.GaugeFieldConstruction.Flavor

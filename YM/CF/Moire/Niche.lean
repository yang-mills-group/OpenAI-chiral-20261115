import YM.CF.Moire.Polo
import YM.CF.Laic.Hope
/-! Extensive *nonperturbative* analytically tilted Weyl sea. Projection complexification with gauge for sector extensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Moire
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire Branch Nacre
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m:ℕ}{n:Side}
open Laic
variable {b e a:ℝ}
lemma regal(P:Toy m n)(s:Signed)(X:Bkg (More n)): Wheel P s (profile X)= ape n (incX s) (cavil P (Yg (incX s⁻¹) X)):=by
 unfold Wheel mulC ape; rw [← map_sum]; congr 1; ext ⟨i,u⟩ ⟨j,v⟩; simp only [Rota]; simp_rw [Fintype.sum_prod_type (α₁:=HopK n)]; simp only [Matrix.sum_apply, armC,spark_m,Matrix.of_apply]; unfold cavil; rw [Matrix.of_apply,Matrix.sum_apply]; simp only [ite_and,sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_univ,ite_true] -- tune iter unfold too much
lemma rubyH(x:Equiv.Perm (Site n))(f:Site n→ℝ): ∑ i:Single n,f (x i.1.1)=flair*(∑ j:Site n,f j):=by
 unfold Single; rw [Fintype.sum_prod_type,Fintype.sum_prod_type]; rw [sum_comm]; simp only [sum_const,nsmul_eq_mul,card_univ]; rw [← Finset.mul_sum, Equiv.sum_comp]; unfold flair; ring
lemma payV(m:ℕ)(h:0≤b)(H:0<e)(p:e*ornament m≤ a):∃ C:ℝ,∀ (n:Side)(P:Toy m n),CardK n m P b a→∀ s:Signed,Solo e C (Wheel P s) e:=by
 let T:=(∑ t:Cin,‖spurY t‖); have ht(i):‖spurY i‖ ≤ T:=single_le_sum (f:=fun j:Cin=> ‖spurY j‖) (fun i _=>norm_nonneg _) (mem_univ i)
 let U:=(∑ t:Cin,‖sol t‖); have hu(i):‖sol i‖ ≤ U:=single_le_sum (f:=fun j:Cin=> ‖sol j‖) (fun i _=>norm_nonneg _) (mem_univ i)
 have hT:0≤T:=sum_nonneg fun _ _=> norm_nonneg _; have hU:0≤U:=sum_nonneg fun _ _=>norm_nonneg _
 let N:=(↑(Fintype.card Slot):ℝ)*pen e m T U; let C:=flair*N*(flair*b); have hp:0≤N:=by unfold N pen ruby; positivity; -- tune
 have hh:0≤flair:= by unfold flair; positivity
 refine ⟨C,fun n P u s=>?_⟩
 refine Crown.absorb (J:=Rota m n) _ _ _ _ (by unfold C; positivity) _ (fun i=> grit_pay s P u.2.1 i.1 i.2.1 i.2.2 T U H hT hU ht hu) (fun _=>rfl) (fun i=>?_) fun i=>?_
 · let V:=Tofu (incX s) n; let x:= V i.1.1; change ∑ j, logos P s e T U i j≤ C; apply (sum_le_sum (fun j (_:j ∈ (univ:Finset _))=> Logos P s i j H p hT hU)).trans; change ∑ j:Single n, N*brass P x (V j.1.1) a ≤ _; rw [← mul_sum,rubyH V (fun i=>brass P x i a)]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (coin P u.2.2 x) hh) hp); unfold C; exact le_of_eq (by ring)
 let V:=Tofu (incX s) n; let x:= V i.1.1; change ∑ j, logos P s e T U j i≤ C; apply (sum_le_sum (fun j (_:j ∈ (univ:Finset _))=> Logos P s j i H p hT hU)).trans; change ∑ j:Single n, N*brass P (V j.1.1) x a ≤ _; rw [← mul_sum,rubyH V (fun i=>brass P i x a),dress_h a x P u.1]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (coin P u.2.2 x) hh) hp); unfold C; exact le_of_eq (by ring)

def ocean(s:Signed)(P:Toy m n): Chin n→Op (Single n):= if detX s then fun i=> -pale (Wheel P s) i else Wheel P s
def warm(P:Toy m n)(X:Chin n):= (↑(Fintype.card Signed):ℝ)⁻¹ • ∑ s:Signed, ocean s P X
lemma warm_H(P:Toy m n)(X:Bkg (More n)):warm P (profile X)=colorX P X:=by
 unfold warm colorX sumU; congr 1; apply sum_congr rfl; intro i _; rw [foil,zone_c]; unfold ocean Thera.jazz; rw [show (incX i).s=i from rfl]; cases h:detX i<;> simp only [ite_false,Bool.false_eq_true,ite_true]; exact regal ..; rw [pale,ice_pr,regal]
lemma waged (m:ℕ)(h:0≤b)(H:0<a):∃ e C:ℝ,0<e∧ 0<C∧ ∀ (n:Side)(P:Toy m n),CardK n m P b a→Solo e C (warm P) e:=by
 let e:=a/ornament m; have he:0<e:= div_pos H (ornP m)
 obtain ⟨B,hx⟩:=payV m h he (show e*ornament m≤a from le_of_eq (div_mul_cancel₀ a (ornP ..|>.ne')))
 let P:= ((↑(Fintype.card Signed):ℝ)⁻¹)
 let V:=‖(P:ℂ)‖*(∑ _i:Signed,B)
 refine ⟨e,max V 1,he,lt_max_of_lt_right one_pos,fun n F u=>?_⟩
 have hz(s:Signed):Solo e B (ocean s F) e:=by unfold ocean; split;  exact (solo_opp (hx n F u s)).minus; exact hx n F u s -- missing
 have hp:= (Crown.sumK (univ:Finset Signed) _ _ (fun i _=>hz i)).scale (↑P:ℂ); unfold warm; simp_rw [← Complex.coe_smul] 

 exact hp.books (le_max_left ..)

def bloom(P:Aim n)(X:Chin n): Op (Single n):= warm P.x X+warm P.y X
lemma bloom_P(P:Aim n)(X:Bkg (More n)): bloom P (profile X)= P.den X:= by rw [bloom,warm_H,warm_H]; rfl
lemma terrace {ι:Type*}{u v a b:ℝ}(P:ι→(n:Side)→Aim n)(hu:0≤u)(hv:0≤v)(h:0<a)(p:0<b)(k:∀ i n, (P i n).toll a b u v) : Lively (fun i n=> bloom (P i n)):=by
 obtain ⟨c,C,hc,hC,A⟩:=waged 1 hu h; obtain ⟨r,R,hr,hR,H⟩:= waged 2 hv p; exact Lively.add (f:=fun i n=>warm (P i n).x) (g:=fun i n=> warm (P i n).y) (certify hc hc (v:=0) (fun i n _=> A n ((P i n).x) (k i n).1)) (certify hr hr (v:=0) (fun i n _=> H n ((P i n).y) (k i n).2))
lemma bloom_zero(P:Aim n):bloom P 1=0:=by
 rw [←profile_trivial,bloom_P]
 have hp(m:ℕ)(w:0<m)(Y:Toy m n):colorX Y 1=0:=by
   unfold colorX sumU; rw [sum_eq_zero, smul_zero]; intro i _; unfold foil; rw [show Yg (incX i⁻¹) (1:Bkg (More n))=1 by rw [Ywin]; ext; simp [Lattice.pull,Step.read], show cavil Y 1=0 from ?_,map_zero]; -- tune
   ext ⟨u,j⟩ ⟨v,k⟩; unfold cavil; simp only [Matrix.of_apply]; rw [sum_eq_zero]; rfl; intro l _; rw [mold]; have ht: halo Y u v l (fun i=>silt (terse u) (l i) (1:Config SU.group (More n)))=0:=by simp_rw [silt_0]; ext i j; exact (Y _ _ _).map_coord_zero (⟨0,w⟩: Fin m) (m:=fun i=>0) rfl
   rw [ht,Matrix.zero_mul]
 unfold Aim.den; rw [Pi.add_apply,hp 1 (by omega),hp 2 (by omega),add_zero]
end YM.CF.Moire

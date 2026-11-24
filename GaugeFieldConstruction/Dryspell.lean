import GaugeFieldConstruction.DrySlot
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tulip
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra

variable {N:Side}{e:ℝ}
abbrev DryPulse (a r:ℝ)(f:Chin N→Op (Single N))(e:ℝ):= DrySlot (badge _) (bail N e) (bail N e) a r (fun x=>f x.val) (fun x=> x.val=Tulip.profile (1:Bkg (More N)))
lemma Dry_down (a r:ℝ){f:Chin N→Op (Single N)}(h:DryPulse a r f e) (d:ℝ)(hp:0<d)(hl:d≤e): DryPulse a r f d :=by
  let ρ(x : Openc (More N) d) : Openc (More N) e:= ⟨x.val, filt' x.val d e x.property hl⟩
  have T:Towards (forum N e) (badge _) (forum N d) (badge _) ρ 1:=by
    refine ⟨Continuous.subtype_mk continuous_subtype_val _,rfl,rfl,fun _ _=>rfl,fun S x y=>?_,fun f h V hs γ p=>?_⟩
    · rw [one_mul]; change fare S x.val y.val/|e|≤fare S x.val y.val/|d|; gcongr; exact fare_t ..; all_goals simp [abs_of_pos hp,abs_of_pos (hp.trans_le hl), hl]
    exact h V hs (ρ ∘ γ) p
  obtain ⟨F,C,p,q,l,k⟩:=h; exact ⟨_,_,fun i=>T.suite (s':=bail N d) (t':=bail N d) rfl rfl (p i) le_rfl,q,fun x=> show f (ρ x).val=_ from l (ρ x),fun i x w=> k i (ρ x) w⟩

lemma Dry_op {A:Chin N→Op (Single N)}{a r}(H:DryPulse a r A e): DryPulse a r (pale A) e:=by
  let X:=Openc (More N) e; let f(x:X):↑X:=⟨ice x.val,ice_o x.val e x.property⟩; let b:=forum N e
  refine DrySlot.impose H f ?_ ?_ ?_ ?_ ?_
  · exact (burnOut.comp continuous_subtype_val).subtype_mk _
  · intro g d; exact Subtype.ext (icy_g ..)
  · intro S x y; change fare S (ice x.val) (ice y.val)/_=_; rw [ice_f]; rfl
  · intro g h; exact realigns h f fun V e γ p=> snowy e (fun z=>(γ z).val) p
  intro x y; change ice x.val= _; rw[y,ice_pr]
end YM.CF.Tulip

namespace YM.CF.Moire
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire Branch Nacre
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m:ℕ}{n:Side}
open Laic
variable {b e a:ℝ}

lemma dry_mulC (s:Signed)(P:Toy m n)(p:0 < m)(w:Rota m n): mulC s P w.1 w.2.1 w.2.2 (profile (1:Bkg (More n)))=0:=by
 let i:=w.1; let j:=w.2.1; let k:=w.2.2
 have hx:mold P i j k (1:Bkg (More n))=0:=by
   rw [mold]; have ht: halo P i j k (fun l=>silt (terse i) (k l) (1:Config SU.group (More n)))=0:=by simp_rw [silt_0]; ext u v; exact (P _ _ _).map_coord_zero (⟨0,p⟩: Fin m) (m:=fun i=>0) rfl
   rw [ht,Matrix.zero_mul]
 have hv: armC (incX s⁻¹) P i j k (profile (1:Bkg (More n)))=0:=by
   ext u v; rw [armC,Matrix.of_apply,spark_m,show Yg (incX s⁻¹) (1:Bkg (More n))=1 by rw [Ywin]; ext; simp [Lattice.pull,Step.read],hx]; simp
 unfold mulC ape; change (twist _ (armC (incX s⁻¹) P i j k _))=0; rw [hv,map_zero]
lemma dry_pay(m:ℕ)(v:0 < m)(h:0≤b)(H:0<e)(p:e*ornament m≤ a):∃ C:ℝ,∀ (n:Side)(P:Toy m n),CardK n m P b a→∀ s:Signed,DryPulse e C (Wheel P s) e:=by
 let T:=(∑ t:Cin,‖spurY t‖); have ht(i):‖spurY i‖ ≤ T:=single_le_sum (f:=fun j:Cin=> ‖spurY j‖) (fun i _=>norm_nonneg _) (mem_univ i)
 let U:=(∑ t:Cin,‖sol t‖); have hu(i):‖sol i‖ ≤ U:=single_le_sum (f:=fun j:Cin=> ‖sol j‖) (fun i _=>norm_nonneg _) (mem_univ i)
 have hT:0≤T:=sum_nonneg fun _ _=> norm_nonneg _; have hU:0≤U:=sum_nonneg fun _ _=>norm_nonneg _
 let N:=(↑(Fintype.card Slot):ℝ)*pen e m T U; let C:=flair*N*(flair*b); have hp:0≤N:=by unfold N pen ruby; positivity; -- tune
 have hh:0≤flair:= by unfold flair; positivity
 refine ⟨C,fun n P u s=>?_⟩
 refine DrySlot_absorb (J:=Rota m n) _ _ _ _ (by unfold C; positivity) _ (fun i=> grit_pay s P u.2.1 i.1 i.2.1 i.2.2 T U H hT hU ht hu) (fun _=>rfl) (fun i=>?_) (fun i=>?_) _ ?_
 · let V:=Tofu (incX s) n; let x:= V i.1.1; change ∑ j, logos P s e T U i j≤ C; apply (sum_le_sum (fun j (_:j ∈ (univ:Finset _))=> Logos P s i j H p hT hU)).trans; change ∑ j:Single n, N*brass P x (V j.1.1) a ≤ _; rw [← mul_sum,rubyH V (fun i=>brass P x i a)]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (coin P u.2.2 x) hh) hp); unfold C; exact le_of_eq (by ring)
 · let V:=Tofu (incX s) n; let x:= V i.1.1; change ∑ j, logos P s e T U j i≤ C; apply (sum_le_sum (fun j (_:j ∈ (univ:Finset _))=> Logos P s j i H p hT hU)).trans; change ∑ j:Single n, N*brass P (V j.1.1) x a ≤ _; rw [← mul_sum,rubyH V (fun i=>brass P i x a),dress_h a x P u.1]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (coin P u.2.2 x) hh) hp); unfold C; exact le_of_eq (by ring)
 intro i x hp; change x.val=_ at hp; exact congrArg (mulC s P i.1 i.2.1 i.2.2) hp|>.trans (dry_mulC s P v i)

lemma dry_warm (m:ℕ)(w:0 < m)(h:0≤b)(H:0<a):∃ e C:ℝ,0<e∧ 0<C∧ ∀ (n:Side)(P:Toy m n),CardK n m P b a→DryPulse e C (warm P) e:=by
 let e:=a/ornament m; have he:0<e:= div_pos H (ornP m)
 obtain ⟨B,hx⟩:=dry_pay m w h he (show e*ornament m≤a from le_of_eq (div_mul_cancel₀ a (ornP ..|>.ne')))
 let P:= ((↑(Fintype.card Signed):ℝ)⁻¹)
 let V:=‖(P:ℂ)‖*(∑ _i:Signed,B)
 refine ⟨e,max V 1,he,lt_max_of_lt_right one_pos,fun n F u=>?_⟩
 have hz(s:Signed):DryPulse e B (ocean s F) e:=by unfold ocean; split;  exact (Dry_op (hx n F u s)).neg; exact hx n F u s -- missing
 have hp:= (DrySlot.sums (univ:Finset Signed) _ _ (fun i _=>hz i)).scale (↑P:ℂ); unfold warm; simp_rw [← Complex.coe_smul] 

 exact hp.dry_erase le_rfl (le_max_left ..)


end YM.CF.Moire
end

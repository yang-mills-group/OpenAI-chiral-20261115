import YM.SU5.FiniteGaugeData.Jadot.Dinar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
/-! # Calibrated Cholesky, field-one incl moving mass. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Fock.Reduction
open Function Filter Finset Brique NormedSpace MeasureTheory Pastry Scree Cascade Hutch Drama Dinar Relief
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
namespace Rheims
variable {n:Type*} [Fintype n]
section
variable [DecidableEq n]{Q P A B L Z D S:Op n}{a ε s μ:ℝ}
structure Milieu (Q A:Op n):Prop where
  litA:lit A
  lowerV:A*(1-Q)=1-Q
structure Spear(Q Z:Op n):Prop where
  up:Q*Z=Z
  low: Z*(1-Q)=Z
namespace Spear
variable(h:Spear Q Z)
include h
lemma lo : Z*Q=0:=by have p:=h.low; rw [mul_sub,mul_one] at p; exact (sub_eq_self.mp p) -- tune
lemma lowerP (q:IsStarProjection Q): (1-Q)*star Z=star Z:= by nth_rw 1 [← q.one_sub.2.star_eq]; rw [←star_mul,h.low]
lemma duelP (q:IsStarProjection Q) : Q*star Z=0:=by nth_rw 1 [←q.2.star_eq]; rw [←star_mul,h.lo,star_zero]
lemma stab (q:IsStarProjection Q): star Z*Q=star Z:=by nth_rw 1 [←q.2.star_eq]; rw [←star_mul,h.up]
lemma zero_sq: Z*Z=0:=by nth_rw 2 [←h.up]; rw [←mul_assoc,h.lo,zero_mul]
lemma twist_e(V:UNI n):Spear (twist V Q) (twist V Z):=⟨by rw [←map_mul,h.up],by rw [show (1 : Op n)-twist V Q=twist V (1-Q) from by rw [map_sub,map_one],←map_mul,h.low]⟩
-- various prices
end Spear
lemma turns_lit (V:UNI n)(h:lit A): lit (twist V A):=⟨le_trans (le_of_eq ((map_zero (twist V)).symm)) (twist_mono V h.1),h.2.map _⟩
lemma commute_invl(h: Commute A B)(p: lit A): Commute A⁻¹ B:=by
 apply p.2.mul_right_injective; show A*(A⁻¹*B)=A*(B*A⁻¹); rw [←mul_assoc,←mul_assoc A B,h.eq,mul_assoc B,lit_mulin p,one_mul,mul_one] -- Commute defeq
lemma sqrt_comm (h: Commute A B):Commute (ReflW A) B:= h.cfcₙ_nnreal _
lemma diff_pos(h:Commute A B)(v:A≤B)(p:0≤A): (B-A)*(B-A) ≤ B*B-A*A:=by
 let X:= B-A; have ht:0≤A*X:= Commute.mul_nonneg p (sub_nonneg.mpr v) (h.sub_right (Commute.refl A))
 refine sub_nonneg.mp ?_; rw [show B*B-A*A-(B-A)*(B-A)= A*X+A*X by unfold X; simp only [sub_mul,mul_sub, h.eq]; abel]; exact add_nonneg ht ht
namespace Milieu
variable (h:Milieu Q L) (p:IsStarProjection Q)
include h
lemma upperR : star L=L:= IsSelfAdjoint.of_nonneg h.litA.1
lemma lowerL(p:IsStarProjection Q): (1-Q)*L=(1-Q):=by
 nth_rw 1 [←p.one_sub.isSelfAdjoint.star_eq,←h.upperR]; rw [←star_mul,h.lowerV,p.one_sub.2.star_eq] -- tune p.one_sub not q
lemma busy(p:IsStarProjection Q): Commute L Q:=by
 have he:L-L*Q=L-Q*L:=by simpa [mul_sub,sub_mul] using h.lowerV.trans (h.lowerL p).symm
 exact sub_right_inj.mp he
lemma invM : Milieu Q L⁻¹:= by
 refine ⟨lit_inv h.litA,?_⟩; conv_lhs=> right; rw [←h.lowerV]
 rw [←mul_assoc,lit_inmul h.litA,one_mul]
lemma rootM (p:IsStarProjection Q): Milieu Q (ReflW L):=by
 let R:= ReflW L; let K:=1-Q; have hy:Commute R K:=(Commute.one_right R).sub_right (sqrt_comm (h.busy p)); have hl: lit R:= refl_live h.litA; have he : R*K=K:=by
    apply (CFC.sqrt_unique (show R*K*(R*K)=K from by rw [mul_assoc, ← mul_assoc K R,hy.eq.symm,mul_assoc R K K,show K*K=K from p.one_sub.1,←mul_assoc,show R*R=L from refl_sq h.litA.1,h.lowerV]) (hy.mul_nonneg hl.1 p.one_sub.nonneg)).symm.trans; exact CFC.sqrt_unique (p.one_sub.1) p.one_sub.nonneg
 exact ⟨hl,he⟩
lemma rootI(p:IsStarProjection Q): Milieu Q (tangle L):= h.invM.rootM p
lemma entire(p:IsStarProjection Q): Q*L*Q+(1-Q)= L:=by
 have ht:= h.busy p; rw [←ht.eq, mul_assoc, p.1]; have hx:= h.lowerV; rw [mul_sub,mul_one] at hx; rw [←hx]; abel -- wrong rewrite Q? (`←eq` transforms Q*L)
lemma glow(V:UNI n): Milieu (twist V Q) (twist V L):=⟨turns_lit V h.litA, by rw [show 1-twist V Q=twist V (1-Q) from by rw [map_sub,map_one],←map_mul,h.lowerV]⟩
end Milieu
-- graph weight and inverse
abbrev Pall (L Z:Op n):Op n:= (1-star Z)*L
abbrev Hail (L Z:Op n):Op n:= L⁻¹*(1+star Z)
namespace Pall
variable (l:Milieu Q L)(h:Spear Q Z)(p:IsStarProjection Q)
include l h
lemma mun : Pall L Z * Hail L Z=1:=by
 unfold Pall Hail; rw [mul_assoc _,←mul_assoc L,lit_mulin l.litA,one_mul,sub_mul,one_mul,mul_add,mul_one,←star_mul,h.zero_sq,star_zero,add_zero]; abel -- tune assoc
lemma wun : Hail L Z*Pall L Z=1:=mul_eq_one_comm.mp (mun l h)
include p
lemma upper: Q*(Pall L Z)=L*Q:=by unfold Pall; rw [←mul_assoc,mul_sub,h.duelP p,mul_one,sub_zero]; exact (l.busy p).eq.symm
lemma hailV: star (Hail L Z) = L⁻¹ + Z:=by unfold Hail; rw [star_mul,star_add,star_one,star_star,l.invM.upperR,add_mul,one_mul,show Z*L⁻¹=Z from ?_]; nth_rw 1 [←h.low]; rw [mul_assoc,l.invM.lowerL p,h.low]
lemma rotV (V:UNI n): Pall (twist V L) (twist V Z)=twist V (Pall L Z):=by unfold Pall; rw [map_mul,map_sub,map_one,map_star]
omit p
end Pall
abbrev frost(Q P:Op n)(μ:ℝ) := bloom Q (Q*P) μ
abbrev Lumi(Q P:Op n)(μ:ℝ) := tangle (frost Q P μ)
abbrev Zami(Q P:Op n)(μ:ℝ) := Lumi Q P μ * (Q*P) * (1-Q)
variable(h:IsStarProjection Q)(p:IsStarProjection P)
include h
lemma accord_f: Q*(Q*P)=Q*P:=by rw [←mul_assoc,h.1]
lemma foom : frost Q P μ*(1-Q)=1-Q:=by
 let S:=Q*P; have he:star S * (1-Q)=0:=by nth_rw 1 [←h.one_sub.2.star_eq]; rw [←star_mul, sub_mul,one_mul, show Q*S=S from accord_f h,sub_self,star_zero]
 unfold frost bloom spring; rw [add_mul,add_mul,Algebra.smul_mul_assoc, Porth h,smul_zero,h.one_sub.1,mul_assoc (Q*P),he,mul_zero,zero_add,add_zero]
lemma isle (v:lit (frost Q P μ)): Milieu Q (frost Q P μ):=⟨v,foom h⟩
lemma pole (v:lit (frost Q P μ)): Milieu Q (Lumi Q P μ):= (isle h v).rootI h
lemma ice (v:lit (spring Q (Q*P)))(w:0≤μ): lit (frost Q P μ):=by
 have hp: spring Q (Q*P) ≤ frost Q P μ:=le_add_of_nonneg_right (smul_nonneg w h.nonneg)
 exact ⟨v.1.trans hp,CStarAlgebra.isUnit_of_le _ hp v⟩
lemma paean (v:lit (frost Q P μ)): Q*(Lumi Q P μ*(Q*P))= Lumi Q P μ*(Q*P):=by rw [←mul_assoc,←((pole h v).busy h).eq,mul_assoc,accord_f h] -- parentheses
lemma heart (v:lit (frost Q P μ)): Spear Q (Zami Q P μ):=⟨by unfold Zami; rw [←mul_assoc,paean h v],by unfold Zami; rw [mul_assoc (Lumi _ _ μ *(Q*P)), h.one_sub.1]⟩
lemma extra_lt (v:0≤μ): (Q*P)*star (Q*P) ≤ frost Q P μ:= (le_add_of_nonneg_right h.one_sub.nonneg).trans (le_add_of_nonneg_right (smul_nonneg v h.nonneg))
omit h in
private lemma own2' (X:Op n)(t:star X*X ≤1):‖X‖≤1:=by nth_rw 1 [← norm_star X]; apply own2 _ zero_le_one; rw [one_pow,Canon,one_smul,star_star]; exact t
lemma revenuePP(t:lit (frost Q P μ))(v:0≤μ): ‖Lumi Q P μ*(Q*P)‖≤1:=by
 let H:=frost Q P μ; let L:= Lumi Q P μ; let B:=Q*P; let R:=L*B; have he:= (pole h t).upperR; have he: R*star R≤1:=by
    rw [show star R=star B*L from by unfold R; rw [star_mul,he]]; unfold R; rw [←mul_assoc,mul_assoc L B]; apply le_trans (b:=L*H*L); · exact IsSelfAdjoint.conjugate_le_conjugate (extra_lt h v) he
    rw [show L*H*L=1 from tangle_n t]; -- tune
 change ‖R‖≤_; apply own2 _ zero_le_one; rw [one_pow,Canon,one_smul]; exact he
lemma revenueZZ (t:lit (frost Q P μ))(v:0≤μ): ‖Zami Q P μ‖ ≤ 1:= (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (h.one_sub.norm_le _)).trans (revenuePP h t v))
lemma frost_order {s t:ℝ}(v:s≤t): frost Q P s ≤ frost Q P t:= by apply add_le_add le_rfl (smul_le_smul_of_nonneg_right v h.nonneg) -- tune
lemma frost_diff (μ a:ℝ): frost Q P (μ+a)=frost Q P μ+a • Q:=by unfold frost bloom; rw [add_smul]; abel
lemma frost_com(t:lit (frost Q P μ))(a:ℝ): Commute (frost Q P μ) (frost Q P a):=by
 rw [show frost Q P a=frost Q P μ+(a-μ) • Q by rw [←frost_diff h, add_sub_cancel μ a]] -- name
 exact (Commute.refl _).add_right (((isle h t).busy h).smul_right (a-μ))
-- for anti-order $L$ (full PSD). Already for ≥0 via thick.
lemma lumi_diff (u:lit (frost Q P s))(v:s≤a)(t:lit (frost Q P a)):
  0 ≤ Lumi Q P s-Lumi Q P a ∧ (Lumi Q P s-Lumi Q P a)*(Lumi Q P s-Lumi Q P a) ≤ (frost Q P s)⁻¹-(frost Q P a)⁻¹:=by
 let T:=frost Q P s; let L:= Lumi Q P s; let K:=Lumi Q P a; let H:= frost Q P a
 have he: Commute T⁻¹ H⁻¹:= (commute_invl (commute_invl (frost_com h u a) u).symm t).symm
 have hz: Commute K L := sqrt_comm (sqrt_comm he).symm
 have hp:H⁻¹ ≤ T⁻¹:= inv_order u (frost_order h v); have hv: K ≤ L:= CFC.sqrt_le_sqrt _ _ hp
 exact ⟨sub_nonneg.mpr hv,(diff_pos hz hv (pole h t).litA.1).trans_eq (by rw [show L*L=T⁻¹ from intake_t u,show K*K=H⁻¹ from intake_t t])⟩
include p
lemma prism_L (t:lit (frost Q P μ)) : Lumi Q P μ * P = Lumi Q P μ *(Q*P) + (1-Q)*P:=by
 let T:=Lumi Q P μ; change T*P=T*_+_; rw [←mul_assoc,← Milieu.lowerV (pole h t),←add_mul]; apply congrArg (·*P); rw [mul_sub,mul_one]; abel -- tune occurrence of `1-Q`
lemma accord_b (t:lit (frost Q P μ)): Pall (Lumi Q P μ) (Zami Q P μ)*P= let A:= Lumi Q P μ*(Q*P); A+(1-Q)* (P-star A*A):=by
 let T:=Lumi Q P μ; let Z:=Zami Q P μ; let A:=T*(Q*P); change (1-star Z)*T*P=A+_; have he:star Z=(1-Q)*star A:=by unfold Z Zami; rw [star_mul,h.one_sub.2]
 have hz:=heart h t; rw [mul_assoc, prism_L h p t]; change (1-star Z)*(A+(1-Q)*P)=_; rw [sub_mul,one_mul,mul_add,←mul_assoc (star Z) (1-Q), mul_sub (star Z), mul_one,hz.stab h,sub_self, zero_mul,add_zero,he,mul_sub (1-Q),mul_assoc]; abel -- price
-- not using ∥P∥ enough alone; price square
lemma authority (t:lit (frost Q P μ))(e:0≤μ): ‖Pall (Lumi Q P μ) (Zami Q P μ) * P‖ ≤ 1:=by
 let L:=Lumi Q P μ; let A:=L*(Q*P); let X:=star A*A; let Y:=1-X; let B:=(1-Q)*P; have hx:‖A‖≤1:= revenuePP h t e
 have he{X:Op n}(g:‖X‖≤1):star X*X ≤1:= le_trans CStarAlgebra.star_mul_le_algebraMap_norm_sq ((algebraMap_mono _ (show ‖X‖^2≤1 from by nlinarith only [g,norm_nonneg X])).trans_eq (map_one _))
 have ht:X≤1:=he hx; have hx0:0≤X:=star_mul_self_nonneg _
 have hR:Y*Y≤Y:=by
    apply sub_nonneg.mp; rw [show Y-Y*Y=X*Y from by unfold Y; noncomm_ring]; exact Commute.mul_nonneg hx0 (sub_nonneg.mpr ht) ((Commute.one_right X).sub_right (Commute.refl _))
 have hb: ‖B‖≤1:= (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (h.one_sub.norm_le _)).trans (p.norm_le P))
 have hs:star Y=Y:= IsSelfAdjoint.of_nonneg (show 0≤Y from sub_nonneg.mpr ht); have hi : star (B*Y)*(B*Y)≤ Y:=by
    rw [star_mul,hs,←mul_assoc,mul_assoc Y (star B)]; exact (IsSelfAdjoint.conjugate_le_conjugate (he hb) hs).trans ((by rw [mul_one]: Y*1*Y=Y*Y).trans_le hR)
 have hy:B*Y=(1-Q)*(P-X):=by
    have hb:A*P=A:=by unfold A; rw [mul_assoc L _ P, mul_assoc Q P P,p.1]; -- tune assoc reversed
    have hx:P*star A=star A:=by nth_rw 1 [←p.2.star_eq]; rw [←star_mul,hb]
    unfold B Y; rw [mul_assoc, mul_sub P,mul_one]; unfold X; rw [←mul_assoc P (star A) A,hx]; -- tune
 have hA:star A*(B*Y)=0:=by
    have hu:Q*A=A:= paean h t; unfold B; nth_rw 1 [←hu]; rw [star_mul,h.2,mul_assoc (1-Q),mul_assoc,←mul_assoc Q,Porth h,zero_mul,mul_zero]
 have hB:star (B*Y)*A=0:=by nth_rw 1 [←star_star A]; rw [←star_mul,hA,star_zero] -- beware occurrence A in B Y (reducible?)
 apply own2'; rw [accord_b h p t]; change star (A+ (1-Q)*(P-X)) * (A+ (1-Q)*(P-X)) ≤ _; rw [←hy,star_add,add_mul,mul_add,mul_add,hA,hB,zero_add,add_zero]; exact (add_le_add le_rfl hi).trans_eq (by change X+Y=_; unfold Y; abel) -- tune
lemma costLP (t:lit (frost Q P μ))(e:0≤μ): ‖Lumi Q P μ * P‖ ≤ 2:=by
 rw [prism_L h p t]; exact (norm_add_le ..).trans ((add_le_add (revenuePP h t e) ((norm_mul_le ..).trans (mul_le_one₀ (h.one_sub.norm_le _) (norm_nonneg _) (p.norm_le _)))).trans_eq (by norm_num)) -- tune
-- floor & mark localization
lemma lumi_floor (e:0≤μ)(u:μ≤1)(v:lit (frost Q P μ)) : Canon n (1/2) ≤ Lumi Q P μ:=by
 have he:‖Q*P‖≤1:=(norm_mul_le ..).trans (mul_le_one₀ (h.norm_le _) (norm_nonneg _) (p.norm_le _)); have hh: frost Q P μ ≤ Canon n 4:=by
    have hl: ((Q*P)*star (Q*P))≤ Canon n 1:= le_trans CStarAlgebra.mul_star_le_algebraMap_norm_sq (by rw [canon_map]; exact algebraMap_mono _ (by nlinarith only [he,norm_nonneg (Q*P)]))
    have hu: ∀ A:Op n,0≤A→‖A‖≤1→ A≤Canon n 1:=by intro A p hp; rw [canon_map]; exact (CStarAlgebra.norm_le_iff_le_algebraMap _ zero_le_one p).mp hp
    have hw: ‖μ • Q‖≤1:=by rw [norm_smul,Real.norm_of_nonneg e]; exact mul_le_one₀ u (norm_nonneg _) (h.norm_le _)
    refine (add_le_add (add_le_add hl (hu _ h.one_sub.nonneg (h.one_sub.norm_le _))) (hu _ (smul_nonneg e h.nonneg) hw)).trans ?_; unfold Canon; rw [←add_smul,←add_smul]; exact smul_le_smul_of_nonneg_right (by norm_num) zero_le_one -- tune closure
 let T:=Canon n (1/2); have he: T*T=(Canon n 4)⁻¹:=by
    apply (canon_live (n:=n) (by norm_num:(0:ℝ)<4)).2.mul_right_injective; change Canon n 4*(T*T)=Canon n 4*(Canon n 4)⁻¹; rw [lit_mulin (canon_live (by norm_num:(0:ℝ)<4))]; unfold T; rw [canon_left,canon_left]; unfold Canon; rw [smul_smul,smul_smul]; norm_num
 exact (CFC.sqrt_unique he (canon_nn (by norm_num))).symm.trans_le (CFC.sqrt_le_sqrt _ _ (inv_order v hh)) -- tune sqrt RHS Lumi
omit p h
lemma rise_cost (c:lit (frost Q P μ)): rueD (Lumi Q P μ)= -rueD (frost Q P μ)/2:=by
 have v:lit (Lumi Q P μ):= refl_live (lit_inv c); have he:= intake_t c; have h:= rue_pair v v; change tangle _ *tangle _ = _ at he; rw [show _*_=(frost Q P μ)⁻¹ from he,rue_inv c] at h; linarith
-- little more later
end
end Rheims
end YM.CF.Fock.Reduction

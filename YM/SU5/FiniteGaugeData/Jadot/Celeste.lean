import YM.SU5.FiniteGaugeData.Jadot.Ziz
import YM.CF.Spire.Quartz
/-! # Bra calibration. Likewise for gauge-transformed tilt. -/
set_option autoImplicit false
set_option synthInstance.maxSize 17000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Fock.Reduction
open Function Filter Finset Brique NormedSpace MeasureTheory Pastry Scree Cascade Hutch Drama Dinar Relief Rheims Dijon Currency Fist Ziz Thera Spire Scroll
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
namespace Celeste
variable {n:Type*}[LinearOrder n][Fintype n]{P Q H W L Z Y:Op n}{x p q y:Wave n}
abbrev lever (H W:Op n)(X:FC n):=quant H*X*quant W
namespace lever
variable (kWh: H*W=1)(kWg:W*H=1)
include kWh kWg
lemma nilV : lever H W 0=0:=by simp only [lever,mul_zero,zero_mul]
lemma stockI : lever H W 1=1:=by unfold lever; rw [mul_one,←quant_mul,kWh,quant_one]
lemma sums(X Y:FC n):lever H W (X+Y)=lever H W X+lever H W Y:=by unfold lever; rw [mul_add,add_mul]
lemma semi(X:FC n)(c:ℂ): lever H W (c • X)=c • lever H W X:=by unfold lever; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
lemma gapI(X Y:FC n):lever H W (X-Y)=lever H W X-lever H W Y:=by unfold lever; rw [mul_sub,sub_mul]
lemma mult(X Y:FC n): lever H W (X*Y)=lever H W X * lever H W Y:=by
 unfold lever; rw [mul_assoc (quant H*X) (quant W),←mul_assoc (quant W),← mul_assoc (quant W),←quant_mul,kWg,quant_one,one_mul,mul_assoc,mul_assoc,mul_assoc] -- tune
lemma uphill (u:Ket n): lever H W (create u)= create (acts H u):=by unfold lever; rw [quant_create,mul_assoc,←quant_mul,kWh,quant_one,mul_one]
lemma takeDown(u:Ket n):lever H W (remove u)=remove (acts (star W) u):=by unfold lever; rw [mul_assoc,quant_ann,←mul_assoc,←quant_mul,kWh,quant_one,one_mul] -- tune quant_ann order
lemma twist_I (V:UNI n)(A:FC n): lever (twist V H) (twist V W) (twist (quantU V) A) = twist (quantU V) (lever H W A):=by unfold lever; rw [quant_twist,quant_twist,map_mul,map_mul]
end lever
variable (l:Milieu Q L)(z:Spear Q Z)(Ω:IsStarProjection Q)
local notation "W8"=> Pall L Z
local notation "Γ"=> Hail L Z
local notation "J"=> lever (Pall L Z) (Hail L Z)
abbrev cost (L Z:Op n)(X:FC n):FC n:= lever (Pall L Z) (Hail L Z) X
-- bra normalization
include l z Ω
lemma MindBL(u:Sea Q p): acts (quant (star (Hail L Z))) p = Matrix.det (L⁻¹) • p:=by
 have he:= Milieu.busy l.invM Ω; let W:=Hail L Z; let T:= star W; have hh:T*Q=L⁻¹ *Q:=by unfold T; rw [show star W= _ from Pall.hailV l z Ω]; rw [add_mul,z.lo,add_zero]
 have hT:(L⁻¹)*Q=Q*(L⁻¹)*Q:=by rw [← he.eq,mul_assoc,Ω.1]
 nth_rw 1 [← sea_idke Ω u]; rw [←act_mul,←quant_mul,show star Γ *_= _ from hh, hT,beamV Ω Ω rfl (L⁻¹) p u p u, meadow Ω _ u (L⁻¹), Milieu.entire l.invM Ω] -- `nth` tunes
lemma opacity (u:Sea Q p)(y:Wave n)(X:FC n): inner ℂ p (acts X y)=star (Matrix.det L⁻¹) * inner ℂ p (acts (lever (Pall L Z) (Hail L Z) X) (acts (quant (Pall L Z)) y)):=by
 rw [show ∀ F:Wave n,star (Matrix.det L⁻¹) * inner ℂ p F=inner ℂ (Matrix.det L⁻¹ • p) F from fun f=> (inner_smul_left ..).symm,←MindBL l z Ω u]; -- after apply to RHS
 rw [quant_star,act_inner,←act_mul (quant Γ),←act_mul]
 unfold lever
 congr 2
 rw [show quant Γ*(quant W8*X*quant Γ)*quant W8= X from ?_]; -- tune nested location
 rw [←mul_assoc,←mul_assoc,←quant_mul,Pall.wun l z,quant_one,one_mul,mul_assoc,←quant_mul,Pall.wun l z,quant_one,mul_one] -- tune
lemma smokeX(u:Sea Q p)(A:FC n)(y:Wave n): ‖inner ℂ p (acts A y)‖ ≤ Real.exp (-rueD L)* ‖acts (star (cost L Z A)) p‖ * ‖acts (quant (Pall L Z)) y‖:=by
 rw [opacity l z Ω u y A,norm_mul,norm_star,←act_inner,←rue_inv l.litA,rueD, Real.exp_log (norm_pos_iff.mpr (def_beam (lit_inv l.litA)).ne'),mul_assoc]; exact mul_le_mul_of_nonneg_left (norm_inner_le_norm ..) (norm_nonneg _)
-- Free comparator at unrepaired L0,Z0 for field-one.T. Use Standing.
omit Ω l z
variable (g:Standing Q P)
abbrev Lemp(Q P:Op n):= Lumi Q P 0
abbrev Zemp(Q P:Op n):= Zami Q P 0
abbrev smut (Q P:Op n)(A:FC n):= cost (Lemp Q P) (Zemp Q P) A
namespace Cardio
include g
local notation "QK"=> Q*P
local notation "η"=> Lemp Q P
local notation "Z8"=> Zemp Q P
lemma live : lit (Rheims.frost Q P 0):=by unfold Rheims.frost; rw [bloom_zero]; exact g.litA
lemma heart : Spear Q (Zemp Q P):=Rheims.heart g.carpet (live g)
lemma warm : Milieu Q (Lemp Q P):=pole g.carpet (live g)
lemma pulse : Q*(Pall (Lemp Q P) (Zemp Q P)*P)=Pall (Lemp Q P) (Zemp Q P)*P:=by
 let T:=spring Q (Q*P); have h:=g.litA; let X:=η*(Q*P); have hh:star X*X=P:=by
    unfold X; rw [star_mul,(warm g).upperR,←mul_assoc,mul_assoc (star (QK)),show η*η=T⁻¹ from (show Rheims.frost Q P 0=T from bloom_zero ..) ▸ intake_t (live g)] -- maybe notation ambigu & substitution messing
    -- now =star QK*T^-1*(Q*P). via T*P=P
    have hx:star (Q*P)*T⁻¹*(Q*P)=oblique Q P*P:=by unfold oblique; unfold T; simp only [mul_assoc]
    exact hx.trans (TuneC.up g.luxury)
 rw [accord_b g.carpet g.hedge (live g)]; simp only [show star (Lemp Q P*(QK))*(Lemp Q P*(QK))=P from hh,sub_self,mul_zero,add_zero]; exact paean g.carpet (live g)
lemma cashG(l:Sea Q p)(u:Sea P x)(A:FC n): inner ℂ p (acts A x) / inner ℂ p x= inner ℂ p (acts (smut Q P A) p):=by
 let F:= Pall η Z8; let c:= skyGlow p F x; have h:acts (quant F) x=c • p:=by nth_rw 1 [← sea_idke g.hedge u]; rw [←act_mul,←quant_mul,←pulse g,←mul_assoc]; exact beamV g.hedge g.carpet g.balance _ _ u _ l -- let issue
 have he:inner ℂ p x≠0:= (vision g u l 1).1; apply (div_eq_iff he).mpr; have hz := opacity (warm g) (heart g) g.carpet l x 1; rw [act_one,lever.stockI (Pall.mun (warm g) (heart g)) (Pall.wun (warm g) (heart g)),act_one,h,inner_smul_right,inner_self_eq_norm_sq_to_K,l.2] at hz -- id tune
 rw [opacity (warm g) (heart g) g.carpet l x A,h, hz,map_smul,inner_smul_right]; change star _*(c*_)= _*(star _* _); -- subtraction from hz. Lean type info
 unfold smut cost Lemp Zemp; ring_nf; simp -- tune
end Cardio
lemma existenceSea (p:IsStarProjection P):∃ y:Wave n, Sea P y:=by
 obtain ⟨U,S,e⟩:= spot_projection _ p; subst P; refine ⟨_,?_, wedge_norm U S⟩; rw [act_twistLine,inner_self_eq_norm_sq_to_K,wedge_norm]; simp
open scoped Classical
def mantle(P:Op n): Wave n:= if h:IsStarProjection P then (existenceSea h).choose else 0
lemma mantleP(u:IsStarProjection P): Sea P (mantle P):=by unfold mantle; rw [dif_pos u]; exact (existenceSea u).choose_spec
/-- canonical slope: phase-independent spectral charge. -/
abbrev Volt(Q P:Op n)(A:FC n):ℂ:= inner ℂ (mantle Q) (acts A (mantle P))/inner ℂ (mantle Q) (mantle P)
include g
lemma mission (A:FC n): Volt Q P A= inner ℂ (mantle Q) (acts (smut Q P A) (mantle Q)):= Cardio.cashG g (mantleP g.carpet) (mantleP g.hedge) A
omit g
lemma pour_phase (q:IsStarProjection Q)(u:Sea Q x)(v:Sea Q y):∃ a:ℂ, y=a • x ∧ ‖a‖=1:=by
 have he: y=inner ℂ x y • x:= v.1.symm.trans (Sea.scalar q u y); have ht:=v.2; nth_rw 1 [he] at ht; rw [norm_smul,u.2,mul_one] at ht; exact ⟨_,he,ht⟩
lemma pressORT(q:IsStarProjection Q)(u:Sea Q x)(v:Sea Q y)(A:FC n): inner ℂ x (acts A x)=inner ℂ y (acts A y):=by
 obtain ⟨r,rfl,p⟩:= pour_phase q u v; rw [map_smul,inner_smul_left,inner_smul_right,←mul_assoc,show (starRingEnd ℂ) r*r=1 from scale_unit_self p,one_mul]; -- tune rewrite order
lemma pressV(q:IsStarProjection Q)(u:Sea Q x)(v:Sea Q y)(A:FC n): ‖acts A x‖=‖acts A y‖:=by obtain ⟨r,rfl,p⟩:= pour_phase q u v; rw [map_smul,norm_smul,p,one_mul]
include g
lemma bill(u:Sea Q x)(v: Sea P y)(A:FC n): Volt Q P A=inner ℂ x (acts A y)/inner ℂ x y :=by rw [mission g,Cardio.cashG g u v]; exact pressORT g.carpet (mantleP g.carpet) u _
-- rotations incl θ using tour
section
variable {P' Q':Op n} (g':Standing Q' P')(U:UNI n)(a b:Bool)
include g g' a b U
lemma voltR (hp: sings a U Q=swapX b Q')(hQ:sings a U P=swapX b P')(A:FC n): Volt Q' P' (tourP U a b A)=cSignX (a.xor b) (Volt Q P A):=by
 let X:= mantle Q; let Y:=mantle P; let T:=oculus U a b; have he{P P':Op n}(h:IsStarProjection P)(q:sings a U P=swapX b P')(x:Wave n)(p:Sea P x): Sea P' (T x):=by unfold T; constructor; rw [← tour_line U a b P P' h q,←oo_by,p.1]; rw [oo_norm,p.2]
 rw [bill g' (he g.carpet hp X (mantleP g.carpet)) (he g.hedge hQ Y (mantleP g.hedge)), ←oo_by]; unfold T; rw [oo_globe,oo_globe]; unfold Volt; cases hh:a.xor b; rfl; exact (map_div₀ (starRingEnd ℂ) _ _).symm -- syntax
end
lemma voltRefl(U:UNI n)(p:twist U (1-Q)=Q)(h:twist U (1-P)=P)(A:FC n): Volt Q P (theta U A)=star (Volt Q P A):=by
 have hh : ∀ X:Op n,twist U (1-X)=X→sings false U X=swapX true X:=fun X e=>by change twist U X=1-X; rw [map_sub,map_one] at e; nth_rw 2 [←e]; abel -- RHS occurrence tune
 exact voltR g g U false true (hh Q p) (hh P h) A -- need cSign defin
end Celeste
end YM.CF.Fock.Reduction

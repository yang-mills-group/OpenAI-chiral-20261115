import YM.SU5.FiniteGaugeData.Tower.Gallery
/-!
# Finite warm log-convex interpolation of the physical two-satellite train

gq=the origin in clock units (cover, not modulus). One-plane CS around
internal and external seam. Need ending positions of endpoint y in buffered
stencil at distance 2w+, for asynchronous half circumference. Width/account
comparisons in further modules. No translation invariance assumption on finite
ratios, keep the origin explicit.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Heat Analysis
section principal
variable {K:Calibration}{m:Side}{L:Scree.Loom (K.c m)}{Y:Mark (K.c m) →ℂ}{D:ℝ}(p:Metered K m L Y D)
local notation "N"=> K.c m
variable (j:Axis)(w:ℤ)(f x:Family K)
local notation "U" i:max=> relocate K j i
local notation "R" i:max=> mirror K j i
local notation "b₀"=>ruler K.B
local notation "r" i:max=>gaugeT K i
local notation "f₂" i:max n:max=>b₀ * (i*n)
local notation "J"=>lace K j w
local notation "I"=>toward K j w
local notation "O"=>plow K j
/-- full train as written relative to aligned center v, use all, translate using
two-theta motion. width = w (clock units, double time). -/
noncomputable def chambers (v:ℤ)(f x:Family K)(n:ℕ):Family K:= (U v) ((R 0) (J f x n)* J f x n)
local notation "F" i:max x:max n:max=> chambers j w i f x n
/-- charged inequality between translated trains (algebra only, quals below). show exact two shares forming the 2 section budgets. -/
private lemma chamber_plus {n:ℕ}(v:ℤ)(t:TestFamily K true f)(h:TestFamily K true x):
 let B:=(U (v+w)) (J f x n)
 let A:=(U v) ((R 0) (J f x (n+1)) * I f n)
 let d:=r (2*(v+w))
 (F v x (n+1))=A*B ∧
 A*((R d) A)=F (v+w) x (n+2) ∧ (R d) B*B=F (v+w) x n:=by
 intro B A d
 let z:=I f n; let X:= J f x (n+1)
 have hZ(k):=lace_paid K j w t h k
 have hx:=hZ (n+1)
 have hz:=toward_paid K j w t n
 have h₁(q:ℤ)(a:Family K)(t:TestFamily K true a): (R (r (2*q))) ((U q) a)=(U q) ((R 0) a):=by
   rw [odd_cancel K j _ 0 _ t,show 2*q-0-q=q from by ring,gaugeT_zero]
 have Aeq:A=(U (v+w)) ((R 0) (J f x (n+2))):=by
   rw [lacing,toward_step,mirror_times,relocate_mul,mirror_relocate K j _ _ hx,relocate_sums K j _ _ (reflect_ok K j _ hx),show (v+w)+ -w=v from by ring]
   change (U v) ((R (0:ℤ)) X * z)=(U (v+w)) ((R 0) ((R (r w)) z))* (U v) ((R 0) X)
   rw [mirror_at K j (show (0:ℤ)-r w=r (-w) from by unfold gaugeT gaugeShift; ring) hz,relocate_sums K j _ _ hz,show v+w+ -w=v from by ring, relocate_mul,even_tests K (move_ok K j _ hz) (move_ok K j _ (reflect_ok K j _ hx))]
 constructor
 · unfold chambers A B; rw [relocate_mul K j,relocate_mul K j (v)];
   change (U v) ((R 0) X) * (U v) (J f x (n+1))=(U v) ((R 0) X)*(U v) z* (U (v+w)) _
   rw [lacing K j w f x n,relocate_mul,relocate_sums K j _ _ (hZ n),mul_assoc]
 rw [Aeq]; unfold d B chambers; rw [h₁ (v+w) _ (hZ n),h₁ _ _ (reflect_ok K j _ (hZ (n+2))),mirror_invert K j _ (hZ (n+2)),relocate_mul,relocate_mul]
 exact ⟨rfl,rfl⟩
variable {f x}{S T:Finset Cover}{A:ℤ}{n:ℕ}(v:ℤ)(e:0 < w)(a:0≤ A)
 (hf:InTest K true S false f)(hs:Between K j 0 (ruler K.B*w) S)
 (ht:InTest K true T false x)(hZ:Between K j 0 A T)
-- B as above relative center v, n+1. A=U(v+w)θ... n+2. common z
include p hf ht a hs hZ e
lemma chamber_cut (he:f₂ w (n+2)+A ≤ ((N).val:ℤ)):
 ‖Y ((F v x (n+1)) m)‖^2 ≤ ‖Y ((F (v+w) x (n+2)) m)‖ * ‖Y ((F (v+w) x n) m)‖:=by
 let d:=r (2*(v+w))
 let b:=(U (v+w)) (J f x n)
 let i:=(U v) ((R 0) (J f x (n+1)) * I f n)
 obtain ⟨h,t,q⟩:=chamber_plus j w f x (n:=n) v (aux_test hf) (aux_test ht)
 change (F v x (n+1)) = i*b at h
 change (i * (R d) i)=F (v+w) x (n+2) at t
 let W:=f₂ w (n+2)+A; let c:=b₀*(v+w)
 have hd:d=c:=by unfold d c; rw [two_mul,gaugeT_add,←two_mul,ruler_offset]
 obtain ⟨s₂,X,k⟩:=spans_only K j e.le a hf hs ht hZ (n+1)
 obtain ⟨s₃,Z,kk⟩:=spans_only K j e.le a hf hs ht hZ n
 have ha₀ :∃ X:Axis→ℤ,∃ d:ℕ,Tower.CompactArc S d ∧ Transom j S X d:=trans_exists j S -- disambiguate
 obtain ⟨k0,n0,Vproof,h0⟩:=ha₀
 have saf:∃ S2:Finset Cover, InTest K true S2 false (toward K j w f n) ∧ Between K j 0 (b₀*w) S2 ∧ Transom j S2 k0 n0:=orient_room K j hf hs h0 n
 obtain ⟨sm₂,hY,hBetween,hgT⟩:=saf
 let T₀:=O (v+w) s₃
 let S₀:= O v (reflectedBox j 0 s₂ ∪ sm₂)
 have ht0:InTest K true T₀ false b:= flow_port K j _ Z
 have ht':InTest K true S₀ false i:= flow_port K j _ (((axial K j 0 X).mono subset_union_left).mul (hY.mono subset_union_right))
 let S':=reflectedBox j d S₀
 have hz:Between K j c (c+((N).val:ℤ)) T₀:=by
    have pi:= kk.relocate K j (v+w)
    intro x z; obtain ⟨k,h⟩:=pi x z
    rw [add_zero] at k; refine ⟨k,?_⟩
    have hr:=ruler_gene K.B; unfold c; nlinarith
 have hp:Between K j c (c+((N).val:ℤ)) S':=by
    have hr:=ruler_gene K.B; have hmk := k.mirror K j (0:ℤ)
    simp only [mul_zero,zero_sub,neg_zero] at hmk
    have hW:= Between.mirror K j ((Between.relocate K j (pair_between K j hmk hBetween (by exact neg_nonpos.mpr (by positivity)) (by positivity)) v)) d
    intro x z; obtain ⟨k,h⟩:=hW x z
    rw [hd] at k h
    simp only [Nat.cast_add_one,Nat.cast_add,Nat.cast_ofNat] at k h he; unfold c at *; constructor <;> nlinarith
 have hv:= seam_cut p j (2*(2*(v+w))) ht' ht0 (show Satin.region S' N⊆_ from enters_arc K j hp hd.symm) (enters_arc K j hz hd.symm)
 change ‖Y ((i*b) m)‖^2 ≤ ‖Y ((i*(R d) i) m)‖ * ‖Y (((R d) b*b) m)‖ at hv
 rw [h,←t,←q]; exact hv

-- raw price at every origin
noncomputable def worth (Y:Mark (K.c m)→ℂ)(j:Axis)(w:ℤ)(f x:Family K)(n:ℕ)(v:ℤ):=‖Y (chambers j w v f x n m)‖
noncomputable def principal(Y:Mark (K.c m)→ℂ)(j:Axis)(w:ℤ)(f x:Family K)(n:ℕ):ℝ:=sSup (Set.range fun v=>worth (m:=m) Y j w f x n v)
local notation "π" n:max=>principal (m:=m) Y j w f x n
local notation "ϕ" n:max v:max=>worth (m:=m) Y j w f x n v
omit hs hZ e a
lemma housing (Q c:ℝ)(h:pay f Q)(t:pay x c):ϕ n v≤π n:=by
 apply le_csSup _ (Set.mem_range_self _)
 let d:=Q^n*c
 use Real.exp (D*(m.val:ℝ)^4)*(d*d)
 rintro _ ⟨v,rfl⟩
 have h1:=lace_cost K j w Q c h t n; have hp:=lace_paid K j w (aux_test hf) (aux_test ht) n
 refine bill p (move_ok K j _ ((reflect_ok K j _ hp).mul hp)) (d*d) (chime_pay K j _ (d*d) (pay_mul (pay_flips K h1 j _) h1))
-- max principle for log convex finite
omit p hf ht in
lemma ladder_max (x:ℕ→ℝ)(n:ℕ){C B:ℝ}(h:0 < C)(k:0 < B)(g:∀ i ≤ n,0 ≤ x i)(q:x 0 ≤ C)(z:x n ≤ C*B^n)(v:∀ i:ℕ, i+1<n → x (i+1)^2 ≤x (i+2)*x i): ∀ i≤ n,x i ≤ C*B^i:=by
 let y i:=x i/(C*B^i)
 have he(i:ℕ):0<C*B^i:=by positivity
 have hp(i:ℕ)(a:i≤n):0 ≤ y i:=div_nonneg (g i a) (he i).le
 have hq(i:ℕ)(a:i+1<n): y (i+1)^2 ≤ y (i+2)*y i:=by
    unfold y; rw [div_pow,div_mul_div_comm,
      show (C*B^(i+2))*(C*B^i)=(C*B^(i+1))^2 by ring]
    exact div_le_div_of_nonneg_right (v i a) (sq_nonneg _)
 let s:= Finset.Iic n; obtain ⟨i,p,gM⟩:=Finset.exists_max_image s y ⟨0,Finset.mem_Iic.mpr (Nat.zero_le _)⟩
 have hB(j)(hj:j≤n): y j ≤ y i:=gM j (Finset.mem_Iic.mpr hj)
 have hY(v:ℕ)(vl:v≤n)(vh:y i≤ y v): y i≤1:=by
    induction v with
    | zero=> exact vh.trans (by unfold y; apply (div_le_one (he _)).mpr; simpa)
    | succ v ih=>
       by_cases z1:v+1=n
       · rw [z1] at vh; exact vh.trans ((div_le_one (he _)).mpr z)
       have h1:=hq v (by omega); apply ih (by omega)
       have hr:=hB (v+2) (by omega)
       have hv:= hp v (by omega); have e:= hp i (by simpa [s] using p); nlinarith [mul_le_mul_of_nonneg_right hr hv]
 intro b h
 simpa using (div_le_one (he b)).1 ((hB b h).trans (hY i (by simpa [s] using p) le_rfl))
end principal
end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.chamber_cut

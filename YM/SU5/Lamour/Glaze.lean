import YM.SU5.Velvet.Glint
import YM.CF.Buffered.Ranged
import YM.SU5.FiniteGaugeData.Pannier.Veldt
/-! # Flat Light. d seat-wise kernel & match to native absolute Bark. keep local unpaired-cost funding. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 190000
set_option quotPrecheck false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Lamour
open Function Filter Metric NormedSpace Lattice Wilson Laurent Finset Lat Ember Jill Rush Cube Fock Peaks
open Fir Next.Free Bloch SU Tulip Dial Spire Flare Kea Velvet Pannier.Chancel
open Window (polarWork polarLift polarClad polarMetric projector_norm_fact)
open Onyx Emu
open scoped Topology NNReal ENNReal Matrix Matrix.Norms.L2Operator BigOperators MatrixOrder Kronecker ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable (N:Side)(j:ℕ)(M:Jill.Male)
def lakeP(i:Stag N):= polarWork (field (too N) j M i) (freckles N j M i.1)
def lakeK(i:Stag N):= polarLift (field (too N) j M i) (freckles N j M i.1)
/-- reference for dressed RAW (all letters in T) against flat sea. -/
def lake:= Dofu N (lakeP N j M)
variable {N j}
lemma pitch (p:1≤j)(g:Even N.val):let Q:= (Dofu N (lakeK N j M)); Clad (Dofu N (field (too N) j M)) (tickA N) 1 1 Q ∧ lake N j M=laneP (tickA N) 1 Q:=by
 intro Q; have he:lakeP N j M= tilt 1 (lakeK N j M):=rfl
 unfold Q lake; -- Q names
 refine ⟨?_,?_⟩
 · nth_rw 1 2 [←map_one (Dofu N)]; apply torn (too N) g; intro i; let u:=meadow_stats N j p M g i; apply polarClad u.1 (by rw [u.2.1,dateA]) u.2.2.2.1 (falls_down p i.1 M)
 rw [he,Emu.tall_s,map_one]
lemma align_b(g:Even N.val)(z:Slot)(i:Site N): trackF (too N) (lakeP N j M) z i=dip j M (tmap (glen (zeroF N) i)):=by
 have hx:glen (zeroF N) i=pm i:=add_zero ..; rw [Onyx.dip,←Onyx.pear,ice_h g,hx,← Complex.ofReal_inv,BZ.ofReal_action]; unfold trackF; rw [show rake (too N) i z=(i,z) from (by simp [Emu.rake,too])]; unfold lakeP field; rw [too_u]; dsimp only; unfold Window.polarWork Window.polarLift laneP; rw [mul_one,Matrix.mul_smul,mul_assoc]; rfl -- tune
omit M
lemma lake_formal (p:1≤j):∃ C:ℝ,0<C∧∀ (N:Side),Even N.val→∀ (M:Jill.Male)(x:Slot), FormU ((too N).u x) j M C 1 (trackF (too N) (lakeP N j M) x):=by
 obtain ⟨c,C,h,q,Q⟩:=Jill.zip p; refine ⟨c/2,by positivity,fun N g M x=>?_⟩; constructor
 · exact fun i _=> align_b M g x i
 intro i v; change disk j M (pm i+0)≤_ at v; rw [add_zero] at v; exfalso; apply not_lt_of_ge v
 have hx:pinch N ≤‖pm i‖:= by have ht:= tall_p i; unfold Jill.tall at ht; simpa using (le_div_iff₀ (pinch_pos _)).mp ht
 refine lt_of_lt_of_le ((mul_lt_mul_of_pos_right (show c/2<c by linarith) (pow_pos (pinch_pos N) 2)).trans_le (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pinch_pos N).le hx 2) h.le)) (Q M _ (mass_valid i)).1
-- ROWf for cp4 math
lemma lake_range (p:1≤j)(w:ℝ)(v:0<w):∃ d t:ℕ,∀ {N:Side}, Pad j N → t≤ N.val →∀ (M:Jill.Male), ∃ P:Op (Single N),Buffered.Glaze.Ranged d P ∧ Buffered.Glaze.Billow w (lake N j M-P):=by
 obtain ⟨C,u,V⟩:=lake_formal p; obtain ⟨d,t,T⟩:=Buffered.Glaze.range_bill p u (by norm_num :(0:ℝ)<1) w v; exact ⟨d,t,fun {N} g W M=> T g W _ M _ (V N g.1 _)⟩ -- implicits T?
lemma lake_local (p:1≤j):∃ C:ℝ,0<C∧∀ {N:Side},Even N.val →∀ (M:Jill.Male), Buffered.Glaze.Billow C (lake N j M):=by
 obtain ⟨C,u,V⟩:=lake_formal p; obtain ⟨z,s,T⟩:=Gall.fame p u (by norm_num :(0:ℝ)<1); exact ⟨z,s,fun {N} W M=> T _ _ W (V N W _) ⟩ -- arg Pad? check
-- tilted compression Fourier
section spin
variable {P:Op SpinIdx} {d z:ℝ}
def slant {I:Type*}[LinearOrder I][Fintype I](T D:Op I)(z:ℝ):=(z^2)⁻¹ • ((1-T)*D*T)
/-- CRE cost of unsplit F_T letter from D-ordered grant -/
def wish {I:Type*}[LinearOrder I][Fintype I](T D:Op I)(z:ℝ)(b:Bool):= z⁻¹ • ((hand (!b) D)*(hand b T))
variable (h:IsStarProjection P)(p:P*Aop*P=d • P)(s:0<z)(v:z≤1)(f:0<d)(g:d≤1)
include h p s v f g
lemma tilted : let B:=coin d z; let H:=gate Aop z; draft P Aop z=B⁻¹ • (H*P*H):=by
 intro B H; let J:= hinge P Aop z; have hv:B*B⁻¹=1:=mul_inv_cancel₀ (coin_p f g).ne'
 have he:J*P=B • P:=by unfold J; rw [coin_gap h p,add_mul,Matrix.smul_mul,h.1,sub_mul,one_mul,h.1,sub_self,add_zero]
 have hj:J⁻¹*P=B⁻¹ • P:=by nth_rw 1 [← one_smul ℝ P,←hv, mul_comm B, mul_smul,←he]; rw [Matrix.mul_smul, ←mul_assoc,(live (hinge_unit h A_id s v)).2,one_mul]
 change H*P*J⁻¹*(P*H)=_; rw [mul_assoc (H*P), ←mul_assoc J⁻¹, hj,Matrix.smul_mul, Matrix.mul_smul, ←mul_assoc (H*P),mul_assoc H P P,h.1]
omit h p s v f g
lemma gateA(z:ℝ): gate Aop z*Aop=Aop:=by rw [Velvet.gate,add_mul,Matrix.smul_mul,AOne,sub_mul,one_mul,AOne,sub_self,smul_zero,add_zero]
lemma gateL(z:ℝ): minA*gate Aop z=z^2 • minA:=by rw [Velvet.gate,mul_add,Matrix.mul_smul, show 1-Aop=minA from rfl,show minA*Aop=0 from (by change (1-Aop)*Aop=0; rw [sub_mul,one_mul,AOne,sub_self]),zero_add,minA_p.isIdempotentElem]
include h p s v f g
lemma slant_diag: slant Aop (draft P Aop z) z=(d/coin d z) • polarWork P d:=by
 let H:=gate Aop z; let B:=coin d z; rw [slant,tilted h p s v f g]; rw [Matrix.mul_smul,Matrix.smul_mul, mul_assoc (1-Aop) _ Aop,mul_assoc _ H Aop,gateA]; let y:=minA*P*Aop; change (z^2)⁻¹ • (B⁻¹ • (minA*(H*P*Aop)))= _; unfold Window.polarWork Window.polarLift laneP; rw [mul_one, ←mul_assoc,←mul_assoc,gateL,Matrix.smul_mul,Matrix.smul_mul,smul_comm _ B⁻¹,inv_smul_smul₀ (pow_pos s _).ne',div_eq_mul_inv,mul_comm d, mul_smul, Matrix.mul_smul,smul_inv_smul₀ f.ne',mul_assoc]
lemma wish_diag (u:Aop*P*Aop=d • Aop)(q:minA*(1-P)*minA=d • minA)(b:Bool): ‖wish Aop (draft P Aop z) z b‖^2 ≤ z^2 * d⁻¹:=by
 let D:=draft P Aop z; let H:=gate Aop z; let A:= hand b Aop; let E:= hand (!b) D; let L:= minA; let B:=coin d z
 let r:= z^4*(1-d); have he:0≤r:= mul_nonneg (by positivity) (sub_nonneg.mpr g); have hp:d≤B:=le_add_of_nonneg_right he; have hb:0<B:=lt_of_lt_of_le f hp
 have hE: IsStarProjection E:=raft _ (draft_lit h A_id s v).1; have hA:= raft b A_id
 have hx:A*E*A=(r*B⁻¹) • A:=by
    cases b with
    | false =>
       have hj:Aop*H=Aop:=by exact (by have h:=congrArg star (gateA z); rwa [star_mul, A_id.isSelfAdjoint,gate_shine A_id] at h)
       change Aop*(1-draft P Aop z)*Aop=(r*B⁻¹) • Aop; rw [tilted h p s v f g,mul_sub,mul_one,sub_mul,AOne,Matrix.mul_smul,Matrix.smul_mul,←mul_assoc Aop,←mul_assoc Aop,hj,mul_assoc _ H Aop,gateA,u,smul_smul]; nth_rw 1 [←one_smul ℝ Aop]; rw [←sub_smul]; congr 1; change 1-B⁻¹*d=r*B⁻¹; have t:(d+r)*B⁻¹=1:=mul_inv_cancel₀ hb.ne'; linarith only [t]
    | true=>
       have hj:H*L=z^2 • L:=by exact (by have h:= congrArg star (gateL z); rwa [star_mul, minA_p.isSelfAdjoint,gate_shine A_id,star_smul,star_trivial,minA_p.isSelfAdjoint] at h)
       have hL: L*P*L=(1-d) • L:=by change L*(1-P)*L=d•L at q; rw [mul_sub L 1 P,mul_one,sub_mul L (L*P),minA_p.isIdempotentElem] at q; rw [sub_smul,one_smul,←q]; abel
       change L*draft P Aop z*L=_ • L; rw [tilted h p s v f g,Matrix.mul_smul,Matrix.smul_mul] -- probably wrong
       rw [←mul_assoc L, ←mul_assoc L,gateL, mul_assoc _ H L,hj,Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_mul,hL]; change B⁻¹ • _ =_; unfold r; module
 have hg: ‖E*A‖^2 ≤ r*B⁻¹:=by
    rw [show ‖E*A‖^2=‖star (E*A)*(E*A)‖ from (by rw [CStarRing.norm_star_mul_self, sq]),star_mul,hA.isSelfAdjoint,hE.isSelfAdjoint,←mul_assoc,mul_assoc A E E,hE.isIdempotentElem,hx,norm_smul,Real.norm_of_nonneg (by positivity)]; exact mul_le_of_le_one_right (by positivity) (hA.norm_le _)
 unfold wish; rw [norm_smul,mul_pow]; apply (mul_le_mul_of_nonneg_left hg (sq_nonneg ‖z⁻¹‖)).trans; rw [Real.norm_of_nonneg (inv_nonneg.mpr s.le)] -- tune
 apply le_trans _ (mul_le_mul_of_nonneg_left (inv_anti₀ f hp) (sq_nonneg z)); rw [←mul_assoc]; gcongr; unfold r; rw [inv_pow, ← mul_assoc, show (z^2)⁻¹*z^4=z^2 by field_simp]; exact mul_le_of_le_one_right (by positivity) (sub_le_self _ f.le)
end spin
end YM.CF.Lamour
#print axioms YM.CF.Lamour.wish_diag
#print axioms YM.CF.Lamour.pitch
#print axioms YM.CF.Lamour.lake_range

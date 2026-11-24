import YM.SU5.Registration.Rise.ClockBooking
/-! # Queue algebra and amplitude at long-booking. Compare the `cue` lemmas in
`Silk/Span/Flow` (not a dependency; insert their bounds here). -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5800
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.ClockBooking
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SatinVerification
section relay
variable {K:Calibration}{S:Finset Cover}{B:ℕ → Family K}{x:Family K}(h:BQueue S B x)
include h
lemma cueMono{T:Finset Cover}(u:S⊆T): BQueue T B x:= ⟨fun _=> (h.whereTo _).mono u,h.landing.mono u,h.bdd,h.saved⟩
lemma cueSum {Z:ℕ → Family K}{X:Family K}(u:BQueue S Z X): BQueue S (fun i=>B i+Z i) (x+X):=by
 obtain ⟨p,q,⟨C,v,t,g⟩,e⟩:=h; obtain ⟨j,k,⟨D,w,s,r⟩,F⟩:=u
 refine ⟨fun i=>(p i).add (j i), q.add k,⟨_,add_pos v w,pay_add t s,(g.and r).mono fun i ⟨u,v⟩=>pay_add u v⟩,fun a b=>?_⟩
 filter_upwards [e _ (half_pos b), F _ (half_pos b)] with i h u
 have hv:=pay_add h u; rw [add_halves] at hv; rw [show B i+Z i-(x+X)=(B i-x)+(Z i-X) from by abel]; exact hv
lemma cueSub {Z:ℕ → Family K}{X:Family K}(u:BQueue S Z X): BQueue S (fun i=>B i-Z i) (x-X):=by
 obtain ⟨p,q,⟨C,v,t,g⟩,e⟩:=h; obtain ⟨j,k,⟨D,w,s,r⟩,F⟩:=u
 refine ⟨fun i=>InTest.subOp (p i) (j i), InTest.subOp q k,⟨_,add_pos v w,pay_sub t s,(g.and r).mono fun i ⟨u,v⟩=>pay_sub u v⟩,fun a b=>?_⟩
 filter_upwards [e _ (half_pos b), F _ (half_pos b)] with i h u
 have hv:=pay_sub h u; rw [add_halves] at hv; rw [show B i-Z i-(x-X)=(B i-x)-(Z i-X) from by abel]; exact hv
lemma cue_scale (f:ℕ→ℂ)(v:ℂ)(u:Tendsto f atTop (𝓝 v)): BQueue S (fun i=> f i • B i) (v • x):=by
 obtain ⟨p,q,⟨C,g,t,k⟩,e⟩:=h; let D:= ‖v‖+1; have hd:‖v‖<D:=by linarith
 have hD:0<D:=lt_of_le_of_lt (norm_nonneg _) hd; let H:=D*C; have hB:= u.norm.eventually (ge_mem_nhds hd)
 refine ⟨fun i=>(p i).smul _, q.smul _,⟨H,mul_pos hD g,(fun i j=>(pay_scale t v i j).trans (mul_le_mul_of_nonneg_right hd.le g.le)), ?_⟩,fun b r=> ?_⟩
 · filter_upwards [hB,k] with i h v m j; exact (pay_scale v (f i) m j).trans (mul_le_mul_of_nonneg_right h g.le)
 let d:= b/(2*D); let l:= b/(2*C); have ht:Tendsto (fun i=> ‖f i - v‖) atTop (𝓝 0):=by simpa using (u.sub (tendsto_const_nhds (x:=v))).norm
 filter_upwards [hB,e _ (show 0 < d from div_pos r (by positivity)), ht.eventually (ge_mem_nhds (show 0<l from div_pos r (by positivity)))] with i h V z
 rw [show f i • B i-v • x=f i • (B i-x)+(f i-v) • x from by rw [smul_sub,sub_smul]; abel]
 intro m V0; apply (pay_add (pay_scale V _) (pay_scale t (f i-v)) m V0).trans; refine (add_le_add (mul_le_mul_of_nonneg_right h (by unfold d; positivity)) (mul_le_mul_of_nonneg_right z g.le)).trans_eq ?_; unfold d l; field_simp; try ring
end relay

variable {K:Calibration}{S':Finset Cover}
lemma keep_queue {Y:ℕ→Family K}{Z:Family K}(h:BQueue S' Y Z){φ:ℕ→ℕ}(v:Tendsto φ atTop atTop) : BQueue S' (Y∘φ) Z:=
 ⟨fun i=> h.whereTo _, h.landing,⟨_,h.bdd.choose_spec.1,h.bdd.choose_spec.2.1,v.eventually h.bdd.choose_spec.2.2⟩,fun i e=> v.eventually (h.saved i e)⟩

local notation "P" => K
variable (b:ℝ)(j:Axis)(w:ℤ)(f:Family K)
private lemma fantastic (n:ℕ): toward P j w ((b:ℂ) • f) n=(b:ℂ) • toward P j w f n:=by
 induction n with
 | zero=> rfl
 | succ n ih=>rw [toward_step, toward_step, ih, mirror_scale]; simp
lemma lace_real_bill (n:ℕ) : lace P j w ((b:ℂ) • f) 1 n = ((b:ℂ)^n) • lace P j w f 1 n:=by
 induction n with
 | zero=> rw [pin_zero,pin_zero,pow_zero,one_smul]
 | succ n ih=> rw [lacing,lacing, fantastic, ih, relocate, chime_scale,pow_succ, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,mul_comm (b:ℂ)]; rfl
lemma banner_real (v:ℤ)(n:ℕ) : banner j w v n ((b:ℂ) • f) = ((b:ℂ)^(4*n)) • banner j w v n f:= by
 have h : chambers j w v ((b:ℂ) • f) 1 n=((b:ℂ)^(2*n)) • chambers j w v f 1 n:=by
    unfold chambers; rw [lace_real_bill, mirror_scale,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,star_pow]; simp only [Complex.star_def,map_pow,Complex.conj_ofReal]; rw [←pow_add,←two_mul,relocate,chime_scale]; rfl
 rw [banner,h,mirror_scale,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul, star_pow]; simp only [Complex.star_def,Complex.conj_ofReal]; rw [←pow_add,show 2*n+2*n=4*n from by omega]; rfl
end YM.CF.Buffered.Afterglow.Tower.SlabMark.ClockBooking

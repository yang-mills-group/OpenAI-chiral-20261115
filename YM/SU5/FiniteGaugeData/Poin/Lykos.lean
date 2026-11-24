import YM.SU5.FiniteGaugeData.Poin.Cobble
/-! # Reducing heat from motion. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Set Function Metric OS OS.Semigroup Complex
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(Q:H.Op)(u v:ℝ≥0)(p:∀ t:ℝ,Commute Q (S.edge t))(d: Commute (saucer S) Q)(x:H)
local notation "R"=> saucer S
local notation "ψ"=>OS.Semigroup.duration
local notation "E"=> highlande S
local notation "A"=>R*Q
-- h p.He.R comm.UTC.Mink count.
lemma propY : parade S 0 x = I • (x-R x):=by unfold parade; simp [S.birth,show ContinuousLinearMap.id ℂ H.space=(1:H.Op) from rfl,smul_sub]
include p
lemma co_reg: Commute R Q:=by
 ext1 x; let y:=Q (R x); let f(t:ℝ):= R (S.edge t y); have he: f=(fun t=> S.edge t (R y)):=funext fun i=> DFunLike.congr_fun ((cupL S i).eq) y; let L:=(R*Q); have ht:f=(fun t=> L (S.edge t (R x))):=funext fun i=>congrArg (saucer S) (DFunLike.congr_fun (p i).eq.symm (R x))
 have hv:HasDerivAt f (L (parade S 0 x)) 0:= ht ▸ (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt _ (fanfare S x 0); have hh := hv.unique (show HasDerivAt f (parade S 0 y) 0 from he ▸ fanfare S y 0); rw [propY,propY,map_smul] at hh; have hm:=smul_right_injective H.space I_ne_zero hh; rw [map_sub] at hm; exact Eq.trans (sub_left_inj.mp hm) rfl -- tune sub_left_inj orientation; L(Rx) defeq R y
omit p
-- q derivative band identities both-side
lemma currents(z:ℂ)(p:z∈inside): saucer S*slug S z=(saucer S-1)* S.F z ∧ slug S z*R= S.F z*(R-1):=by
 have h:= dorsal S z p; have he:= jalousie S z p; unfold looper at h he; rw [mul_sub] at h; rw [sub_mul] at he
 constructor <;> (first| rw [sub_mul,one_mul] | rw [mul_sub,mul_one]); exact eq_sub_of_add_eq ((add_comm ..).trans (sub_eq_iff_eq_add.mp h).symm)
 exact eq_sub_of_add_eq ((add_comm ..).trans (sub_eq_iff_eq_add.mp he).symm)
include d
lemma dielectric (k:0<u): Commute (S.E u) Q:=by
 -- compare entire ∀α∈(0,u) lines heat product hol.SOT only endpoints.
 let L:= ψ u; let Λ:= {z:ℂ|0<z.re∧ z.re<(u:ℝ)}; let f(z:ℂ):= S.F (L-z)*Q*S.F z
 have hop:IsOpen Λ:= IsOpen.inter (isOpen_lt continuous_const continuous_re) (isOpen_lt continuous_re continuous_const)
 have hU:IsPreconnected Λ:= Convex.isPreconnected (Convex.inter (convex_halfSpace_gt reCLM.toLinearMap.isLinear _) (convex_halfSpace_lt reCLM.toLinearMap.isLinear _)) -- target defeq ∩
 have he(z:ℂ)(p:z∈ Λ): HasDerivAt f 0 z:=by
    have h:z∈ inside:= p.1; let y:=L-z; have he:y∈inside:=sub_pos.mpr p.2; let L':= S.F y; have hh : HasDerivAt (fun z=> S.F (L-z)) (-(slug S y)) z:= by
       simpa only [neg_smul,one_smul] using! ((S.localHeat y he).differentiableAt.hasDerivAt.scomp z (show HasDerivAt (fun z=>L-z) (-1) z from (by convert (hasDerivAt_id' z).const_sub L)))
    apply HasDerivAt.congr_deriv ((hh.mul_const Q).mul (S.localHeat z h|>.differentiableAt.hasDerivAt)); apply isochron S _ _; let F':= S.F
    rw [mul_zero]; let σ:=slug S; let E0:=S.F z; change R * ((-(σ y))*Q*E0 + L'*Q*σ z)=0
    have v: R * L'= L'*R:=(cupF S y he).eq
    rw [mul_add,← mul_assoc, ← mul_assoc R (-σ y), mul_neg, (currents S y he).1,← mul_assoc, ← mul_assoc R L',v,mul_assoc L' R Q, d.eq]; rw [show -( (R-1)*F' y) * Q * E0 = - (L'*Q*((R-1)*E0)) from ?_]; -- F' y syntax. right
    · rw [← (currents S z h).1]; noncomm_ring
    let J:= S.F z; have hp: (R-1)* F' y=F' y*(R-1):=by rw [sub_mul,mul_sub,v,one_mul,mul_one]
    have hk:(R-1)*Q=Q*(R-1):=by rw [sub_mul,mul_sub,d.eq,one_mul,mul_one]
    rw [hp,neg_mul,neg_mul,mul_assoc _ _ Q, hk]; simp only [mul_assoc]; rfl
 let z:ℂ:= L/2; have hz: z∈ Λ := by unfold z L Λ OS.Semigroup.duration; simp [k]
 have hf:= hop.eqOn_of_deriv_eq hU (f:=f) (g:=fun _=> f z) (fun i h=> (he i h).differentiableAt.differentiableWithinAt) (differentiableOn_const _) (fun i h=> Eq.trans ((he i h).deriv) (deriv_const .. |>.symm)) hz rfl
 ext1 x; let P(y:ℝ≥0):H:= S.E (u-y) (Q (S.E y x)); have hp:Continuous P:= by
    -- using duet
    have hc:= (duet S).comp ((Q.continuous.comp (S.continuousE x)).prodMk ((continuous_const (y:=u)).sub continuous_id)); exact hc
 have h(v:ℝ≥0)(s:v∈Set.Ioo 0 u): P v=f z x:= by
    let Z(v:ℝ≥0):= ψ v; have hh:f (Z v)=f z:=hf (show Z v∈Λ from s); rw [← hh]; unfold f P; rw [show L-Z v=Z (u-v) from ?_, (S.roots_heat (show 0< u-v from tsub_pos_of_lt s.2)), S.roots_heat s.1]; rfl
    unfold L Z OS.Semigroup.duration; rw [NNReal.coe_sub s.2.le]; push_cast; rfl
 -- use closure Ioo lemma? NNReal order no issues.Search.
 have hv: ∀ y∈Icc (0:ℝ≥0) u,P y=f z x:=by rw [← closure_Ioo k.ne]; intro y p; exact closure_minimal (t:={x'| P x'=f z x}) h (isClosed_eq hp continuous_const) p
 have ht := (hv 0 (left_mem_Icc.mpr k.le)).trans (hv u (right_mem_Icc.mpr k.le)).symm; unfold P at ht; rw [tsub_self,S.eZero,tsub_zero] at ht; exact ht
#print axioms dielectric
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

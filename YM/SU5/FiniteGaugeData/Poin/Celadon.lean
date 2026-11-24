import YM.SU5.FiniteGaugeData.Poin.Lykos
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Set Function Metric OS OS.Semigroup Complex
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(Q:H.Op)(u v:ℝ≥0)(T:OS.Semigroup H a)(p: S.edge=T.edge)(e: saucer S=saucer T)(x:H)
local notation "R"=> saucer S
local notation "ψ"=>OS.Semigroup.duration
local notation "E"=> highlande S
local notation "A"=>R*Q
include e
lemma derives_heatK (d:Commute (saucer S) Q)(k:0<u): S.E u*Q=Q*T.E u:=by
 -- compare entire ∀α∈(0,u) lines heat product hol.SOT only endpoints.
 let L:= ψ u; let Λ:= {z:ℂ|0<z.re∧ z.re<(u:ℝ)}; let f(z:ℂ):= S.F (L-z)*Q*T.F z
 have hop:IsOpen Λ:= IsOpen.inter (isOpen_lt continuous_const continuous_re) (isOpen_lt continuous_re continuous_const)
 have hU:IsPreconnected Λ:= Convex.isPreconnected (Convex.inter (convex_halfSpace_gt reCLM.toLinearMap.isLinear _) (convex_halfSpace_lt reCLM.toLinearMap.isLinear _)) -- target defeq ∩
 have he(z:ℂ)(p:z∈ Λ): HasDerivAt f 0 z:=by
    have h:z∈ inside:= p.1; let y:=L-z; have he:y∈inside:=sub_pos.mpr p.2; let L':= S.F y; have hh : HasDerivAt (fun z=> S.F (L-z)) (-(slug S y)) z:= by
       simpa only [neg_smul,one_smul] using! ((S.localHeat y he).differentiableAt.hasDerivAt.scomp z (show HasDerivAt (fun z=>L-z) (-1) z from (by convert (hasDerivAt_id' z).const_sub L)))
    apply HasDerivAt.congr_deriv ((hh.mul_const Q).mul (T.localHeat z h|>.differentiableAt.hasDerivAt)); apply isochron S _ _; let F':= S.F
    rw [mul_zero]; let σ:=slug S; let E0:=T.F z; change R * ((-(σ y))*Q*E0 + L'*Q*slug T z)=0
    have v: R * L'= L'*R:=(cupF S y he).eq
    rw [mul_add,← mul_assoc, ← mul_assoc R (-σ y), mul_neg, (currents S y he).1,← mul_assoc, ← mul_assoc R L',v,mul_assoc L' R Q, d.eq]; rw [show -( (R-1)*F' y) * Q * E0 = - (L'*Q*((R-1)*E0)) from ?_]; -- F' y syntax. right
    · rw [← (show R*slug T z=(R-1)* T.F z from (by rw [e]; exact (currents T z h).1))]; noncomm_ring
    let J:= S.F z; have hp: (R-1)* F' y=F' y*(R-1):=by rw [sub_mul,mul_sub,v,one_mul,mul_one]
    have hk:(R-1)*Q=Q*(R-1):=by rw [sub_mul,mul_sub,d.eq,one_mul,mul_one]
    rw [hp,neg_mul,neg_mul,mul_assoc _ _ Q, hk]; simp only [mul_assoc]; rfl
 let z:ℂ:= L/2; have hz: z∈ Λ := by unfold z L Λ OS.Semigroup.duration; simp [k]
 have hf:= hop.eqOn_of_deriv_eq hU (f:=f) (g:=fun _=> f z) (fun i h=> (he i h).differentiableAt.differentiableWithinAt) (differentiableOn_const _) (fun i h=> Eq.trans ((he i h).deriv) (deriv_const .. |>.symm)) hz rfl
 ext1 x; let P(y:ℝ≥0):H:= S.E (u-y) (Q (T.E y x)); have hp:Continuous P:= by
    -- using duet
    have hc:= (duet S).comp ((Q.continuous.comp (T.continuousE x)).prodMk ((continuous_const (y:=u)).sub continuous_id)); exact hc
 have h(v:ℝ≥0)(s:v∈Set.Ioo 0 u): P v=f z x:= by
    let Z(v:ℝ≥0):= ψ v; have hh:f (Z v)=f z:=hf (show Z v∈Λ from s); rw [← hh]; unfold f P; rw [show L-Z v=Z (u-v) from ?_, (S.roots_heat (show 0< u-v from tsub_pos_of_lt s.2)), T.roots_heat s.1]; rfl
    unfold L Z OS.Semigroup.duration; rw [NNReal.coe_sub s.2.le]; push_cast; rfl
 -- use closure Ioo lemma? NNReal order no issues.Search.
 have hv: ∀ y∈Icc (0:ℝ≥0) u,P y=f z x:=by rw [← closure_Ioo k.ne]; intro y p; exact closure_minimal (t:={x'| P x'=f z x}) h (isClosed_eq hp continuous_const) p
 have ht := (hv 0 (left_mem_Icc.mpr k.le)).trans (hv u (right_mem_Icc.mpr k.le)).symm; unfold P at ht; rw [tsub_self,S.eZero,T.eZero,tsub_zero] at ht; exact ht
#print axioms derives_heatK
omit e
include p
lemma derives_saucer : saucer S=saucer T:=by
 ext1 x; let L:=saucer T; let f(t:ℝ):=R (T.edge t (L x)); have he:f=(fun t=>S.edge t (R (L x))):=funext fun t=>by unfold f; rw [←p]; exact DFunLike.congr_fun (cupL S t).eq _
 have hv: HasDerivAt f (parade S 0 (L x)) 0:= he ▸ fanfare S (L x) 0; have hh: HasDerivAt f (R (parade T 0 x)) 0:= ((saucer S).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt _ (fanfare T x 0); have hp:=hv.unique hh; rw [propY,propY,map_smul] at hp; have hv:= smul_right_injective H.space I_ne_zero hp; rw [map_sub] at hv; exact sub_left_inj.mp hv.symm
lemma derives_clock : S.E=T.E:=funext fun v=>by
 rcases eq_zero_or_pos v with rfl|x; · rw [S.eZero,T.eZero]
 simpa using derives_heatK S 1 v T (derives_saucer S T p) ( Commute.one_right _ ) x
omit p
lemma derive_full (p:M S=M T): S=T:=by
 have he:S.E=T.E:= derives_clock S T (funext fun i=> (timeslot S i).symm.trans ((congrFun p _).trans (timeslot T i)))
 have ht:S.U=T.U:=funext fun i=> (laneslot S i).symm.trans ((congrFun p _).trans (laneslot T i))
 cases S; cases T; congr
#print axioms derive_full
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

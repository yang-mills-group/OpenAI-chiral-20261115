import YM.CF.Rill.Uni
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Jet Atala
variable {E L H:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup L][NormedSpace ℝ L][NormedAddCommGroup H][NormedSpace ℝ H]
lemma Shake.dil(p:E→L[ℝ]L)(U:L→ H)(h:Shake U 0 e l)(hp:‖p‖≤ b)(hg:1≤b): Shake (U ∘ p) 0 (e*b^l) l:=by
 have he:Shake U (p 0) e l:=(map_zero p).symm ▸ h; refine ⟨mul_nonneg h.price (by positivity),he.smooth.comp _ p.contDiff.contDiffAt,fun i g v=>?_⟩; rw [Push.Uniform.iter_lin_at (he.smooth.of_le (Nat.cast_le.mpr v))]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; simp only [prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul (he.bill i g v) ((pow_le_pow_left₀ (norm_nonneg _) hp i).trans (pow_le_pow_right₀ hg v)) (by positivity) he.price
lemma funding(n:ℕ):∃ C:ℝ,1≤ C∧ ∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](F:E→ SU.group.Color)(x:E)(u:ℝ),Allows n F x u→u≤1 → Tender (SU.group.lieExp ∘ F) x (C*u) n:=by
 let X:= SU.group.mat ∘ SU.group.lieExp; obtain ⟨H,h,U⟩:=Jet.payment_for n (isCompact_closedBall (0:SU.group.Color) 1) X (fun _ _=>SU.group.exp_jet.contDiffAt.of_le le_top); refine ⟨max 1 (Shake.quota n*H),le_max_left ..,fun F x u p t=>?_⟩; exact (((Shake.pick p).thorn (Shake.pick (U _ (mem_closedBall_zero_iff.mpr (p.value.trans t)))) t)).bag (by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right ..) p.nonneg)
lemma hullD(n l:ℕ)(Q:Patch)(q:Chi)(a b:ℝ)(ha:0<a)(hb:0<b):∃ C:ℝ,1 ≤ C∧∀ᶠ x in atTop,∀ {c f:Side}(S:StepData c f)(T:Tube G S)(M:Monk G S),S.patch=Q→∀ d:ℝ, MossX n l x M.key M.park T M.V M.k a d (fiery G x S.patch.L) q → ‖M.z‖ ≤ b*Scales.p G S.patch.L x → ∀ β∈Set.Icc (y G S.patch.L x/2) (2*y G S.patch.L x),
 (∀ i,Tender (fun u=>Vmove x M.V u i) 0 (C*fiery G x Q.L) n)∧∀ i:Bond f,Tender (fun u:Directions G c=>(M.atop u x).sent x T q d l β i) 0 (C*fiery G x Q.L) n:=by
 obtain ⟨e,K,he,hK,h,-⟩:= sailors n q (div_pos (first_pos G) (by norm_num : (3:ℝ)>0)) (show 2*(firstRadius G/3)< firstRadius G by have hh:= first_pos G; linarith) -- tune
 let W:=Push.Uniform.shade G; have hp:0<W:=Push.Uniform.shade_pos _; obtain ⟨C,hC,H⟩:= funding n; let z:= a+2^n*a*(2*b); have hz:0<z:=by unfold z; positivity
 let L:= max 1 (W*z); let D:= 2+L; have hh:0<L:=zero_lt_one.trans_le (le_max_left ..); have hy:1 ≤ D:=by unfold D; linarith
 let C':= C*D; let B:=K*C'; have hw:1≤C':= one_le_mul_of_one_le_of_one_le hC hy; have hy':1 ≤ B:= one_le_mul_of_one_le_of_one_le hK hw; refine ⟨K*B,one_le_mul_of_one_le_of_one_le hK hy',?_⟩
 filter_upwards [expM Q (hp:=div_pos he (b:=B) (zero_lt_one.trans_le hy')),expM Q (hp:=one_div_pos.mpr (zero_lt_one.trans_le hy)),monitors G Q.L, (year G Q.L).eventually (eventually_gt_atTop 0)] with x hs hd hk hQ c f S T M hu d t v β p; let R:= fiery G x Q.L
 rw [hu] at t v p; have hr:0<R:=by unfold R; linarith only [hk.1,hk.2.2] -- monitors
 have hD:D*R≤1:=(mul_comm D R).le.trans ((le_div_iff₀ (zero_lt_one.trans_le hy)).mp hd); have hb': B*R≤e:=(mul_comm B R).le.trans ((le_div_iff₀ (zero_lt_one.trans_le hy')).mp hs); have hv: C'*R≤B*R:=by unfold B; gcongr; exact le_mul_of_one_le_left (zero_le_one.trans hw) hK
 have hf(i:Bond c): Tender (fun u=>Vmove x M.V u i) 0 (B*R) n:=by
    let P(u:Directions G c):=temp x • u i; have hp: ‖ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond c=>SU.group.Color) i‖≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i'=> (norm_le_pi_norm i' i).trans_eq (one_mul _).symm
    have he:= (allows_linear (x:=0) (n:=n) hp (by simp)).smul (temp x); have hh : Allows n P 0 (D*R):= he.mono (by rw [abs_of_nonneg hk.1.le,mul_one]; exact hk.2.2.trans (mul_le_mul_of_nonneg_right (show 2≤ D from by unfold D; linarith only [hh]) hr.le)); have ht: Tender (SU.group.lieExp ∘ P) 0 (C'*R) n:= (mul_assoc C D R).symm ▸ H _ _ _ hh hD
    rw [show B*R= K*(C'*R) from mul_assoc ..]; exact h.duty (hv.trans hb') ht ((Shake.holds (SU.group.mat (M.V i))).bag ht.price)
 have hL:B*R≤ K*B*R:=mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (zero_le_one.trans hy') hK) hr.le; refine ⟨fun i=> (hf i).bag hL,fun i=>?_⟩
 by_cases g:i∈M.park.trunks
 · exact ((Shake.holds (SU.group.mat 1)).bag ((mul_nonneg (zero_le_one.trans hy') hr.le).trans hL)).same (Eventually.of_forall fun u=>congrArg SU.group.mat (tipS (M:=M.atop u x) _ g).symm)
 let j:M.park.Free:=⟨i,g⟩; by_cases k:chill M.key x M.park j
 · let I:Frozen M.key x M.park:=⟨j,k⟩; exact ((Shake.holds (SU.group.mat (M.U i))).bag ((mul_nonneg (zero_le_one.trans hy') hr.le).trans hL)).same (Eventually.of_forall fun u=>congrArg SU.group.mat (held_physical x M.key M.park (M.atop u x).V (M.bush x) ((M.atop u x).fuel x T q d l β) I).symm)
 let I:Active M.key x M.park:=⟨j,k⟩; let Z(v:Directions G c) := (M.atop v x).rich x T q d l β I -- tune I.v
 let Y:= b*Scales.p G Q.L x; have hY:0<Y:=mul_pos hb (Scales.pos ..); have hZ:=ready_heat (β:=β) (M.bush x) (M.bell x) _ t Y ((pi_norm_le_iff_of_nonneg hY.le).mpr (fun i=> (norm_le_pi_norm M.z i.val.val).trans v)) ha.le; have hβ:0<β:=(half_pos hQ).trans_le p.1
 have hu: a*R+ |coupling β| * (2^n*a*Y) ≤ z*R:=by
    rw [abs_of_pos (coupling_pos hβ)]; apply le_trans (add_le_add_right (mul_le_mul_of_nonneg_right (compare_v G Q.L x p hQ).1 (show 0≤ 2^n*a*Y from by positivity)) _) -- tune
    unfold R z Y; rw [Scales.fi]; apply le_of_eq; ring
 have H':Tender (SU.group.lieExp ∘ Z) 0 (C'*R) n:= by
    have hg:Allows n Z 0 (D*R):= (shelJ hZ.2 I).mono (le_trans (mul_le_mul_of_nonneg_left hu hp.le) (by change W*_≤_; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right ?_ hr.le; unfold D; exact (le_max_right ..).trans (show L≤ 2+L by linarith))) -- tune
    rw [show C'*R=C*(D*R) from mul_assoc ..]; exact H _ _ _ hg hD
 let V(u:Directions G c):= replica S.ratio (Vmove x M.V u) i; have he:Tender V 0 (B*R) n:=by unfold V Precision.replica; split; exact (Shake.holds (SU.group.mat 1)).bag (mul_nonneg (zero_le_one.trans hy') hr.le); exact hf _
 rw [mul_assoc K]; exact (h.duty hb' (H'.bag hv) he).same (Eventually.of_forall fun i'=>congrArg SU.group.mat (clear_physical x M.key M.park _ _ ((M.atop i' x).fuel x T q d l β) I).symm) -- tune
end YM.CF.Rill

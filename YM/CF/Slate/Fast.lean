import YM.CF.Slate.Vroom
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Slate
open Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
namespace Far
lemma score (K:Teller SU.group)(P:Patch)(p:P.Branches K.bind G)(n l j:ℕ)(hp:3  ≤  n)(hv:l  ≤ 18)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+3))(V: Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+2))(D:ℝ)(hD:0  ≤  D):
 ∃ A e v:ℝ,0<A∧0<e∧0<v ∧∀ᶠ x in atTop, let s:=v*(lamp x+fiery G x P.L);0<lamp x∧ temp x ≤ s ∧s ≤  1 ∧ ∀ β∈Set.Icc (y G P.L x/2) (2*y G P.L x), |coupling β| *  Jet.composeCost n ((D*Scales.p G P.L x)*A) (1/2)  ≤  s/2 ∧∀{c f:Side}(S:StepData c f)(T: Tube G S), Cert P K S T x→∀(M:Monk G S)(q:Chi)(d:ℝ)(p:Site c),  (j+j+101)*radiusB x  ≤  c.val → sizedP G P K S T M.park→ M.key.flags=RG.flags (temp x) M.V→p∉ M.key.dome ((j+2)*radiusB x)→‖M.z‖  ≤  D*Scales.p G P.L x→∃ g R, Lamp T s x M p g R (j+1) n∧ (∀ y:Mast G c,‖y‖<1→Fire T x M.park M.k l s n A y) ∧∀ (i:Dill S)(u:Signed), separation p (orientZ S u i)+(l+74)*radiusB x  ≤ (j+1)*radiusB x → Allows n (fun v=> Slate.payer T x (M.atop v x) q d l β u i) 0 (e*s^3) :=by
 obtain ⟨A,E,hA,hE,H⟩:= persp K P p n l (by omega) hv W V; obtain ⟨C,hC,Q⟩:= hustle G j n (by omega); obtain ⟨m,y',C',hm,hy,hc,H'⟩:= bear K P n p
 obtain ⟨J,ε,hJ,hε,J'⟩:= tinPaid P K p n l hp V; let R:=composeCost n (D*A) (1/2); let v:= max 1 (max C (2*8*R)); have he:1 ≤  v:=le_max_left ..; have hr:0<v:=zero_lt_one.trans_le he; let t:=min (min 1 E) ε; have ht:0<t:=lt_min (lt_min zero_lt_one hE) hε; have he': Tendsto (fun x=> v*(lamp x+fiery G x P.L)) atTop (𝓝 0):=by
    have hx: Tendsto (fun x=>fiery G x P.L) atTop (𝓝 0):=by
       apply (tally_g G P.L 0 1).congr; intro x; rw [fi]; ring
    simpa only [add_zero,mul_zero] using (lamp_s.add hx).const_mul v
 let e:=composeCost n (J+J) (1/2); refine ⟨A,e,v,hA,by unfold e Jet.composeCost; positivity,hr,?_⟩
 filter_upwards [H,Q,H',J', PatchReads.reserve K P,he'.eventually (ge_mem_nhds ht), Work.E01.radiusB_tendsto.eventually_ge_atTop 1000,(year G P.L).eventually (eventually_gt_atTop (0:ℝ))] with x H Q H' Jp hx hb hv' hc'; intro s
 have ht':s ≤  1:=hb.trans ((min_le_left ..).trans (min_le_left ..)); have hz:=H.1; have hu:=he; let θ:= fiery G x P.L; let Y:=Scales.p G P.L x; have hy':=Scales.pos G P.L x; have ht':=ht'; have hθ:0 ≤  θ:=temp_nonneg _; have hl: lamp x  ≤  s := (le_add_of_nonneg_right hθ).trans (le_mul_of_one_le_left (add_nonneg hz.le hθ) he); obtain ⟨p₁,p₂,p₃⟩:=Q; have ht'': temp x  ≤ s:=H.2.1.trans hl; refine ⟨hz,ht'',ht',fun β u=>?_⟩
 have hp' : 0<β:=(half_pos hc').trans_le u.1; have hX:0  ≤  R:=by unfold R Jet.composeCost; positivity
 have hf:= compare_v G P.L x u hc'; have ht:0<coupling β:=coupling_pos hp'
 have hyB:|coupling β| *composeCost n (D*Scales.p G P.L x * A) (1/2)  ≤  s/2:=by
    rw [show composeCost n (D*Y*A) (1/2)=Y*R from by unfold R composeCost; ring] -- Y unification
    have hU: (2*8*R)  ≤  v:=(le_max_right ..).trans (le_max_right ..); rw [abs_of_pos ht,← mul_assoc]; refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf.1 hy'.le) hX).trans ?_; unfold s; change _  ≤  v*(lamp x+θ)/2; unfold θ; rw [fi]; have ht:=Scales.gauge G P.L hc'; change 0< Y at hy'; change _* Y*_  ≤  v*(lamp x+_* Y)/2; nlinarith only [mul_le_mul_of_nonneg_right hU (mul_nonneg (mul_nonneg ht.le hy'.le) zero_le_one),mul_nonneg hr.le hz.le,mul_nonneg hX (mul_nonneg ht.le hy'.le)] -- tune
 refine ⟨hyB,fun S T Hx M q d p v' t u' p₀ pV=>?_⟩
 obtain ⟨g,z,hZ,hQ⟩:= p₃ S M.V M.key p p₀ u' v'
 let W: Directions G _ → Mast G _:= fun i=> s⁻¹ • (tideF C x • g i); have hW: Lamp T s x M p z W (j+1) n:=by
    have hL:tideF C x ≤  s:=by
       have h: C  ≤  v := (le_max_left ..).trans (le_max_right ..)
       have ht0:0 ≤ temp x:=temp_nonneg _
       have hM:tideF C x  ≤  v* lamp x:=mul_le_mul h (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (Nat.one_le_cast.mpr (le_trans (by omega) hv')) (by omega : 5  ≤  9)) ht0) (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) ht0) hr.le
       exact hM.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hθ) hr.le)
    refine ⟨(((hZ.2.smul (tideF C x)).smul s⁻¹).mono ?_),?_ ,p₀⟩ -- defeq j+1+1
    · rw [abs_of_pos (inv_pos.mpr (hz.trans_le hl)),abs_of_pos p₁,inv_mul_le_iff₀ (hz.trans_le hl)]; exact mul_le_mul_of_nonneg_right hL (by norm_num)
    filter_upwards [hQ] with i hp; unfold satU W; rw [smul_inv_smul₀ (hz.trans_le hl).ne']; exact hp
 have hh:=H.2.2.2 _ _ M.park Hx t M.k s hl (hb.trans ((min_le_left ..).trans (min_le_right ..))); refine ⟨z,W,hW,hh,fun i v p=>?_⟩
 have hm0:0 ≤ temp x:=temp_nonneg x; have hs: temp x ^(l+1) ≤  s:=(pow_le_of_le_one hm0 (ht''.trans ht') (by omega)).trans ht''
 have he :=ink_e (g:=z) (q:=q) (d:=d) hp (hz.trans_le hl) ht' hJ.le (hh _ (hW.stage.value.trans_lt (by norm_num))) hW.stage pV hyB v i ((Jp S T M.park Hx t M.k v i).mono (mul_le_mul_of_nonneg_left hs hJ.le) le_rfl (hb.trans (min_le_right ..)))
 apply (he.germ (wick Hx.funds.1 (H' _ _ Hx _ _ _ u' _) hm hW (hx _ _ Hx.got Hx.size Hx.funds.1) hv' hh i v p).symm).mono; exact le_of_eq (by unfold e Jet.composeCost; ring)
end Far
end YM.CF.Slate

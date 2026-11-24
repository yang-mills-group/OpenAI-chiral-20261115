import YM.CF.Arena.Room
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Push.Uniform (bolt)
variable {K:Teller G}
lemma tall (K:Teller G)(P:Patch)(q:Chi)(l n:ℕ)(h:4 ≤ l)(hv:l≤18)(hp:5 ≤ n)(p:P.Branches K.bind G)(T: ∀ i≤ n+3, Push.Uniform.Before G K.top.width K.top.paths K.j K.bind i): ∃ e D C:ℝ,0<e∧e≤ 1∧0<D∧0<C∧∀ᶠ x in atTop,∀{c f:Side}(S:StepData c f)(U:Tube G S), Cert P K S U x→∀ V:Tab S,sizedP G P K S U V.1→(∀ z,Critical V.1 U.high U.up z→ ClassicalMatch V.1 U.high U.low U.up U.down z)→∀ d:ℝ, let W:=fame U V q x d l;
 (∀ i,Urge (W i) i 2 2 (horn x l) n e C (D*temp x^(l+2-4))) ∧ ∀ k:ℕ,2 ≤ k→k ≤4→ Prox W k (D*temp x^(l+2-4)):=by
 obtain ⟨e,D,M,he,hr,hM,hD,H⟩:=caseA K P q 0 l n hv p (by omega) (T _ (by omega)) (T _ (by omega)); have hx:=fun k:Fin 4=> Hors.pearlier K P p l k.val (by omega) (by omega) (by omega) (T _ (by omega))
 obtain ⟨C,E,hC,hE,H'⟩:= persp K P p n l (by omega) hv (T _ (by omega)) (T _ (by omega)); let t:= about P.L 0; let Z:=max 2 (D*t); let K':=M*(t+1)
 refine ⟨e,Z,K',he,hr,lt_of_lt_of_le (by norm_num: (0:ℝ)<2) (le_max_left ..), (by unfold K'; positivity),?_⟩
 filter_upwards [H,H',eventually_all.mpr hx,(show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).eventually (ge_mem_nhds zero_lt_one)] with x hh hh' hy hz c f S U hu V hV Hx d W
 have ha(i:Site c): Urge (W i) i 2 2 (horn x l) n e K' (Z*temp x^(l+2-4)):=by
    have ht: (about S.patch.L 0)=t:=by rw [hu.got]
    have hp: temp x ^(l+1) ≤ temp x^(l+2-4):= pow_le_pow_of_le_one (temp_nonneg _) hz (by omega)
    let a':=(t:ℝ); have he:a'*M ≤ K':=by unfold a' K'; linarith
    have hh(j u):Urge (bale U V q x d l u j) (herald S u j) 2 2 (horn x l) n e M (D*temp x^(l+1)):=by obtain ⟨p,hQ,h⟩:= hh S U V hu hV j u d; exact ⟨p,hQ,fun v x t=>by rwa [le_antisymm t x]⟩
    have hU:0≤ D*temp x^(l+1):= mul_nonneg hD.le (pow_nonneg (temp_nonneg _) _); refine Urge.under (fame_p hh (by assumption) (by omega) (by omega) hM.le hU) ?_ ?_ le_rfl
    · rw [ht]; exact he
    rw [ht]; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hD.le) (Nat.cast_nonneg _)).trans ?_; rw [←mul_assoc,mul_comm (_:ℝ) D]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg (temp_nonneg _) _) -- ℝ implicit
 refine ⟨ha,fun k hv' hv'' i s=> ?_⟩
 let L:=chair U V.1; have ht : satX (∑ j,W j)=ᶠ[𝓝 0] Complex.ofRealCLM ∘ Hors.hut U x V.1 V.2 l ∘ chair U V.1:=by
    let X:= E⁻¹ • L; filter_upwards [X.continuous.continuousAt.eventually (isOpen_ball.mem_nhds (show X 0∈ ball (0:Mast G c) 1 by simp))] with w hi; let v:=X w; have hp: E • v=L w:=smul_inv_smul₀ hE.ne' _; have he := hut_v (q:=q) U V x d v C E hu.funds.1 l n (hh'.2.2.2 S U V.1 hu hV V.2 E hh'.2.2.1.le le_rfl v (mem_ball_zero_iff.mp hi)); dsimp only [bunk] at he; rw [hp, show facadeX _ _= _ from chap U V.1 w] at he; change (∑ j,W j) (represent w)= _; rw [Finset.sum_apply]; exact he
 have hP(v:Fin k→ Push.Uniform.Primary c G): ContDiffAt ℝ (k:ℕ∞ω) (Hors.hut U x V.1 V.2 l) 0 ∧ |Push.Uniform.entry (Hors.hut U x V.1 V.2 l) 0 v| ≤ Z*temp x^(l+2-4):=by
    obtain ⟨k,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega); obtain ⟨hp,h⟩:= hy ⟨k,by omega⟩ S U V.1 hu hV Hx V.2 v; exact ⟨hp,h.trans (mul_le_mul (le_max_left ..) (pow_le_pow_of_le_one (temp_nonneg _) hz (by dsimp only; omega)) (pow_nonneg (temp_nonneg _) _) ((by norm_num:(0:ℝ)≤ 2).trans (le_max_left ..)))⟩
 exact mat_sum U l k V ht (fun i=> (((ha i).1.ledger 0 (by simpa using he)).smooth.of_le (by exact_mod_cast hv''.trans (show 4 ≤ n by omega)))) (hP (fun i'=> (i i',s i'))).1 (fun j=>(hP j).2) i s
end YM.CF.Arena

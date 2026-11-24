import SatinThinNeutron
import SatinThinBank
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "E" r:max=> P.singleState 3 r x
local notation "Ω"=> P.colorZero 3 ξ
local notation "Γ"=>P.cartage 3 ξ
local notation "Η"=>P.seasons 3 ξ
local notation "κ"=>P.wealth 3 ξ
local notation "Πγ"=>P.enter 3 ξ
local notation "ω"=> P.heaven 3 ξ
local notation "B"=> P.basePlay x f r
local notation "K" f:max r:max=> P.megaK f r
local notation "W'" => P.tallWorth r
local notation "q!" i:max s:max=> P.runP f r i s
local notation "p!" i:max s:max=> P.meshPose r (q! i s)
local notation "O"=> P.charmF
local notation "oQ"=> opposeQ 3
local notation "oR"=> opposeR 3
open Regis.Circuit SatinJets
local notation "r!" f:max r:max=> ((P.rewardK f r):ℝ)
local notation "Cσ"=> Yoke.canonWeight
local notation "H!" i:max b:max=> P.strollQ x f r i b
local notation "Hu" i:max b:max=> P.strollV x f r i b
/-! # Purchase & projection simultaneously on exactly elected R-m&parting. 
-/
local notation "Φ"=> P.Spectrum0 3
local notation "χ"=> P.pillars 3
local notation "cwd" f:max=> slotFee P.par f

private lemma coresL(f:ℕ→ Φ→ℝ)(h:∀ i,Continuous (f i))(v:∀ i,0≤f i)(p:∀ i,(∫ x,f i x∂χ)≤3/4) {F:Φ→ Prop} (u:∀ᵐ x∂χ,F x): ∃ x: P.Spectrum0 3, F x∧ ∃ᶠ i in atTop, f i x<1:=by
 by_contra! q
 let Wb(i:ℕ):Φ→ℝ:=fun x=> min (f i x) 1; have he(i):Continuous (Wb i):=(h i).min continuous_const
 have hs(i): 0 ≤ Wb i:= fun y=> le_min (v i y) zero_le_one
 have H' (j:Φ→ℝ)(t:Continuous j):Integrable j χ:= t.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have hp(i:ℕ): (∫ x, Wb i x∂χ)≤ 3/4:= (integral_mono (H' _ (he i)) (H' _ (h i)) (fun y=>min_le_left ..)).trans (p i)
 have ht: Tendsto (fun i:ℕ=>∫ x,Wb i x∂χ) atTop (𝓝 (∫ (_:Φ),(1:ℝ)∂χ)):=by
    refine tendsto_integral_of_dominated_convergence (fun (_:Φ)=> (1:ℝ)) (fun i=> (H' _ (he i)).1) (integrable_const _) (fun i=> Eventually.of_forall (fun x=> (Real.norm_of_nonneg (show 0≤ Wb i x from hs i x)).trans_le (min_le_right ..))) (u.mono ?_)
    intro z vz; refine tendsto_const_nhds.congr' ?_; filter_upwards [q z vz] with i v; exact (min_eq_right v).symm -- check push_neg
 rw [integral_const,probReal_univ,one_smul] at ht; linarith only [le_of_tendsto ht (Eventually.of_forall hp)]
private lemma lensAm(A:ℝ) : (lensValue A)^2=16* Real.exp (16*A+1):= by
 have hp: ((16*A+1)/2)+((16*A+1)/2)=16*A+1:=by ring
 unfold lensValue; rw [mul_pow,sq (Real.exp _),← Real.exp_add,hp]; norm_num
lemma heartfelt_q (y:P.Vox j v): (∫ x:P.Spectrum0 3,‖P.stateVox j (P.advocate 3 x j) v y‖^2∂(P.pillars 3))=‖P.piece j v y‖^2:=by
 let S:=P.voxTest j v y; let T:=P.reflectTest j S*S; let U:= P.reading j v T; apply Complex.ofReal_injective
 refine ((integral_ofReal (𝕜:=ℂ) («μ»:=P.pillars 3) (f:=fun x=>‖P.stateVox j (P.advocate 3 x j) v y‖^2)).symm.trans ?_); change (∫ x:P.Spectrum0 3, ((‖P.stateVox j (P.advocate 3 x j) v y‖^2:ℝ):ℂ) ∂(P.pillars 3))=_; rw [Complex.ofReal_pow]; rw [← show inner ℂ (P.piece j v y) (P.piece j v y)=((↑‖P.piece j v y‖):ℂ)^2 from inner_self_eq_norm_sq_to_K _, P.seed_pairing]
 have he(x:P.Spectrum0 j): ((‖P.stateVox j x v y‖^2:ℝ):ℂ)= P.chi j x U:=by rw [Complex.ofReal_pow,← show inner ℂ (P.stateVox j x v y) (P.stateVox j x v y)=((↑‖P.stateVox j x v y‖):ℂ)^2 from inner_self_eq_norm_sq_to_K _]; exact P.gram_at j x v y y
 simp_rw [he]; exact (P.recovery_all 3 j U).trans (P.occupied j v T)
-- `Batch`: arbitrary request paid.
lemma officeCost (A:ℝ)(s:ℕ) : 3*Yoke.owedF P.par s A 2 ≤ (lensValue A* cwd s)^2 /4:=by
 unfold Yoke.owedF; rw [mul_pow,lensAm]; norm_num only [Nat.cast_ofNat]; rw [show 8*A*2+1=16*A+1 from by ring]; nlinarith only [Real.exp_pos (16*A+1), sq_nonneg (cwd s)] -- multiplication nonneg supplied by nlinarith?
local notation "Hub"=> ℕ× ℕ
structure Pedal (P:Spine)(f:ℕ) where
 axis:Axis
 s:Hub
 center:Cover
 bill:P.repeatBill (twiceT center axis) s.1
 grows:f ≤ s.1
 granted: Plans axis center s.1 P
 depth:s.1 < s.2
 book:0<slotFee P.par s.1
variable {A C:ℝ}(F0:Pedal P f)(v:ℕ)(a: Hub→ℝ)
local notation "ρ"=> F0.s
local notation "μ!"=> P.pillars 3
local notation "a!"=> a (F0.s)
local notation "j!"=> F0.axis
local notation "Hq" u:max=> P.cameo F0.axis F0.center (a (F0.s)) F0.depth.le u F0.granted
noncomputable abbrev lensForm (A:ℝ)(f:ℕ):= lensValue A*slotFee P.par f
noncomputable abbrev reachF (w:F0.s.2 ≤ v):= ‖P.stateVox F0.axis (P.advocate 3 x (F0.axis)) v (Hq w)‖^2
noncomputable def reachP (A:ℝ) :ℝ:= if p:(F0.s).2≤v then (P.reachF x F0 v a p)/(P.lensForm A F0.s.1)^2 else 0
-- cost at advance root
lemma reach_cont : Continuous (fun x:P.Spectrum0 3=> P.reachP x F0 v a A):=by
 by_cases t:F0.s.2≤v; · have he:= P.state_cont_cost (F0.axis) (Hq t); simp_rw [reachP,dif_pos t]; exact (he.comp (P.otherSpectrum 3 (F0.axis)).continuous).div_const _
 simp_rw [reachP,dif_neg t]; exact continuous_const
lemma reach_zero (A:ℝ) : 0 ≤ P.reachP x F0 v a A:=by
 unfold reachP; split; · exact div_nonneg (sq_nonneg _) (sq_nonneg _)
 rfl -- ≤refl ?
lemma reach_window {c:ℕ→Hub→ℝ}{l:ℕ→ℕ}(b:Workforce A C f v P c a l) (G₀:P.NightCop): (∫ x:P.Spectrum0 3,P.reachP x F0 v a A∂ μ!)≤ 1/4:=by
 unfold reachP; by_cases e : (F0.s).2 ≤ v; swap; · simp only [e,not_false_eq_true,dif_neg,integral_zero]; norm_num
 simp only [dif_pos e]; rw [integral_div]; let p:= (b.plans (F0.s) ⟨F0.grows, F0.depth,e⟩); let d:= P.lensForm A F0.s.1; have hx:0<d:=mul_pos (lensBasis A) F0.book
 apply (div_le_iff₀ (pow_pos hx 2)).2; unfold reachF; rw [P.heartfelt_q,P.into_vivid]; refine ((P.vision F0.axis F0.center p F0.granted F0.bill G₀).trans (P.officeCost A _))|>.trans_eq ?_; unfold d lensForm; ring
-- price at many simultaneous calls in one x
noncomputable abbrev navy (i:ℕ):ℝ:= 2^(i+1)
private lemma navy_pos (i:ℕ):1 ≤ navy i:= one_le_pow₀ (by norm_num) 
lemma charge_p (A:ℝ)(u:F0.s.2 ≤ v)(i:ℕ)(h:P.reachP x F0 v a A ≤ navy i): ‖P.stateVox F0.axis (P.advocate 3 x F0.axis) v (Hq u)‖^2≤ (navy i* P.lensForm A F0.s.1)^2:= by
 unfold reachP at h; rw [dif_pos u] at h; have he:0< P.lensForm A F0.s.1:= mul_pos (lensBasis _) F0.book; rw [mul_pow]; exact ((div_le_iff₀ (pow_pos he 2)).1 h).trans (mul_le_mul_of_nonneg_right (by nlinarith only [navy_pos i]) (sq_nonneg _)) -- z^2-z from z≥1
lemma navy_sum(i:ℕ): ∑ j∈ range i,1/navy j ≤ 1:=by
 suffices he: ∑ j∈ range i,1/navy j=1-(2^i)⁻¹ by rw [he]; exact sub_le_self _ (by positivity)
 induction i with| zero=> simp| succ i ih=> rw [sum_range_succ,ih]; unfold navy; rw [pow_succ (2:ℝ) i]; field_simp [pow_succ]; ring
-- allocate unit-committee. Charge accumulator ≤3/4. F and G analog
private lemma ctRent(T:Φ→ℝ)(t:Continuous T):Integrable T μ!:= t.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma budgetFor (g h:ℕ→ Φ→ℝ)(u:ℕ→ℕ→Φ→ℝ)(t: ∀ i:ℕ,Continuous (g i))(t1:∀ i:ℕ,Continuous (h i))(t2:∀ i s, Continuous (u i s))(q:∀ i x,0≤g i x)(q1:∀ i x,0≤h i x)(q2:∀ i s x,0≤u i s x) (e:∀ i,(∫ x,g i x ∂μ!)≤1/4) (e1:∀ i,(∫ x,h i x ∂μ!)≤1/4) (e2:∀ i s,(∫ x,u i s x ∂μ!)≤1/4){D:P.Spectrum0 3→Prop}(z:∀ᵐ x∂μ!, D x): ∃ x:P.Spectrum0 3,D x∧∃ᶠ i in atTop, g i x≤1∧h i x≤1∧∀ n, n < i→ u i n x≤ navy n:=by
 let a(i s:ℕ)(x:Φ):= (u i s x)/navy s; let b(i:ℕ)(x:Φ):= ∑ s∈range i,a i s x; let c(i:ℕ)(x:Φ):= g i x+ h i x+b i x; have he(i s):Continuous (a i s):=(t2 i s).div_const _; have hv(i s x):0≤ a i s x:=div_nonneg (q2 i s x) (zero_le_one.trans (navy_pos _)); have hy(i):Continuous (b i):=continuous_finsetSum _ fun j _=> he i _; have hx(i x):0 ≤ b i x:=sum_nonneg fun _ _=> hv i _ x; have H0(i): (∫ x:P.Spectrum0 3, b i x ∂μ!) ≤ 1/4:=by
    unfold b; rw [integral_finsetSum _ (fun _ _=> P.ctRent _ (he i _))]; unfold a; simp_rw [integral_div]; let s:ℝ:=1/4; have hs:(0:ℝ) ≤ s := by unfold s; norm_num
    refine le_trans (sum_le_sum (g:=fun j=>s/navy j) (fun i₀ _=>div_le_div_of_nonneg_right (e2 ..) (zero_le_one.trans (navy_pos _)))) ?_; suffices he: ∑ j∈range i,s/navy j ≤ s*1 by simpa only [mul_one] using he
    rw [show ∑ j∈range i,s/navy j=s*∑ j∈range i,1/navy j from ?_]; exact mul_le_mul_of_nonneg_left (navy_sum i) hs
    rw [mul_sum]; exact sum_congr rfl fun _ _=> by ring
 have hw(i:ℕ): (∫ x,c i x ∂μ!) ≤3/4:=by
  unfold c; have he: Integrable (fun x=> g i x+h i x) μ!:= P.ctRent _ (t i|>.add (t1 i)); rw [integral_add he (P.ctRent _ (hy i)),integral_add (P.ctRent _ (t i)) (P.ctRent _ (t1 i))]; linarith only [H0 i,e i,e1 i]
 obtain ⟨x,b',p⟩:= P.coresL c (fun i=> ((t i).add (t1 i)).add (hy i)) (fun i x=> add_nonneg (add_nonneg (q i x) (q1 i x)) (hx i x)) hw z
 refine ⟨x,b',p.mono fun i h' =>?_⟩
 · unfold c at h'; refine ⟨by linarith only [h', hx i x,q1 i x],by linarith only [h',hx i x,q i x],fun n w=>?_⟩; have he:a i n x ≤ b i x:= single_le_sum (f:=fun n=> a i n x) (fun j _=>hv i j x) (mem_range.mpr w); have h0:0<navy n:= lt_of_lt_of_le zero_lt_one (navy_pos _); exact (div_le_one h0).1 (show a i n x≤1 by linarith only [he,h',q i x,q1 i x])
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.reach_window
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.budgetFor

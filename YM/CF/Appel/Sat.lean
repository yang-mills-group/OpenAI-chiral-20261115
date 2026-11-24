import YM.CF.Appel.Parcel
set_option autoImplicit false
noncomputable section
namespace YM.CF.Appel
open Char Summit Neige
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal NNReal
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c} {K v d s t:ℝ} {n:ℕ}
open Gaussian ProbabilityTheory AnalyticBridge.Annulus1AD
open Set Topology
open SectorNext.Remainder.Affine SectorNext.Remainder.Scales
open Oriented Finset
lemma dues (u:Finset α)(v:α→ℝ)(q:Chi)(d:ℝ): q.share u v d = ∏ i,AnalyticBridge.Annulus1AD.profile q u v d i:=by
 unfold Chi.share; rw [← Finset.prod_mul_prod_compl u]; congr 1
 · refine prod_congr rfl fun i hi=>?_ ; unfold AnalyticBridge.Annulus1AD.profile; rw [if_pos hi]
 refine prod_congr rfl fun i hi=>?_ ; unfold AnalyticBridge.Annulus1AD.profile; rw [if_neg (mem_compl.mp hi)]
variable (q:Chi){D w:ℝ}
lemma see (A:Stores S)(u:Config G f)(V:Config G c)(k:S.Choices)(hw:0<w)(he:0<fiery G x S.patch.L)(hp:A.flags=flags (temp x) V):
 (q.profiles G S x w hw he).bill A k u V * S.likelihood u k= receipts q A x w univ univ univ u V k:=by
 have hh:=hp.symm
 unfold Chi.profiles; dsimp only; rw [Chi.distribute,if_pos hh]
 have hz : profilesHere x w q A u V k univ univ univ=q.fineShare S x u A.costs*q.bondShare S x w u k V A.aisles:=by
    have hx:∏ i:Site c,AnalyticBridge.Annulus1AD.flag x A V i=1:= Finset.prod_eq_one fun i _=>if_pos (by rw [hp])
    unfold profilesHere tokenF tokenB; rw [hx,mul_one, Chi.fineShare,Chi.bondShare,dues _ _ q, dues _ _ q] -- tune
 unfold receipts; rw [hz]; rfl
section fine
variable (K:Teller G)(κ width H:ℝ)(J:ChartRatio G) (m N:ℕ)
-- main earning. stamps. Could impose guard κ H4.
lemma ditto (h:SafeX K P J w κ width H m N x)(U:Tube G S)(O:Stores S)(hc:Cert P K S U x)(he:A.flags=flags (temp x) V) (hp:PointCharge U x w κ)(hr:Packet O A ((m+5)*radiusB x)) (hm: 2 ≤ m)(q':Chi)(l:ℕ)(hw:0<w)(β:ℝ)(z:LogArray G (Active A x F))(ht:β∈Set.Icc (y G S.patch.L x/2) (2*y G S.patch.L x)) :
 let t:=fiery G x S.patch.L; let d:=width*t; let M:= O.dome ((m+100)*radiusB x);
 let a:=realP β U F A V k x l q d Y z
 let X:=fieldU β U F A V k x l q d Y z;
 receipts q' A x w M (nearFace S M) (nearNoise M) X V k ≠0→ capsule x A F q d J (locals A O x F ((m+104)*radiusB x)) (tape a)≠0 →
 (∀ s:Signed,Wide (turnStore s O) (turnStore s A) m x w (pull s 0 X) (choice s k) (pull s 0 V))∧
 embH U A F V k q β d x Y l z (fun s=>anchorage (turnStore s O) (m*radiusB x)) ≤ -κ/4*(SectorNext.Remainder.Scales.p G S.patch.L x)^2 * O.shares -SectorNext.Remainder.coin G S.patch.L H N x*O.shares:=by
 intro t d M a X hz hf; have hJ:=hc.got; obtain ⟨hY,hD,hL⟩:= h.Hz; obtain hh:= h.He; rw [←hc.got] at hY hD hL hh
 have hv:K.Funds S U:=hc.funds.1; have hp':0<t:= Work.E09.temp_pos (lt_trans zero_lt_one hh.1)
 have hH(s:Signed):=force_wide (D:=m) (funds_branch hv) hw hp' (show O.dome ((m+5)*radiusB x) ⊆ M from farther (Nat.mul_le_mul_right _ (by omega))) hz s -- tune
 obtain ⟨b,hb⟩:= (h.HR S U A F V k (q'.profiles G S x w hw hp') hc he).2 -- tune
 obtain ⟨C,hc',hu,hR⟩:= h.Hp
 have hs(s):= hR S U (congr_arg RG.Patch.L hJ) hc.size hv m (turnForest s F) (turnStore s O) (turnStore s A) _ _ _ (turn_sliced s F X (fun i he=> F.on_tree _ ⟨i,he⟩)) (hH s)
 refine ⟨hH,Real.exp_le_exp.mp (depositing U V O q hv rfl hc.size hp hh hb ht hr le_rfl hm _ _ (by rw [hJ];exact h.Hl.2) hH (show _ ≤ (m+104)*radiusB x from Nat.mul_le_mul_right _ (by omega)) (right_ne_zero_of_mul hf) hY (by linarith) ⟨C,hc',hu,hs⟩).1⟩ -- tune
end fine
end YM.CF.Appel

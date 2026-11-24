import YM.CF.Neige.Never
set_option autoImplicit false
noncomputable section
namespace YM.CF.Neige
open Char Summit
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c}{a:ℕ} {K v d s t:ℝ} {n:ℕ}
open Finset Filter
open AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor PhysicalNext.OrderedAffine2B.SymRows
variable {q:Chi}{D v' A₀ m:ℝ}{i j: Rows.In x A F (G:=G)}{i' j':Rows.In x A' F' (G:=G)}
section warps
variable {α β:Type} [Fintype α][Fintype β][DecidableEq α][DecidableEq β](O :ColorOrtho G α)(e:α≃β)
local notation "W"=>warp O e
variable (M N : Matrix (β × G.ColorIndex) (β × G.ColorIndex) ℝ)
lemma mul_w : W (M*N)= W M * W N:=by
 apply Eq.symm; apply warp_of; intro a b; rw [←Matrix.mulVec_mulVec,warp_mv,warp_mv,move_dot,Matrix.mulVec_mulVec]
lemma one_w : W 1=1:= by apply Eq.symm; apply warp_of; intro a b; rw [one_mulVec,one_mulVec,move_dot]
lemma add_w : W (M+N)= W M + W N:=by unfold warp dressed; rw [Matrix.submatrix_add]; simp only [Pi.add_apply,Matrix.mul_add,Matrix.add_mul]
lemma scal_w(t:ℝ) : W (t • M)= t • W M:=by unfold warp dressed; rw [Matrix.submatrix_smul]; simp only [Pi.smul_apply,Matrix.mul_smul,Matrix.smul_mul]
lemma bank_w: W (perturb M N)=perturb (W M) (W N):=by
 have he: W M.transpose=(W M).transpose:=by rw [warp,warp,transpose_dressed, transpose_submatrix]
 rw [perturb, Char.warp_subX, fuseQ, mul_w,mul_w,he,one_w]; rfl
lemma bill_w: W (port M)=port (W M):=by
 have he:W (-M)= -W M:=by rw [← neg_one_smul ℝ M,scal_w,neg_one_smul]
 simp only [port, punt, add_w, scal_w, pow_two, mul_w,he, one_w]
end warps
section swing
variable {L:Box x A A' F F'}{O:ColorOrtho G (Bond f)}{U:ColorOrtho G (Slots S)}
lemma Nature(h:Flow L O U k k' T V W q D Y Y')(hh:Flows L)(l:ℕ)(hT:T.up.Bounds T.high v' A₀ s)(hs:S.patch.Branches S.kernel G)(p:FreeResolvent.Gap (baseX T x A F k V) m)(hm:0< m)(hp:120  ≤ radiusB x):
 layX T x A' F' k' q D Y' l W=warp (onBond O) L.onKey (layX T x A F k q D Y l V):=by unfold layX white bedX majorX; rw [boxV h hh hs hT, boxH h p hm hp,mul_w,bill_w,bank_w]
end swing
section Local
variable {M N:Gaussian.Table (Rows.In x A F (G:=G))}{M' N':Gaussian.Table (Rows.In x A' F' (G:=G))}
-- interval-level locality, no equiv F global
structure Names (M:Gaussian.Table (Rows.In x A F (G:=G)))(w:ℕ):Prop where
 rank (i j : Rows.In x A F (G:=G)): w< separation (front A F i) (front A F j) → M i j=0
lemma Names.under (h:Names M r)(hp:r ≤ l): Names M l:= ⟨fun i j hh=> h.rank i j (hp.trans_lt hh)⟩
lemma Names.turnt (h:Names M r): Names M.transpose r:= ⟨fun i j hh=> h.rank j i (by rwa [separation_comm])⟩
lemma Names.maps (h:Names M r)(hp:Names N l):Names (M*N) (r+l):=by
 refine ⟨fun i j hh=>?_⟩; rw [Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _; by_cases he:r< separation (front A F i) (front A F k)
 · rw [h.rank _ _ he,zero_mul]
 rw [hp.rank k j _,mul_zero]; have ht:= separation_triangle (front A F i) (front A F k) (front A F j); omega
lemma Names.foam (h:Names M r): Names (port M) (r+r):=by
 refine ⟨fun i j hh=>?_⟩; have he: r< separation (front A F i) (front A F j):=by omega
 have hi:i ≠ j:=fun h=>by subst h; rw [separation_self] at hh; omega
 unfold port punt; simp only [Matrix.add_apply,Matrix.neg_apply,Matrix.smul_apply,one_apply, if_neg hi,h.rank _ _ he, pow_two,(h.maps h).rank _ _ hh, neg_zero,smul_zero,add_zero]
lemma tooth(hr:Ready T x)(A:Stores S)(F:Forest S.ratio): Names (bark x V T k A F) (radiusB x/20):= ⟨fun i j hh=> Summit.mild_zero _ _ _ _ fun he=> hh.not_ge ((separation_comm ..).trans_le (PatchReads.ball_member he))⟩
lemma supportV(hr:Ready T x)(h:1000 ≤ radiusB x)(l:ℕ) : Names (bankX T x A F k q D Y l V) (radiusB x/20+radiusB x/20+radiusB x/20):=by
 let r:=radiusB x/20; let H:=majorX T x A F k q D Y l V; have hp:= tooth (V:=V) (k:=k) hr A F
 have hH:Names H r:=⟨fun i j hh=> hessN_off hr (fun hv=> hh.not_ge (PatchReads.ball_member hv)) h l⟩
 refine ⟨fun i j hi=>?_⟩; unfold bankX perturb; rw [Matrix.sub_apply,one_apply,if_neg (show i ≠ j from fun h=>by subst h; rw [separation_self] at hi; omega),sub_zero]; exact (((hp.turnt.maps hH).maps hp).rank _ _ hi)
lemma supportH(hr:Ready T x)(h:1000 ≤ radiusB x)(l:ℕ) : Names (layX T x A F k q D Y l V) (radiusB x):=by
 let r:=radiusB x/20; have he:=supportV (V:=V) (k:=k) (Y:=Y) (q:=q) (D:=D) hr h l; exact ((tooth hr (V:=V) (k:=k) A F).maps he.foam).under (by omega)
end Local
end YM.CF.Neige

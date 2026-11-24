import YM.SU5.Relativistic.Kinetic
import YM.CF.Vp929.Stage.Oar
import YM.CF.Newt.Tree
/-! # o(Vol) determinant credit at arc, exact comparisons with both flat gauges. -/
set_option autoImplicit false
set_option maxHeartbeats 980000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Papyrus.GaugeFlux
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Vale
open Corne
section logcap
variable {I:Type}[Fintype I][DecidableEq I]
private lemma thins (A:Matrix I I ℝ)(i:I): ∑ j, |A i j| ≤ ‖paintO (τ:=I) A‖ :=by
 let v : Fish I:= fun j=> if A i j≥ 0 then 1 else -1
 have he:‖v‖ ≤ 1:= (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i=> by unfold v; split_ifs<;> simp
 have hp:(∑ j,|A i j|)= paintO A v i:=by
    rw [paintO_p]; refine sum_congr rfl fun j _=>?_ ; change _=A i j*v j; unfold v; split_ifs with h; rw [abs_of_nonneg h,mul_one]; push Not at h; simp [abs_of_nonpos h.le]
 rw [hp]; exact (le_abs_self _ : paintO A v i ≤ |paintO A v i|).trans (((norm_le_pi_norm (paintO A v) _).trans (((paintO A).le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) he))))
private lemma schur_tails (P:Matrix I I ℝ)(h:P.IsSymm)(v:I→ℝ) : |dotProduct v (P*ᵥ v)|≤ ‖paintO P‖*dotProduct v v :=by
 let D:=FreeResolvent.native (1:Side); let K:I→Site (1:Side):=fun _=>0
 apply FreeResolvent.schur_qf D K
 exact ⟨⟨fun i=>by simpa only [D,FreeResolvent.Cost.weight_zero,one_mul] using thins _ i⟩,(show _ from ⟨fun i=> by change ∑ j,D.weight 0 _ _ *|(Matrix.transpose P) i j|≤_; rw [h]; simp only [D,FreeResolvent.Cost.weight_zero,one_mul]; exact thins _ i⟩)⟩ -- h type
-- use directional det monotonic. absolute at identical gaps.G1 G2 pd.
private lemma det_book {r t:ℝ}(A B:Matrix I I ℝ)(p:A.IsSymm)(q:B.IsSymm)(g:FreeResolvent.Gap A t)(w:FreeResolvent.Gap B t)(h:0<t)(e:0≤r)(v:‖paintO A - paintO B‖ ≤ r*t):
    |Real.log (Matrix.det A)-Real.log (Matrix.det B)|≤ Fintype.card I*r:=by
 let X:=1+r; have he:0<X:=by unfold X; positivity
 have hQ(A B:Matrix I I ℝ)(p:A.IsSymm)(q:B.IsSymm)(g:FreeResolvent.Gap A t)(w:FreeResolvent.Gap B t)(v:‖paintO A - paintO B‖ ≤ r*t):Real.log (Matrix.det A)-Real.log (Matrix.det B)≤ Fintype.card I*r:=by
    have H : ∀ (A:Matrix I I ℝ),A.IsSymm→ FreeResolvent.Gap A t→ Matrix.PosDef A:=fun A x p=> psd x (fun i e=>(mul_pos h (show 0<dotProduct i i from by simpa using (Matrix.PosDef.one (n:=I) (R:=ℝ)).dotProduct_mulVec_pos e)).trans_le (p.lower i))
    have hx := H A p g; have hy:= H B q w
    have hd {v:I→ℝ}(A:Matrix I I ℝ): dotProduct v ((X • A) *ᵥ v) = X*dotProduct v (A *ᵥ v):=by rw [Matrix.smul_mulVec,dotProduct_smul]; rfl
    have hu:=det_hike hx (Q:=X • B) (psd (by rw [Matrix.transpose_smul,q]) (fun i ht=>by rw [hd]; apply mul_pos he; simpa using hy.dotProduct_mulVec_pos ht)) (by
       intro i; rw [hd]; have hv:= le_trans (schur_tails (A-B) (by unfold Matrix.IsSymm; rw [Matrix.transpose_sub,p,q]) i) (mul_le_mul_of_nonneg_right (show ‖paintO (A-B)‖ ≤ r*t from by rw [map_sub]; exact v) (FreeResolvent.normSum_nn i)); rw [Matrix.sub_mulVec,dotProduct_sub] at hv
       have hp:= (abs_le.mp hv).2; have hh:= w.lower i; unfold X; nlinarith only [hp,e,hh])
    rw [Matrix.det_smul] at hu; have ht:= Real.log_le_log hx.det_pos hu; rw [Real.log_mul (pow_pos he _|>.ne') hy.det_pos.ne',Real.log_pow] at ht; nlinarith [Real.log_le_sub_one_of_pos he, (show X=1+r from rfl), (show (0:ℝ) ≤ Fintype.card I by positivity)]
 rw [abs_le]; constructor; · linarith only [hQ B A q p w g ((norm_sub_rev ..).trans_le v)]
 exact hQ A B p q g w v
end logcap
open _root_.YM.FreeResolvent (treeMatrix)
-- forest grant directly on any mint/call at increasing x even with arbitrary torus. gap with κ root constant
variable {K:Teller SU.group}{R:Patch}{L: ChartRatio SU.group}(V:Grace K R L) {C N:Side}
local notation "G₅"=> SU.group
lemma primal_g (i:ℕ)(N:Side)(p:2≤ N.val) : (blockD G₅ (V.L.H i) N).PosDef ∧ K.top.clip.direct^Fintype.card (ScrollB G₅ N)≤ costDet G₅ (V.L.H i) N := by apply fairDet G₅ _ p ((V.L.roof i).2.1 N) (V.L.mood i) (V.L.tied i)
lemma arc_toll {ε:ℝ}(q:0<ε) : ∀ᶠ x in atTop,∀ {C N:Side}(e:N.val=C.val*R.L.val)(i:ℕ)(M:Monk G₅ (V.L.op i e)), Cert R K (V.L.op i e) (V.L.mint i e) x →
   let Z:= Corne.arcD (V.L.mint i e) x M
   let S:=V.L.op i e
   |Z - (- (1/2:ℝ) * (Real.log (costDet G₅ (V.L.H i) N)+Fintype.card (Ink G₅ C)*Real.log S.kernel.penalty-Real.log (costDet G₅ (V.L.H (i+1)) C)))| ≤ ε * (Fintype.card (Site N):ℝ):= by
 let D:=4*(Fintype.card SU.group.ColorIndex:ℝ); let u:=ε/(D+1); have hv:D≥0:=by unfold D; positivity
 have huv:u≤ε:=div_le_self q.le (by linarith)
 have hz:0<u:=by unfold u; positivity
 let t:= FreeResolvent.Affine.headGap G₅ R K.bind K.top.clip; have ht:0<t:=FreeResolvent.Affine.headGap_pos ..; let h0:= u*t; let o:=ozPay R K.bind K.top.width K.top.paths G₅
 filter_upwards [smallF (n:=1) (div_pos K.top.width_pos (by norm_num :(4:ℝ)>0)) o, (show Tendsto temp atTop (𝓝 0) from by simpa using Work.E09.radiusB_temp 0).eventually (ge_mem_nhds (show 0<h0 from mul_pos hz ht))] with x W hp C N e i M p
 intro Z S; let F:= (kist M).park; let B:=V.L.H i; let T:=V.L.mint i e; let U:= treeMatrix G₅ S F B.metric; let k:= (kist M).k; let H:=B; have hx:= V.L.mood i; have hf:= V.L.roof i; have hH:=(V.L.deed i).link (V.L.sized i e)
 have he:= (FreeResolvent.Affine.identifies S F k p.pace.1 hx (V.L.tied i) (hf.2.1 N).roots (hf.2.2 N)); let A:=baseX T x (kist M).key F k 1
 obtain ⟨a,b⟩:= recount F x k (show T.up.Bounds T.high _ _ _ from hx) p.pace p.funds; rw [show FreeResolvent.Affine.primary (V.L.op i e) F k T.high T.up FreeResolvent.Affine.all 0=U from he] at b -- test
 let f:= pageX (G:= G₅) F x; let P:= A.submatrix f f; change P=_ at a; change _=U at b
 have hv':(V.L.op i e).patch= R:=V.L.patch_x ..
 have he0:FreeResolvent.Gap P t ∧ FreeResolvent.Gap U t:=by
    have hg:T.high=K.top.clip:=rfl; have ht:S.patch=R:=hv'; have hy:S.kernel=K.bind:=rfl; rw [←show FreeResolvent.Affine.headGap G₅ S.patch S.kernel T.high=t by rw [ht,hy,hg]]; constructor
    · rw [a]; exact FreeResolvent.Affine.directGap S F k T.high T.up _ p.pace
    rw [←show FreeResolvent.Affine.primary S F k T.high T.up (fun _=>true) 0=U from he]; exact FreeResolvent.Affine.directGap S F k T.high T.up _ p.pace
 have hK:P.IsSymm:=(Char.gramS ..).submatrix f -- tune
 have hu:U.IsSymm:=by
    unfold Matrix.IsSymm U treeMatrix FreeResolvent.fullMatrix FreeResolvent.baseMatrix; rw [Matrix.transpose_submatrix,FreeResolvent.tensor_transpose]; unfold Precision.K B; simp only [Matrix.transpose_add,Matrix.transpose_smul,Matrix.transpose_mul,Matrix.transpose_transpose,(hf.2.1 N).symmetric.1,Matrix.mul_assoc]
 have hP:=octo (T':=K) F x k (show T.up.Bounds T.high K.top.width K.top.paths V.W.bar from hx) p.pace p.funds K.top.paths_pos.le; rw [b,hv'] at hP -- tune
 have hd:=det_book U P hu hK he0.2 he0.1 ht hz.le (hP.trans (W.trans (by simpa using hp)))
 have hh:1<C.val:=p.pace.2.2; have hm: 2≤ N.val:= (show 2≤C.val by omega).trans ((Nat.le_mul_of_pos_right C.val R.L.property).trans_eq e.symm)
 obtain ⟨h₁,h₂⟩:= Work.F03.answer G₅ C N S p.pace F B K.top.clip T.up K.top.width K.top.paths V.W.bar _ _ (hf.2.1 N) hx (V.L.tied i) (hf.2.2 N) (Work.F02.answer _ _ T.up K.top.width K.top.paths _ hx)
 have hT:= stepGauge S G₅ B F hm hh h₂ (hf.2.1 _) (V.L.H (i+1)) _ hH.trial
 have hg:0<costDet G₅ (V.L.H i) N:= (primal_g V i N hm).1.det_pos; have hj:0<costDet G₅ (V.L.H (i+1)) C:= (primal_g V (i+1) C hh).1.det_pos; have hU:0 < U.det:= pos_of_mul_pos_left (show 0 < U.det*_ from lt_of_lt_of_eq (mul_pos hg (pow_pos S.kernel.penalty_pos _)) hT) hj.le -- tune
 have he' := congrArg Real.log hT; change Real.log (_*_)=Real.log (U.det*_) at he'; rw [Real.log_mul hg.ne' (pow_pos S.kernel.penalty_pos _|>.ne'), Real.log_pow, Real.log_mul hU.ne' hj.ne'] at he'
 rw [show Z=_ from (show Z= -(1/2:ℝ)*Real.log P.det by rw [show P.det= Matrix.det A from Matrix.det_submatrix_equiv_self f A]; rfl),show Real.log _+ _*_-_= _ from (show Real.log (costDet G₅ (V.L.H i) N)+Fintype.card (Ink G₅ C)*Real.log S.kernel.penalty-Real.log (costDet G₅ (V.L.H (i+1)) C)=Real.log U.det by linarith only [he'])]
 let Q:= Fintype.card (FreeResolvent.Active G₅ F); have hQ: (Q:ℝ) ≤ D*Fintype.card (Site N):=by
    have h:= Fintype.card_le_of_embedding (front S G₅ F); change Q ≤ Fintype.card (Ink G₅ N) at h; apply (Nat.cast_le.mpr h).trans_eq; rw [Fintype.card_prod]; unfold Bond Fixed.Pivots.Link Edge; rw [Fintype.card_prod]; unfold Axis D; rw [Fintype.card_fin]; push_cast; ring
 have hw: u*D ≤ 2*ε:=by unfold u; field_simp; nlinarith
 change _≤(Q:ℝ)*u at hd; rw [abs_le] at hd ⊢; constructor <;> nlinarith only [hd.1,hd.2,mul_le_mul_of_nonneg_right hw (show (0:ℝ) ≤ Fintype.card (Site N) by positivity),hQ,hz]
end YM.CF.Papyrus.GaugeFlux

import YM.SU5.FiniteGaugeData.Hierarchy.Vox
/-! # The naturality across observing levels in the same Rolled hierarchy -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
section convergence
variable {U W:Type*}[NormedAddCommGroup U][NormedSpace ℂ U][NormedAddCommGroup W][NormedSpace ℂ W]
variable {f:Filter ℕ}(P:ℕ→ U →L[ℂ] W)(F:U→L[ℂ] W)
lemma audition {x:ℕ→U}{y:U}(p:Tendsto P f (𝓝 F))(a:Tendsto x f (𝓝 y)): Tendsto (fun t=>P t (x t)) f (𝓝 (F y)):= ((show Continuous (fun p : (U→L[ℂ] W)×U=> p.1 p.2) from continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (p.prodMk_nhds a))

lemma submitted {x:ℕ→U}{y:U}(t:∀ x,Tendsto (fun k=>P k x) f (𝓝 (F x)))(C:ℝ)(h:∀ᶠ k in f, ‖P k‖≤ C)(a:Tendsto x f (𝓝 y)):
    Tendsto (fun k=>P k (x k)) f (𝓝 (F y)):=by
  suffices p: Tendsto (fun k=>P k (x k-y)) f (𝓝 0) by
    simpa [map_sub] using p.add (t y)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun k=>norm_nonneg _) (h.mono (fun k v=> (P k).le_of_opNorm_le v _)) ?_
  have hp:= (a.sub_const y).norm.const_mul C; simpa using hp
end convergence
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
local notation "W₀" => GridStep Λ l S
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable {P:Call Λ l}{J:Wicket Λ l}
variable (K:Universal Y h u v I E)(R:Rolled Y h u v J P)
lemma mark_advanced (p:Offered Y S s i k) :
    mkForm Y h S s i k = (mkForm Y h (GridStep Λ l S) (s+1) i k).comp (snag Y h S s i k):= by
  refine ContinuousLinearMap.ext fun x=>?_ ; rw [ContinuousLinearMap.comp_apply,mk_read _ _ _ _ _ _ (markGate_o (S:=S) (Y:=Y) (s:=s) (i:=i) (k:=k) p |>.1), snag_pay Y h S s i k p,mk_read _ _ _ _ _ _ (markGate_o (S:=S) (Y:=Y) (s:=s) (i:=i) (k:=k) p |>.2)]; exact transition_ticket ..

include K R
lemma horizon (p: Solvent Y S s i) : urn Y h S s i K = (urn Y h W₀ (s+1) i K).comp (J S s i):=by
  refine ContinuousLinearMap.ext fun x=>?_
  have hx:Tendsto (fun k=> (snag Y h S s i (v k)) x) atTop (𝓝 (J S s i x)):= audition _ _ ((R.evening S s).inner i) tendsto_const_nhds
  have ht:= often_offer_inner Y h S s i K p
  have he:= submitted (fun k=>mkForm Y h W₀ (s+1) i (v k)) (urn Y h W₀ (s+1) i K) (f:=atTop) (fun x:Catalog W₀=> inner_lim Y h W₀ _ i K x) (readCost Y h W₀ (s+1)) ((K.pick.grow_k.tendsto_atTop.eventually (reads_within Y h W₀ (s+1))).mono fun k t=>t i) hx
  exact tendsto_nhds_unique_of_eventuallyEq (inner_lim Y h S s i K x) he (ht.mono fun k p=> DFunLike.congr_fun (mark_advanced Y h S s i (v k) p) x)

lemma victoria : singer Y h S s K = (singer Y h W₀ (s+1) K).comp (P S s):=by
  refine ContinuousLinearMap.ext fun x=> ?_
  have hp:= K.pick.grow_i.tendsto_atTop.eventually (solvent_often Y h S s)
  have ht:= audition _ _ (R.evening S s).periods (tendsto_const_nhds (x:=x))
  apply tendsto_nhds_unique_of_eventuallyEq (ir_lim Y h S s K x) (submitted (fun i=> urn Y h W₀ (s+1) (u i) K) (singer Y h W₀ (s+1) K) (fun x=> ir_lim Y h W₀ _ K x) (readCost Y h W₀ (s+1)) (Eventually.of_forall (fun i=>income_v Y h W₀ (s+1) _ K)) ht)
  exact hp.mono fun i p=> DFunLike.congr_fun (horizon Y h S s (u i) K R p) x

lemma headlined (x:Catalog S) : E s (composeQ Kₜ S x)= E (s+1) (composeQ Kₜ W₀ (P S s x)) := DFunLike.congr_fun (victoria Y h S s K R) x
#print axioms victoria
end YM.CF.Buffered.Afterglow.Hierarchy

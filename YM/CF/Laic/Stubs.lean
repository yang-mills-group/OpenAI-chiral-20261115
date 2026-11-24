import YM.CF.Laic.Warm
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n N:Side}{T:RG.StepData (More n) (More N)}{F: Forest T.ratio}{u:Cloud n→ AxisChart group F}
def whisp (p:Positions (Primary (More n) group)):Cloud n:= tint group (Body 1 (More n)) p
def aTrait(T:RG.StepData (More n) (More N))(x:Primary (More n) group):= T.ratio.embed x.1.1
structure Horizon (F:Forest T.ratio) (u: Cloud n→AxisChart group F)(k:ℕ)(r d:ℝ):Prop where
 smooth:ContDiffAt ℝ ω u 0
 flat:u 0=0
 p: Envelope (aTrait T) (clothH T F) r k (Push.Uniform.curve (station u)) 0 d
lemma provision {Q:RG.KernelChoices}{j k m:ℕ}{R:RG.PathData group}{μ C Λ:ℝ}{p:RG.Clip}(P:Push.Uniform.Before group μ C j Q m)(ht:R.Bounds p μ C Λ)(hv: Bid.Larger (G:=group) T)(he:T.patch.J=j)(hT:T.kernel=Q)(h:k<m)(U: Critical F p R u): let S:=P.tables p T.patch; let r:= responseRate S.coords m S.value S.width S.gap; let d:=curveCost S.coords S.value S.width S.gap k
 Horizon F u k r d∧ 0<r∧ 0<d:=by
 intro S r d; let t:T.Choices:=Classical.arbitrary _
 obtain ⟨v,g⟩:= P.graph F ht hv he hT -- signature
 have hp: (Push.Uniform.curve (station u)) =ᶠ[𝓝 0] (Push.Uniform.curve (station v)):=by
    let L:= tint group (Body 1 (More n)); have hy:Tendsto L (𝓝 0) (𝓝 0):=by simpa using L.continuous.tendsto 0
    filter_upwards [hy.eventually (Before.Service.is_extension g U)] with x hx; unfold Push.Uniform.curve station; rw [Function.comp_apply,Function.comp_apply, show u (tint _ _ x)= _ from hx]; rfl
 have he':= (P.receipt (B:=F) (t:=t) ht hv he hT).1
 have hg : (0:Positions (Primary (More n) group))∈Metric.ball 0 S.horizon:=Metric.mem_ball_self g.x_pos
 have hk:= envelopes he' (g.series hg) (g.pricing hg) (g.entered ht hv he hT hg t) h
 refine ⟨⟨U.2.1,U.1,fun i p s q t=>?_⟩, rate_pos he',zero_lt_one.trans_le (curveCost_ge he' _)⟩; unfold Push.Uniform.entry; rw [(hp.iteratedFDeriv ℝ i).eq_of_nhds]; exact hk i p s q t -- tune
lemma wellPath (p:Positions (Primary (More n) group)): hats F (Push.Uniform.curve (station u) p)= ears F u (whisp p):=by
 let L:= tint group (Body 1 (More n)); have he:paint F group (Push.Uniform.curve (station u) p)=(L p, u (L p)):=by rw [Push.Uniform.curve, paint_meet]; dsimp only [station,Function.comp_apply]; rw [ContinuousLinearEquiv.apply_symm_apply]
 unfold hats ears baby natJoint Stationary.encamp Stationary.abode fine outer; rw [he,ContinuousLinearEquiv.apply_symm_apply,bornL]; rfl -- tune paint ambiguity
lemma escH {k:ℕ}{a b c d:ℝ}(v:0<a)(w:0<b)(g: Horizon F u k b c)(h:0≤c){U: Snap F→ Op (Single n)}(Q: HoldX (clothH T F) (popH T) U a d k){R:Cloud n→ Op (Single n)}(ht:∀ x,R (whisp x)=U (Push.Uniform.curve (station u) x)):
 HoldX (aTrait T) (popH T) (R∘whisp) (litSpan k b a) (d*machinist k (townCost group) c a) k:=by
 let T':=Push.Uniform.curve (station u); let L:=tint group (Body 1 (More n)); let X:= tint group F.Free; have hs:ContDiffAt ℝ ω (station u) 0:= X.symm.contDiff.contDiffAt.comp (f:=u ∘ L) _ ((show ContDiffAt ℝ ω u (L 0) by rw [map_zero]; exact g.smooth).comp _ L.contDiff.contDiffAt)
 have hp:T' (0:Positions (Primary _ _))=0:=by
    unfold T' Push.Uniform.curve station; rw [Function.comp_apply,Function.comp_apply,map_zero,g.flat,map_zero]; change (partSpace ..).symm (0,0)=0; exact map_zero _
 have hh:= Push.Uniform.along hs; have hx:R ∘ whisp= U ∘ T':= funext ht
 have hU:ContDiffAt ℝ ω U (T' 0):=by rw [hp]; exact Q.glow
 rw [hx]; refine ⟨hU.comp _ hh,fun r=> ?_,mul_pos Q.funds (machinist_pos h v)⟩
 refine (Cable.attach (l:=aTrait T) (m:=clothH T F) (g:=T') (x:=0) (F:=coinZ r ∘ U) (inkJet r (Nacre.tort.mp hU)) hh (?_) g.p v w Q.funds.le h (town F)) -- tune
 rw [hp]; exact Q.law r
end YM.CF.Laic

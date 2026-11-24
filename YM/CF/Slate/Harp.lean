import YM.CF.Slate.Hydro
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
open Work.E03 AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal Gauges PhysicalNext.OrderedAffine2B.SymRows
local notation "G"=>SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
variable (g:Site c→SU.group.El) (M:Monk G S) (q:Chi)(x β d:ℝ)
abbrev shiftZ : Monk G S:={M with U:= Lattice.gauge (constantGauge g S.ratio) M.U, V:= Lattice.gauge g M.V,z:= Motion.swing (constantGauge g S.ratio) M.z}
abbrev Pogo(L:Prices SU.group (M.zoo x)) := Orthogonal.move (onBond (rotating (constantGauge g S.ratio))) (Equiv.refl (M.zoo x)) L
lemma audU (A:LinkArray SU.group (Frozen M.key x M.park))(a:Prices SU.group (M.zoo x)): landed x M.key M.park (Lattice.gauge g M.V) (gaugeY g x M.key M.park A) (Pogo g M x a)= Lattice.gauge (constantGauge g S.ratio) (landed x M.key M.park M.V A a):=by
 let U:= landed x M.key M.park M.V A a; let V:= Lattice.gauge g M.V; let f:= M.park; let Z:= landed x M.key M.park V (gaugeY g x M.key M.park A) (Pogo g M x a); let K:=constantGauge g S.ratio; let T:= M.key; funext i
 change Z i=K i.1 * U i*(K (i.1+step i.2))⁻¹; by_cases h:i∈ f.trunks
 · have hp:K (i.1+step i.2)= K i.1:=congrArg g (f.trunk_internal h); rw [hp, show Z i=1 from f.on_tree _ ⟨i,h⟩,show U i=1 from f.on_tree _ ⟨i,h⟩,mul_one,mul_inv_cancel]
 let t:f.Free:= ⟨i,h⟩; change f.drape _ t.val=_* f.drape _ t.val*_; rw [f.off_tree,f.off_tree]; unfold Next.SectorChange.returned thaw; by_cases v:chill T x f t
 · let L: Frozen T x f:= ⟨t,v⟩; change _=K i.1*_*(K (i.1+step i.2))⁻¹; rw [show t=L.val from rfl,freeze_held,freeze_held]; rfl
 let a':Active T x f:=⟨t,v⟩; change _=K i.1*_*(K (i.1+step i.2))⁻¹; rw [show t=a'.val from rfl,freeze_regular,freeze_regular]; change SU.group.lieExp (tape (Pogo g M x a) a')* replica S.ratio V i=_*(SU.group.lieExp (tape a a') * replica S.ratio M.V i)*_
 unfold Pogo; rw [move_tape]; let u:=tape a a'; have hp:replica S.ratio V i=K i.1 * replica S.ratio M.V i * (K (i.1+step i.2))⁻¹:= (congrFun (copied S.ratio S.patch.odd_side M.V g) i).symm -- tune
 change SU.group.lieExp (SU.group.adjoint (K i.1) u) * replica S.ratio V i= _
 rw [hp, show SU.group.lieExp _=K i.1 * SU.group.lieExp u * (K i.1)⁻¹ from exp_adjoint (K i.1) u]; unfold u; group
local notation "N"=>shiftZ g M
variable (h:K.Funds S T)
include h

lemma brag (l:ℕ): liftN T x (shiftZ g M).V (shiftZ g M).k (shiftZ g M).key (shiftZ g M).park q d ((shiftZ g M).bush x) l=Pogo g M x (liftN T x M.V M.k M.key M.park q d (M.bush x) l):=by
 obtain ⟨σ,L,H,V⟩:=h.feeds; rw [← h.high] at H
 have hx := boxL (l:=l) (gaugeH T M.key M.park x M.V M.k q d (M.bush x) g H (funds_branch h)) (fun _=> Iff.rfl) (funds_branch h) H; exact hx
omit h in
lemma windM {α γ:Type}[Fintype α][Fintype γ][DecidableEq α][DecidableEq γ](O:ColorOrtho SU.group α)(Q:α≃γ)(A B:Prices SU.group γ)(x:ℝ) : Orthogonal.move O Q A + x • Orthogonal.move O Q B=Orthogonal.move O Q (A+x • B):=by unfold Orthogonal.move; change _= Matrix.mulVec _ (_+x • (B ∘ _)); rw [Matrix.mulVec_add, Matrix.mulVec_smul]; rfl
lemma buzz(l:ℕ)(r:ℝ)(p:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) r)(ht:0<r)(hz:120≤radiusB x):
 (shiftZ g M).fuel x T q d l β=Pogo g M x (M.fuel x T q d l β) :=by
 let Q:= credW T M.key M.park M.k q d x (M.bush _) l M.V; let D : Gaussian.Table (Active M.key x M.park × SU.group.ColorIndex) :=credW T (shiftZ g M).key (shiftZ g M).park (shiftZ g M).k q d x ((shiftZ g M).bush _) l (shiftZ g M).V
 obtain ⟨σ,a,H,A⟩:= h.feeds; rw [← h.high] at H
 have he:D= Orthogonal.warp (onBond (rotating (constantGauge g S.ratio))) (Equiv.refl (M.zoo x)) Q:= Neige.Nature (gaugeH T M.key M.park x M.V M.k q d (M.bush x) g H (funds_branch h)) (fun _=> Iff.rfl) l H (funds_branch h) p ht hz
 let O:= Pogo g M x; have hh:tape.symm ((shiftZ g M).bell x)= O (tape.symm (M.bell x)):=by
    apply tape.injective; funext i; unfold O Pogo; erw [move_tape,tape.apply_symm_apply,tape.apply_symm_apply]; rfl
 unfold Monk.fuel realP spinC; rw [brag g M q x d h]; -- tune dependent cast
 change O _+ coupling β • (D *ᵥ _) =O (liftN T x M.V M.k M.key M.park q d (M.bush x) l+ coupling β • (Q *ᵥ _)); unfold O Pogo at *; rw [hh,he,warp_mv]; change _ = _
 exact windM ..
lemma vega(s:Signed)(U:Config G f): pull s 0 (Lattice.gauge (constantGauge g S.ratio) U)= Lattice.gauge (constantGauge (turned g s) S.ratio) (pull s 0 U):=by rw [Work.F05.pull_gauge_zero]; congr 1; funext i; exact Gauges.comm ..
end YM.CF.Slate

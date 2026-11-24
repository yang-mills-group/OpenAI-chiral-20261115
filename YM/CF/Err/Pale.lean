import YM.CF.Err.Pim
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Err
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
variable{T:Tube SU.group S} {A:Stores S}{F:Forest S.ratio}{V:Config SU.group c}{k:S.Choices}{L:Teller SU.group} {α:Type*}[NormedAddCommGroup α][NormedSpace ℝ α]{R:α→ Directions SU.group c}{Y:α→LinkArray SU.group (Frozen A x F)}{N m l:ℕ}{C u:ℝ}
abbrev Scope {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ SU.group.El)(i:E): Prop:=ContDiffAt ℝ (↑l) (SU.group.mat ∘ U) i -- missing l explicit
lemma patch_r{X:α}(h:ContDiffAt ℝ (↑l) R X)(t:∀ j, Scope (l:=l) (fun v=>Y v j) X)(p:0<d)(k:2*d< firstRadius G): ContDiffAt ℝ (↑l) (fun i=> lacG x q d ((Vmove x V ∘ R) i) (Y i)) X:=by
 refine gaugeCount.symm.contDiff.contDiffAt.comp (f:=fun i=> autoShell q d ((Vmove x V ∘ R) i) (Y i)) X (contDiffAt_pi.mpr fun j=>?_)
 let Z(i:α):=replica S.ratio (Vmove x V (R i)) j.val.val; have he:Scope (l:=l) Z X:=by
    unfold Z replica; split; exact contDiffAt_const; let g:= j.val.val; let e:Bond c:=(S.ratio.parent g.1,g.2)
    unfold Scope; change ContDiffAt ℝ (↑l) (fun i=> SU.group.mat (SU.group.lieExp (temp x • R i e) * V e)) X; simp_rw [Gauge.mat_mul]; exact (((SU.group.exp_jet.of_le le_top).contDiffAt).comp X ((contDiffAt_pi.mp h e).const_smul _)).mul contDiffAt_const -- tune notation
 change ContDiffAt ℝ (↑l) (fun i=> patched _ _ (Y i j * (Z i)⁻¹)) X; apply Skye.hop q p k (k:=(l:ℕ∞)); simp only [Function.comp_def,Gauge.mat_mul,Gauge.mat_inv]; exact (t j).mul ((starL' ℝ).contDiff.contDiffAt.comp _ he) -- Frobenius
variable {U:α}{s:ℝ}
lemma posse(F': MossX N l x A F T V k C d s q)(h:L.Funds S T)(hd:l≤18)(ht:0 < d)(hk:2*d<firstRadius G)(hp:R U=0)(g:ContDiffAt ℝ (↑N) R U)(cV:∀ i,Scope (l:=N) (fun v=>Y v i) U): ContDiffAt ℝ (↑N) (fun i=> liftN T x ((Vmove x V ∘ R) i) k A F q d (Y i) l) U:=by
 let P(i:Directions G c)(a: LinkArray G (Frozen A x F)):=liftN T x (Vmove x V i) k A F q d a l; let f(i:Directions G c)(a: LinkArray G (Frozen A x F)):= lacG x q d (Vmove x V i) a
 obtain ⟨o,z,v⟩:= ownsY  (A:=A) (F:=F) (x:=x) (Vmove x V 0) ht (by linarith) q
 let D:=Prices G (Frozen A x F); let X(w:Directions G c): D→ₗ[ℝ] Prices G (Active A x F):= (linQ h hd F'.ready (Vmove x V w) (k:=k) (F:=F) (q:=q) (d:=d) (A:=A)).choose
 refine plod P f (0:Directions G c) R U Y o z X (fun a i=> (linQ h hd F'.ready _ (k:=k) (F:=F) (q:=q) (d:=d) (A:=A)).choose_spec _ _) hp v g (patch_r g cV ht hk) (fun j=> patch_r (Y:=fun _=>j) (R:=fun x=>x) (V:=V) (X:=0) contDiffAt_id (fun _=>contDiffAt_const) ht hk) (fun j=>?_ ) -- placeholders
 obtain ⟨-,l,-⟩:=F'.jumps j; exact l.smooth
lemma coinL {T':α→ℝ}{z:α→LogArray G (Active A x F)}(F': MossX N l x A F T V k C d s q)(h:L.Funds S T)(hd:l≤18)(ht:0 < d)(hk:2*d<firstRadius G)(hp:R U=0)(g:ContDiffAt ℝ (↑N) R U)(cV:∀ i,Scope (l:=N) (fun v=>Y v i) U)(f:ContDiffAt ℝ (↑N) T' U)(hQ:0< T' U) (hc:ContDiffAt ℝ (↑N) z U): ContDiffAt ℝ (↑N) (fun i=>realP (T' i) T F A ((Vmove x V ∘ R) i) k x l q d (Y i) (z i)) U:=by
 let P:=fun i=> Vmove x V (R i); have hh:ContDiffAt ℝ (↑N) (coupling ∘ T') U:= (f.sqrt hQ.ne').inv (Real.sqrt_pos.mpr hQ).ne' -- tune
 have ht(v:Config G c)(y):credW T A F k q d x y l v=credW T A F k q d x 1 l v:=by unfold credW layX majorX; rw [looser (Z:=1) F'.ready hd]
 let Q:=credW T A F k q d x 1 l
 let a(i:α): Prices G (Active A x F):= paintO (Q (P i)) (tape.symm (z i)); have ha: ContDiffAt ℝ (↑N) a U:=by
    have hx:Protected N (Q ∘ Vmove x V) 0 C:= by obtain ⟨p1,p2,p3,p4,h,-,-⟩:=F'.jumps 1; exact h
    exact (((show ContDiffAt ℝ (↑N) (fun i=> paintO ((Q ∘ Vmove x V) i)) (R U) from hp.symm ▸ hx.smooth).comp U g).clm_apply ((gaugeCount (ι:=Active A x F) («G»:=SU.group)).symm.contDiff.contDiffAt.comp U hc))
 have hR(i): realP (T' i) T F A (P i) k x l q d (Y i) (z i)=liftN T x (P i) k A F q d (Y i) l+(coupling (T' i)) • a i:=by change _+ _ • (credW T A F k q d x _ l _ *ᵥ _ )= _; rw [ht]; rfl
 change ContDiffAt ℝ (↑N) (fun i=> realP (T' i) T F A (P i) k x l q d (Y i) (z i)) U; simp_rw [hR]; exact (posse F' h hd ‹0<d› hk hp g cV).add (hh.smul ha)
end YM.CF.Err

import YM.CF.Siete.Pile
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Jet Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{P:Teller G}{S: StepData c f}{F: Forest S.ratio}{A:Stores S}{x d:ℝ}{X:Support f}{T:Tube G S}{Y:Support c}{I:Type}[Fintype I][DecidableEq I]{n:ℕ}
variable (T) (M:Museum F x A X Y I)(β:ℝ)(k:S.Choices)(q:Chi)(d:ℝ)(l:ℕ)(B:Config G f)(Z:LogArray G (Active A x F))
variable {a s C J w Q:ℝ}
abbrev incF(M: Museum F x A X Y I)(i:I):Site c:=S.ratio.parent (M.address i).1
def airP(V:Support c)(R:ℕ):= Finset.univ.filter (fun i: Active A x F=> S.ratio.parent i.val.val.1∈halo R V)
def coZ(X:Museum F x A X Y I): Finset (Active A x F):= airP (A:=A) (F:=F) (x:=x) (univ.image (incF X)) (radiusB x) -- H undecl
lemma getT(hr:Ready T x)(hp:1000 ≤ radiusB x)(V W:Config G c) (p:∀ i:I,AgreeNear id (incF M i) ((l+50)*radiusB x) V W)(u:LogArray G (Active A x F))(h:Set.EqOn Z u (coZ M)): traceU T M β k q d l B Z V=traceU T M β k q d l B u W:=by
 let N:= Folio.leaf A F x B; funext i; let R:= radiusB x; let t:In x A F (G:=G):=M.colorSeat G i
 have hg: Scan S x (front A F t) ((l+50)*R) A A F F k k V W N N:=⟨fun _ _=>Iff.rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>Iff.rfl,p i.1,fun i j hp he=>congrArg _ (Subtype.ext (Subtype.ext he):i=j)⟩
 let O:=credW T A F k q d x N l; have he:(O V *ᵥ tape.symm Z) t= (O W *ᵥ tape.symm u) t:=by
    simp only [Matrix.mulVec,dotProduct]; apply sum_congr rfl; intro j _; by_cases l': separation (front A F t) (front A F j) ≤ R
    · have hM:j.1∈ coZ M:= mem_filter.mpr ⟨mem_univ _,halo_spec.mpr ⟨front A F t,mem_image_of_mem (incF M) (mem_univ i.1),l'⟩⟩
      rw [show tape.symm Z j=tape.symm u j from congrArg (fun x:G.Color=>x j.2) (h hM), show O V t j= _ from layPt (Y:=N) (Y':=N) (l:=l) hr hp t t j j (hg.lower (Nat.mul_le_mul_right _ (by omega))) rfl rfl]; rfl
    have hh:separation (front A F t) (front A F j)> R:=(by omega); rw [show O V t j=0 from (supportH hr hp l).rank _ _ hh, show O W t j=0 from (supportH hr hp l).rank _ _ hh]; simp
 change (_ + coupling β* _- Offset.mean T x k A F q d N V t)=_
 rw [liftN_read (i:=t) (i':=t) hr (q:=q) (d:=d) (l:=l) (hg.lower (Nat.mul_le_mul_right _ (by omega))) rfl,meetX hr (i:=t) (i':=t) (hg.lower (by rw [Nat.add_mul]; unfold R; omega)) rfl,he]; rfl
private lemma houseE {E α:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Fintype α][DecidableEq α]{x:E}{M:E→Matrix α α ℝ}{K:ℝ} (h:Protected n M x K)(f:Fish α):Allows n (fun y=>M y*ᵥ f) x (‖f‖*K):=by
 refine h.linear (ContinuousLinearMap.apply ℝ _ f) ?_; exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun k=> (k.le_opNorm _).trans_eq (mul_comm ..)
lemma flyP (V: Config G c) (hr:Ready T x)(hp:1000 ≤ radiusB x)(t:Allows n (fun y=>cot T x (Vmove x V y) k A F q d (Folio.leaf A F x B) l) 0 C)(u:Protected n (credW T A F k q d x (Folio.leaf A F x B) l∘ Vmove x V) 0 a)(v:0 ≤ a)(h:∀ i∈coZ M,‖Z i‖ ≤ Q)(w:0 ≤ Q): Allows n (traceU T M β k q d l B Z ∘ Vmove x V) 0 (C+|coupling β| *(Q*a)):=by
 let z :LogArray G (Active A x F):= fun i=> if i∈coZ M then Z i else 0; have hg:‖tape.symm z‖≤ Q:= (loomP z).trans ((pi_norm_le_iff_of_nonneg w).mpr fun i=> by unfold z; by_cases p:i ∈ coZ M <;> simp [p]; exact h i p; exact w) -- tune
 let N:=Folio.leaf A F x B; apply allows_pi (t.nonneg.trans (le_add_of_nonneg_right (by positivity)))
 intro i; let H:=readZ ((houseE u (tape.symm z)).mono (mul_le_mul_of_nonneg_right hg v)) (M.colorSeat G i); apply ((readZ t (M.colorSeat G i)).add (H.smul (coupling β))).germ; filter_upwards [] with y; simp only [Function.comp_apply]
 rw [getT T M β k q d l B Z hr hp _ _ (fun _ _ _=>rfl) z (fun i hp=>(if_pos hp).symm)]; unfold cot traceU realP spinC; simp only [Pi.sub_apply,Function.comp_apply, Pi.add_apply,Pi.smul_apply]; abel
end YM.CF.Siete

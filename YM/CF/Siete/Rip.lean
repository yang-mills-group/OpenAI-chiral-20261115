import YM.CF.Siete.Frame
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{P:Teller G}{S: StepData c f}{F: Forest S.ratio}{A:Stores S}{x d:ℝ}{X:Support f}{T:Tube G S}{Y:Support c}{I:Type}[Fintype I][DecidableEq I]{n:ℕ}
variable (T) (M:Museum F x A X Y I)(β:ℝ)(k:S.Choices)(q:Chi)(d:ℝ)(l:ℕ)(B:Config G f)(Z:LogArray G (Active A x F)) (g:Site c→ G.El)
variable {a s C J w r v Q ε η t:ℝ}
lemma proofHere (b:Folio.Bulletin x P T)(E:Seam T η J)(W: Heir.Web G)(p:0<η)(hp:0≤ J)(t₁:licensed η J S.patch.L)(U:Heir.Act T F x k n t C)(hC:1≤C)(hn:2≤n)(hx:Tension W η C ε x t v r)(hr:0<r)(V:Config G c)(hV:Healthy (temp x) Y V)
    (h:∀ p: Pressure.Cell f,Heir.Tests X p→let o:=S.ratio.parent p.1; ∃ (y:Directions G c)(g: Site c→ G.El), ‖y‖ ≤ v ∧ AgreeNear id o (Heir.reach x) (gauge g V) (increment 1 y)∧ ‖atoms T M β k q d l B Z g V‖ ≤ ε*r):Healthy (r/4) X (recent T β k q d l B Z V):=by
 apply disjoint_left.mpr; intro i hi h'; obtain ⟨e,hj,hz⟩:= (flags_spec ..).mp h'
 have he:Tests X e:=⟨_,hi,hj⟩; set o:=S.ratio.parent e.1; let R:=recent T β k q d l B Z V; obtain ⟨y,g,hu,hB,H⟩:=h e he
 let a:=atoms T M β k q d l B Z g V; have hv:Museum.Station Y x o:= (Corona.halo_mono (Nat.le_add_right ..) (Finset.Subset.refl _)).trans (M.asks _ (he.retain (Work.E01.base_touched e)))
 have ht:=border_toll E p hp t₁ U hC hn hx (p:=(y,a)) hr e hv hu H hV hB
 let z:= g ∘ S.ratio.parent; let u i:= G.lieExp (φ T F true y i)
 rw [show faceValue _ e= faceValue (Lattice.gauge u (gauge z R)) e from ?_,face_gauge,face_gauge, Gauge.chord_conj,Gauge.chord_conj] at ht; swap
 · exact travel_local _ _ _ _ fun i hi hi'=> obtain_s T M β k q d l B Z g b hv V y hB i (he.retain (List.mem_toFinset.mpr hi)) (he.retain (List.mem_toFinset.mpr hi')) ((Work.E04.parent_separation ..).trans (by have hh:=Work.E01.sep_touched e i.1 (List.mem_toFinset.mpr hi); omega)) true
 change r/4<_ at hz; change G.chord (faceValue (recent T β k q d l B Z V) e)<_ at ht; linarith only [ht,hz,hr]
end YM.CF.Siete

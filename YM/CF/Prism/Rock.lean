import YM.CF.Prism.Gale
import YM.CF.Matter.Mass
set_option autoImplicit false
noncomputable section
namespace YM.CF.Prism
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.Frobenius
variable {n:Side}
open Scree
variable {B:RG.BudgetPoint}{X:Hub n}{h c:ℝ}{F:InkD n} (p: PressB B X F h c)
open PhysicalNext.JointLoad MultiNext.SignedSource AnalyticBridge.VerifiedReset Heir RG
set_option quotPrecheck false
local notation "o"=> X.val.1
local notation "Ω"=> X.val.2
abbrev wip (v:Seat n)(d:Axis)(u:group.Color)(t:ℝ)(x:Seat n):E:= rollH u (-t*AnalyticBridge.VerifiedReset.coord v x d)
def lap (e:Axis)(U:tangD n) : tangD n:=fun i=>if i.2=e then U i else 0
lemma laP(U:tangD n): ∑ i,lap i U=U:=by funext p; simp [lap,Finset.sum_apply]
lemma formM (x: tangD n)(e:Axis)(u:group.Color)(t:ℝ) (v:Nonwrapping Ω o)(r:4 ≤ (More n).val)(h:∀ i:Seat n, Mom.needed Ω (i,e) → x (i,e)=u):Agrees Ω (increment 1 (t • lap e x)) (Lattice.gauge (wip o e u t) 1):=by
 rintro ⟨i,j⟩ hi hp; change group.lieExp (t • _) * 1= (_ * 1) *_
 rw [mul_one,mul_one,Cascade.roll_inv,←Cascade.rollAdd,AnalyticBridge.VerifiedReset.coord_step (v _ hi) r]
 by_cases h':j=e; · subst j; rw [if_pos rfl]; change group.lieExp (t • lap e x _)=_; rw [show lap e x (i,e)=u from (if_pos rfl).trans (h i ⟨hi,hp⟩)]; ring_nf
 rw [if_neg (Ne.symm h' : e≠ (i,j).2), show lap e x (i,j)=0 from if_neg h', smul_zero]; unfold rollH; simp
lemma singleM (u:ℝ)(v:tangD n)(he:Lyre.Sized u v B o)(h:Mom.screen Ω v∈Mom.Maps o Ω 1)(e:Axis):∃ w:group.Color,(∀ i:Seat n,Mom.needed Ω (i,e)→v (i,e)=w) ∧ ‖w‖ ≤ u*(B.threshold*(1+(Heir.breadth B Ω:ℝ))^B.power):=by
 obtain ⟨f,hf,t⟩:=h
 have hi(i:Seat n)(k:Mom.needed Ω (i,e)):v (i,e)=f e 0:=by
    have ht:=t (i,e); rw [Mom.screen_at,if_pos k,if_pos k] at ht; refine ht.trans ?_; change f e _=_; simpa using (Mom.base (hf e)).2 0 (Mom.stamp o i) |>.symm -- tune Universe argument
 by_cases p:∃ i:Seat n,Mom.needed Ω (i,e)
 · obtain ⟨i,k⟩:=p; have hh:separation i o ≤ Heir.breadth B Ω:= Heir.close_enough X.property (Finset.mem_union_left _ k.1); refine ⟨_,hi,?_⟩; rw [←hi _ k]; apply (he.2 _).trans; unfold Lyre.width; have hy:=B.threshold_pos; have hx:=he.1; gcongr
 have hx:=B.threshold_pos; have hu:=he.1; exact ⟨0,fun i h=>False.elim (p ⟨i,h⟩),by rw [norm_zero]; positivity⟩
-- local chart matter components
abbrev aull(b:Bool)(i j:SU.Slot)(x:group.Color) := gemT (group.lieExp x) b i j
lemma curr(b:Bool)(i j:SU.Slot):ContDiff ℝ ω (aull b i j):=by
 have hx (i j:SU.F): ContDiff ℝ ω (fun x:group.Color=>fund (group.lieExp x) i j):=(Laic.entry_F  i j).contDiff.comp group.exp_jet -- tune
 have hg (i j: SU.Sheet):ContDiff ℝ ω (fun x:group.Color=>each (fund (group.lieExp x)) i j):=by
    cases i <;> cases j <;> simp only [each,Join.both, Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂, ExTwo.wedge_entry,cc_apply] <;> first| exact ((hx _ _).mul (hx _ _)).sub ((hx _ _).mul (hx _ _))|exact (starL' ℝ:ℂ ≃L[ℝ] ℂ).contDiff.comp (hx _ _)| exact contDiff_const
 have he(i j:SU.Slot):ContDiff ℝ ω (fun x:group.Color=>(matter (group.lieExp x)).val i j):=by rcases i with ⟨a,i⟩; rcases j with ⟨b,j⟩; exact (contDiff_const (c:=(1:Op (Fin 3)) a b)).mul (hg _ _)
 cases b; exact (starL' ℝ:ℂ≃L[ℝ]ℂ).contDiff.comp (he _ _); exact he _ _
abbrev crack(k : Finset (Dwell n)→ℝ)(x y:Rock n):ℝ:= ∑ i:SU.Slot,∑ j:SU.Slot,k {(true,(x,i)),(false,(y,j))}
def crib (F:InkD n)(x y:Rock n)(i j:SU.Slot): Pane n→ℂ:=fun V=>mileT x y true false (F V) i j
private lemma scale_left {F:tangD n→ℂ}(h: Signs B o F c)(i:ℂ)(hy:‖i‖=1): Signs B o (fun v=>i*F v) c:=by
 let L:ℂ →L[ℝ] ℂ:= i • ContinuousLinearMap.id ℝ ℂ
 refine ⟨h.grade,L.contDiff.contDiffAt.comp 0 h.paid,fun j hj y p=>?_⟩
 change ‖iteratedFDeriv ℝ j (L ∘ F) 0 y‖≤_; rw [L.iteratedFDeriv_comp_left (f:=F) h.paid (Nat.cast_le.mpr hj)]; change ‖i* iteratedFDeriv ℝ j F 0 y‖ ≤ _; rw [norm_mul,hy,one_mul]; exact h.token _ hj _ p
lemma sig0 {G:tangD n→ℂ}(p:Signs B o G c):‖G 0‖≤ c:=by simpa using p.token 0 (by omega) Fin.elim0 (fun i=> Fin.elim0 i)
lemma sent(V:Pane n)(k:Finset (Dwell n)→ℝ)(x y:Rock n)(t:BedP B V F X k)(h:pingS B.threshold Ω V)(hp:∀ z,0≤k z)(i j:SU.Slot): Signs B o (crib F x y i j ∘ increment V) (crack k x y):=by
 let l : Dwell n:=(true,x,i); let r: Dwell n:=(false,y,j); let Q:=k {l,r}; have he: Q ≤ crack k x y:=(single_le_sum (f:=fun v:SU.Slot=>k {l,(false,y,v)}) (fun i _=>hp _) (mem_univ j)).trans (single_le_sum (f:=fun i:SU.Slot=> ∑ j:SU.Slot,k {(true,x,i),(false,y,j)}) (fun i _=> sum_nonneg fun j _=>hp _) (mem_univ _)) -- tune inferred i
 have hg: crib F x y i j ∘ increment V=fun w=> parity l {r}*crumb (F (increment V w)).val {l,r}:=funext fun w=>(port_eq (F (increment V w)).val l r).trans (if_neg (by unfold l r; simp)); rw [hg]
 obtain ⟨g,u,hx⟩:=scale_left (t h {l,r}) (parity l {r}) (by simp [parity]); exact ⟨g.trans he,u,fun i j k p=>(hx i j k p).trans he⟩
end YM.CF.Prism

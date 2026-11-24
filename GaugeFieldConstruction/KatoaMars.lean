import GaugeFieldConstruction.RicciMars
/-!
# transcribing symmetries. Tables constructed at all Conf.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C) (Y:AreaQc S)
local notation "T"=> BellTableMars p Y
local notation "M"=> TerraMars p Y
-- proof actual later
structure FirstPackMars (p:Ticket u C)(Y:AreaQc S):Prop where
 clean (F:Fin 0→ΧiMars)(x:Points 0): TerraMars p Y F x=1
 coin {n:ℕ}(F:Fin n→ΧiMars) x(h:x∈conf (n+1)): TerraMars p Y (Fathom.add (Empire.one four) F) x=TerraMars p Y F (Points.tail x)
 spin {n:ℕ}(s:Signed)(F:Fin n→ΧiMars) x(h:x∈conf n):TerraMars p Y (spinFrame four s ∘ F) (NSF.Points.move s.ortho x)=TerraMars p Y F x
 shade {n:ℕ}(F:Fin n→ ΧiMars) x(h:x∈ conf n): TerraMars p Y (Calibration.shade four ∘ F) x= star (TerraMars p Y F x)
 symm {n:ℕ}(s:Equiv.Perm (Fin n))(F:Fin n→ΧiMars) x(h:x∈conf n): TerraMars p Y (F ∘ s) (NSF.Points.rearrange s x)=TerraMars p Y F x
 even {n:ℕ}(t:E4)(F:Fin n→ΧiMars) x(h:x∈conf n): TerraMars p Y F (NSF.Points.across t x)=TerraMars p Y F x
namespace FirstPackMars
open Points (direction)
-- symmetry pool list
lemma turnPoolMars {U:Set (Points n)}(u:IsOpen U)(F:Points n→ℂ)(h:ContDiffOn ℝ ∞ F U)(x:Points n)(e:x∈U)(l r:List (Points n))(j:l.Perm r): PoolDMars l F x=PoolDMars r F x:=by
 induction j generalizing x with
 | nil=>rfl
 | cons i _ h'=>exact GermD i ((u.eventually_mem e).mono h')
 | swap a b l=> exact commuteD ((poolSmMars l _ _ ((h x e).contDiffAt (u.mem_nhds e))).of_le (show (((2:ℕ):WithTop ℕ∞))≤ ∞ from WithTop.coe_le_coe.mpr le_top)) .. -- tune
 | trans j i h t=> exact (h x e).trans (t x e)
lemma MirrorPoolMars (G:Points n→ℂ) (F:Points m→ℂ) (A:Points n→Points m)(L:Points n→L[ℝ]Points m)
    (h:ContDiffOn ℝ ∞ F (conf m))(e:MapsTo A (conf n) (conf m))(v: EqOn G (F∘ A) (conf n))(g:∀ x,HasFDerivAt A L x) (l: List (Points n))(x:Points n)(hx:x∈conf n): PoolDMars l G x= PoolDMars (l.map L) F (A x):=by
 induction l generalizing x with
 | nil=> exact v hx
 | cons i s hs=>
    let W:= PoolDMars (s.map L) F
    have ht:PoolDMars s G=ᶠ[𝓝 x] W ∘ A:= ((conf_open _).eventually_mem hx).mono hs
    rw [poolHeadMars,GermD i ht,D, fderiv_comp x ((poolSmMars _ _ _ ((h _ (e hx)).contDiffAt ((conf_open _).mem_nhds (e hx)) )).differentiableAt (by simp)) (g x).differentiableAt,(g x).fderiv]; rfl
lemma PayTurnsMars (d:NSF.Caps n)(ρ:LabelsMars d) (A:Points n→L[ℝ]Points m):
  ((τGuideMars ρ).map guideDirMars).map A=(List.ofFn (fun i:Fin n=> ((railMars i (maskMars ρ i).2).map guideDirMars).map A)).flatten :=by unfold τGuideMars LineMars; rw [List.map_flatten,List.map_flatten,List.map_ofFn,List.map_ofFn]; rfl
lemma payRailsMars {d:ℕ}(k:Fin n) (w:TrailsMars d): (railMars k w).map guideDirMars=List.ofFn (n:=w.1.val) (fun i=>guideDirMars (k,w.2 i)):=List.map_ofFn ..
lemma payGuideMars (d:NSF.Caps n)(ρ:LabelsMars d) : (τGuideMars ρ).map guideDirMars=(List.ofFn (fun i=> (railMars i (maskMars ρ i).2).map guideDirMars)).flatten :=by unfold τGuideMars LineMars; rw [List.map_flatten,List.map_ofFn]; rfl
variable {p Y}(H: FirstPackMars p Y)
-- reindex Perm
abbrev reindexMars {d:NSF.Caps n}(ρ:LabelsMars d) (s:Equiv.Perm (Fin n)): LabelsMars (d ∘ s):= fun i=>ρ (s i)
def rePickMars (d:NSF.Caps n)(s:Equiv.Perm (Fin n)): LabelsMars d≃ LabelsMars (d∘s):= -- tune
    (Equiv.piCongrLeft (fun i=> LabelMars (d i)) s).symm -- orientation
lemma reAtMars (d:NSF.Caps n)(s:Equiv.Perm (Fin n))(ρ:LabelsMars d): rePickMars d s ρ = reindexMars ρ s:=by rfl
lemma clipMars (s:Equiv.Perm (Fin n))(d:NSF.Caps n)(ρ:LabelsMars d): τCoreMars (d:=d∘s) (reindexMars ρ s)=(τCoreMars ρ) ∘ s:=rfl
lemma placedMars (s:Equiv.Perm (Fin n))(d:NSF.Caps n)(ρ:LabelsMars d): ((((τGuideMars ρ).map guideDirMars).map (NSF.Points.arrangeL s))).Perm ((τGuideMars (d:=d∘s) (reindexMars ρ s)).map guideDirMars):=by
 let X(i: Fin n):= (((railMars i (maskMars ρ i).2).map guideDirMars).map (NSF.Points.arrangeL s))
 rw [PayTurnsMars,payGuideMars]
 have h : ∀ i:Fin n,(railMars i (maskMars (d:=d∘s) (reindexMars ρ s) i).2).map guideDirMars=X (s i):=by
    intro i; unfold X; rw [payRailsMars,payRailsMars,List.map_ofFn]; congr 1; ext1 j
    change guideDirMars (i,_)=NSF.Points.arrangeL s (guideDirMars (_,_))
    change guideDirMars (i,(maskMars ρ (s i)).2.2 j)=NSF.Points.arrangeL s (guideDirMars (s i, (maskMars ρ (s i)).2.2 j))
    generalize hz : (maskMars ρ (s i)).2.2 j=J -- lhs syntax maybe
    unfold guideDirMars; simp only; obtain ⟨a,b⟩:=J; cases b -- tune
    · simp only[Bool.false_eq_true,↓reduceIte]; exact (NSF.Points.directed s i a).symm
    simp only [↓reduceIte,map_neg]; exact congrArg Neg.neg ((NSF.Points.directed s i a).symm)
 simp_rw [h]; exact (s.ofFn_comp_perm X).flatten.symm -- tune.
include H
lemma placardMars (s:Equiv.Perm (Fin n))(d:NSF.Caps n)(ρ:LabelsMars d) (x:Points n)(hx:x∈conf n):
 ChartPriceMars p Y (reindexMars ρ s) (NSF.Points.rearrange s x)=ChartPriceMars p Y ρ x:=by
 let k:= NSF.Points.arrangeL s; let F:=TerraMars p Y (τCoreMars (reindexMars ρ s))
 have he:EqOn (TerraMars p Y (τCoreMars ρ)) (F ∘ k) (conf n):=fun i e=> (H.symm s (τCoreMars ρ) i e).symm
 symm; refine (MirrorPoolMars (TerraMars p Y _) F k k (TerraSm p Y _) (fun i e=>NSF.Points.rearrange_in s e) he (fun i=> k.hasFDerivAt) ((τGuideMars ρ).map guideDirMars) x hx).trans ?_
 exact turnPoolMars (conf_open _) F (TerraSm p Y _) (k x) (NSF.Points.rearrange_in s hx) _ _ (placedMars s d ρ)
lemma placedValueMars (s: Equiv.Perm (Fin n))(d:NSF.Caps n)(v:ChartVuMars d)(x:Points n)(h:x∈conf n):
    ((T).value (d∘s) (NSF.Points.rearrange s x)) (fun i=>v (s i))=((T).value d x) v :=by
 rw[TaxApplyMars,TaxApplyMars]; symm; exact Fintype.sum_equiv (rePickMars d s) _ _ (fun i=> by
    rw [reAtMars,placardMars H s d i x h]; unfold ChartTaxMars; exact congrArg (· *_) ((Equiv.prod_comp s fun j=>v j (i j)).symm))
lemma SymHallMars : NSF.Table.Symmetric T where
    same s x h w:= placedValueMars H s (fun i=>(w i).1) (fun i=>(w i).2) x h
#print axioms SymHallMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric

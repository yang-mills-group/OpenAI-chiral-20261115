import YM.CF.Vale.Bob
import YM.CF.Vale.Spur
import YM.CF.Brace.Quartz
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef Hom Push.SectorMeasure Next.SectorChange
open MeasureTheory Metric Skye Scree Grace Pastry RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {K: Pressure.Teller group}{P:RG.Patch}{R:ChartRatio group}{W:Postal}{η e:ℝ}{n k v i:ℕ}{f g a b d w:ℝ}{B m c u:Side}{C:Credit}
variable {X:Grace K P R}{U: Pricing K.j P.L P.odd_side (Vault.Thread K.j)} {D:Grasp U B e}{S:Gold K P R W}{x y z:ℝ}
section
lemma sign_nil(p:BudgetPoint)(i:Seat c):Signs p i (0:Scree.tangD c→ℂ) 0:=by
 refine ⟨le_rfl,(show ContDiff ℝ _ (0:Scree.tangD c→ℂ) from contDiff_const).contDiffAt,fun j h k v=>?_⟩; simp -- tune
lemma rinse(X:Hub c)(p:BudgetPoint)(q:ℝ): PressB p X 0 q 0:=by
 refine ⟨fun U V _=>rfl,fun _=> Flour.trivial,measurable_const,fun _ _=>Eq.symm (map_zero _), ⟨0,fun i=>le_rfl,fun U h s=>?_,?_⟩⟩
 · convert! sign_nil p X.val.1 -- tune
 simp
lemma rinsed(Y:Force c)(p:BudgetPoint)(q:ℝ):ForceB p Y 0 q 0:=by
 refine ⟨fun V W x y e f=>rfl,fun _=> Flour.trivial,fun _=>rfl,measurable_const,fun _ h=>False.elim (h rfl),fun _ _ _=>Eq.symm (map_zero _),⟨0,fun _=>le_rfl,fun U p S=> ?_,?_⟩⟩
 · convert! sign_nil _ Y.val.1.val.1
 simp
lemma lye(Q:Sweep c→Prop)(p:BudgetPoint)(q:ℝ): Scree.IncX Q 0 p q 0 ∧ Dark Q 0 p q 0:=⟨⟨⟨0,fun t=>rinse ..,fun i=>by simp [BudgetPoint.mass]⟩,fun S _ _ _ _ _=>Eq.symm (map_zero _)⟩,⟨⟨0,fun i=>rinsed ..,fun i=>by simp [BudgetPoint.mass]⟩,fun S _ _ _ _ _ _ _=>Eq.symm (map_zero _)⟩⟩
lemma still_Footprint (p:BudgetPoint)(V:Pane c):exponentL p 0 V=0:=by unfold exponentL; refine Finset.sum_eq_zero fun i _=>?_; simp [numbE]
lemma still_force (p:BudgetPoint)(V:Skye.Orbit c)(h: flags p.threshold V.1≠∅): fueled p 0 V=0:=by
 unfold fueled; refine Finset.sum_eq_zero fun i _=>?_ ; split_ifs with hv
 · obtain ⟨g,w⟩:= Finset.nonempty_iff_ne_empty.mpr (show i≠∅ from fun e=> by have he:=hv.1; rw [e] at he; exact h (by simpa [coverF] using he.symm)); exact prod_eq_zero w (by simp [clamp])
 exact rfl
-- bare mask, not claiming a continuum limit of this
local notation "N"=> (CSide m B)
variable (A:Gold K P R W)(β:ℝ)(q:BudgetPoint)
def launch(n:Side):GramM n:= ⟨q,A.path 0,K.top.clip,β,vanilla n,0,0,0,0⟩
lemma wing_h : Girt.Ward (launch A β q c):= ⟨⟨_,_,_,A.mood 0⟩,fun i=>⟨0,0,rinse ..⟩,fun i=>⟨0,0,rinse ..⟩,fun i=> ⟨0,0,rinsed ..⟩⟩
variable (D)
def capP (U:Pane N):Phys N:= Set.indicator {U|flags q.threshold U=∅} (fun x:Pane N=>Complex.exp (-((β*basicP K.top.clip x:ℝ):ℂ)) • changeM D x babyM) U
lemma pig_b (T:Pane c): Pec.pigment (0:Pride c) T=0:=by
 unfold Pec.pigment Pec.lexn Pec.zinger Pec.tag; simp [Pec.pays]; -- tune
lemma vanilla_K (X:Pane c): (vanilla c).P.den X=0:=by change colorX (k:=1) 0 X+colorX (k:=2) 0 X=_; rw [empty_field, empty_field]; exact add_zero _
lemma curtain (l:ℕ)(T:Scree.Loom N)(h:Roof N x e l T)(t:D.roundZ ≤ (CSide m B).val) -- fix
 (u:Pane N):relV D (vanilla _) u= changeM D u babyM:=by
 unfold relV; simp_rw [vanilla_K,capT]; rw [mul_zero,zero_mul, show dg (0:Op (Single N))=0 from ?_, NormedSpace.exp_zero]; exact act_one _
 ext; simp [dg,dyad] -- tune
lemma core_b (l:ℕ)(T:Scree.Loom N)(h:Roof N x e l T)(t:q.threshold ≤ x)(p:K.top.clip.direct ≤1)(k:D.roundZ≤ (CSide m B).val): ∀ V:Skye.Orbit N,denZ (launch A β q N) D T V=capP (K:=K) D β q V.1:=by
 intro V; let Z:= spar K.j babyM (T V); have hz:IsStarProjection Z:= (D.broadness _ k _).projection _ (h.paid _)
 unfold denZ GramM.betaL -- wrong order
 by_cases v: flags q.threshold V.1=∅
 · unfold capP; rw [Set.indicator_of_mem (show V.1∈ _ from v)]
   have he:flags x V.1=∅:=by
     rw [← Finset.subset_empty]; intro i hi; obtain ⟨p,w,u⟩:= (flags_spec ..).mp hi; exact v ▸ ((flags_spec ..).mpr ⟨p,w,t.trans_lt u⟩)
   have hv:T V=V.1:=funext fun v=>h.lamp V.1 V.2 v (by simp [he]); have hi:(launch A β q N).board V=1:=by
      unfold GramM.board; rw [show (launch ..).F=(0:RegBudget N) from rfl,show (launch ..).slip=(0:RegBudget N) from rfl]; rw [still_Footprint, add_zero, NormedSpace.exp_zero,one_mul]; exact fuel_one _ _ _ v
   -- order
   rw [hi,show (launch A β q N).J.I=0 from rfl,pig_b]; have ha: tank Z 1=1:=by rw [tank_eq Z _ hz]; apply map_one
   rw [show spar K.j (launch A β q N).J.M (T V)= Z from rfl,ha, act_one, show (launch A β q N).J= vanilla _ from rfl, curtain D l T h k,hv]
   unfold GramM.H0 launch; simp only [A.born, plainB _ p _ _ _ v]; rw [zero_sub,sub_zero]
 unfold capP; rw [Set.indicator_of_notMem (show V.1∉_ from v)]; have ht:(launch A β q N).board V=0:=by unfold GramM.board; rw [show fueled (launch A β q N).p (launch A β q N).K V= _ from still_force q V v, mul_zero]
 rw [ht,show spar K.j (launch A β q N).J.M (T V)= Z from rfl, tank_eq _ _ hz,map_zero, act_zero, smul_zero]
end
end YM.CF.Vale

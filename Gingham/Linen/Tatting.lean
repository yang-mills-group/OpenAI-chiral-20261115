import YM.CF.Ione.Lean
noncomputable section
set_option autoImplicit false

/-- Same budget point except add one unit in mass charge. -/
def YM.RG.BudgetPoint.raisin (p: YM.RG.BudgetPoint) : YM.RG.BudgetPoint :=
 {p with supportExponent:= p.supportExponent+1, exponent_pos:= add_pos p.exponent_pos zero_lt_one}
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Linen
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Ione

/-! # Eventually polynomial in 1+b -/

structure PolyBill (f : ℕ→ℝ) : Prop where
  positive : ∀ b, 0 ≤ f b
  slope : ∃ C≥(1:ℝ), ∃d:ℕ, ∀ b, f b ≤ C*(1+(b:ℝ))^d

namespace PolyBill
variable {f g : ℕ→ℝ}

lemma vanish : PolyBill (fun _=> 0):=⟨fun _=>le_rfl,1,le_rfl,0,fun _=>by simp⟩

lemma const {c:ℝ}(p:0≤c) : PolyBill (fun _=> c) :=
 ⟨fun _=>p,max 1 c,le_max_left ..,0,fun _=>by simp⟩

lemma mid : PolyBill (fun b=> (b:ℝ)) :=
 ⟨fun b=>Nat.cast_nonneg _,1,le_rfl,1,fun _=>by simp⟩

lemma shrink (p:PolyBill f) (k:∀ b,0≤g b) (h: g ≤ f) : PolyBill g := by
 obtain ⟨C,l,d,a⟩:=p.slope

 exact ⟨k,C,l,d,fun i=>(h i).trans (a i)⟩

lemma plus (p:PolyBill f)(q:PolyBill g) : PolyBill (fun b=> f b+g b):=by
 obtain ⟨C,l,d,a⟩:=p.slope
 obtain ⟨C',l',d',a'⟩:=q.slope
 refine ⟨fun b=>add_nonneg (p.positive ..) (q.positive ..),C+C',by linarith,max d d',fun b=>?_⟩
 rw [add_mul]
 apply (add_le_add (a b) (a' b)).trans
 have hb : 1≤(1:ℝ)+(b:ℝ):=le_add_of_nonneg_right (by positivity)
 gcongr
 · exact le_max_left ..
 exact le_max_right ..

lemma mul (p:PolyBill f)(q:PolyBill g) : PolyBill (fun b=> f b*g b):=by
 obtain ⟨C,l,d,a⟩:=p.slope
 obtain ⟨C',l',d',a'⟩:=q.slope
 refine ⟨fun b=>mul_nonneg (p.positive ..) (q.positive ..),C*C',one_le_mul_of_one_le_of_one_le l l',d+d',fun b=>?_⟩
 exact (mul_le_mul (a b) (a' b) (q.positive b) (mul_nonneg (zero_le_one.trans l) (by positivity))).trans_eq (by rw [pow_add]; ring)

lemma expN (p:PolyBill f) (k:ℕ): PolyBill (fun b=> f b^k):=by
 induction k with
 | zero=> simpa only [pow_zero] using const (@zero_le_one ℝ _ _ _ _)
 | succ k h=> simp only [pow_succ]; exact h.mul p
end PolyBill

-- all on Sour/Scree Hubs; no assertions about Strong W
variable {n:Side} {p:BudgetPoint} {X:Scree.Hub n} {h c:ℝ}

abbrev sizeB (p:BudgetPoint) (i:Scree.Hub n) := coverNumber p.B i.val.2
abbrev minusO (x:Cipher n) := x - Pastry.hollow (n:=Dwell n) (Pastry.pane x)
def frosting (F : RegBudget n) : RegBudget n := fun X V=>minusO (F X V)

def Glazes (F:RegBudget n)(p:BudgetPoint)(h:ℝ)(k:ℕ)(x:ℝ) : Prop :=
 ∃ J:RegBudget n, IncX Ione.Utrue J p.raisin h x ∧ ∀ X, k<sizeB p X→ frosting J X=frosting F X


variable (x y: Cipher n)

lemma surf (i:Finset (Dwell n)) : crumb (minusO x).val i=if i=∅ then 0 else crumb x.val i:=by
 change ((x.val) i ∅ - (pane x • (1:FC (Dwell n))) i ∅) = _
 rw [Matrix.smul_apply,Matrix.one_apply]
 split
 · next h=> subst i; exact sub_eq_zero.mpr (smul_eq_mul _ _ |>.trans (mul_one _)).symm
 simp [crumb]

-- do sum maneuver generically, avoid deep whnf when rewriting
private lemma paint_rows {α:Type} [Fintype α] [DecidableEq α]
    (W:α→α→ℂ) (u:Bool) (v:α→ℂ) (e i:α)
    (p:∀ i, i≠e → W e i=0)
    (q:∀ i, i≠e → W i e=0) :
   (if i=e then 0 else ∑ j,W i j*cSignX u (v j))=∑ j,W i j*cSignX u (if j=e then 0 else v j) := by
 split
 · rename_i h
   subst i; symm
   apply sum_eq_zero; intro j _
   split_ifs with g
   · rw [sign0,mul_zero]
   rw [p j g,zero_mul]
 rename_i h
 apply sum_congr rfl; intro j _
 by_cases u:j=e
 · subst j; rw [q _ h]; simp
 rw [if_neg u]

lemma surf_paint (a b:Bool)(T : UNI (Tulip.Single n)) :
    minusO (paintR a b T x)=paintR a b T (minusO x) := by
 let A:= minusO (paintR a b T x); let B:=paintR a b T (minusO x)
 apply Subtype.ext
 change A.val=B.val
 calc
   _ = ∑ i,crumb A.val i • Pastry.poke i:=(fineShape A).allP
   _ = ∑ i,crumb B.val i • Pastry.poke i:=?_
   _ = B.val:=(fineShape B).allP.symm
 apply sum_congr rfl; intro i v; congr 1
 unfold A B
 rw [surf, cribP, cribP]
 simp_rw [surf]
 apply paint_rows
 · intro v hv
   exact quant_grade _ _ _ (Ne.symm (by simpa using hv))
 intro v hv; exact quant_grade _ _ _ (by simpa using hv)

lemma icing : Continuous fun z:Cipher n=>minusO z := by
 have hf:Continuous (fun z:Cipher n=> z.val ∅ ∅):=by
    change Continuous (fun z:Cipher n=>(fun A:FC (Dwell n)=>A ∅ ∅) z.val)
    exact (continuous_id.matrix_elem ..).comp continuous_subtype_val
 have hu : Continuous (fun z:ℂ=> Pastry.hollow (n:=Dwell n) z):=
    Continuous.subtype_mk (continuous_id.smul continuous_const) _
 exact continuous_id.sub (hu.comp hf)

lemma with_flour {S:Finset (Dwell n)} (y:Flour S x.val): Flour S (minusO x).val := by
 change Flour S (x.val - pane x • _)
 rw [sub_eq_add_neg,←neg_smul]
 exact y.add (Flour.grainE.smul _)

variable {F:RegBudget n}
lemma frost (t:PressB p X (F X) h c): PressB p X (frosting F X) h c where
 term U V q:=congrArg minusO (t.term U V q)
 fitted U:= with_flour _ (t.fitted U)
 measureV:= icing.measurable.comp t.measureV
 gaugeV U g:= (congrArg minusO (t.gaugeV U g)).trans (surf_paint ..)
 worth:=by
   obtain ⟨v,a,l,k⟩:=t.worth
   refine ⟨v,a,fun U h i=>?_,k⟩
   have eq:(fun z=> crumb (frosting F X (increment U z)).val i)= if i=∅ then (fun _=>0) else (fun z=> crumb (F X (increment U z)).val i):=by
     ext z; rw [show frosting F X (increment U z) = minusO (F X (increment U z)) from rfl, surf]
     split <;> rfl
   rw [eq]; split
   · refine ⟨a _,contDiffAt_const,fun j p k _=>?_⟩
     simpa using a i
   exact l U h i

lemma frost_sweeps (t:IncX Utrue F p h c) (s:Sweep n) (U : _) (g : JetS s.s s.charge (detX s.s) U) :
    ∀ X: Scree.Hub n,∀ V:Pane n, frosting F (moveHub s X) (flashA s V)=paintR s.charge (detX s.s) (prepU (castX s) U (xtra s.charge) n) (frosting F X V) := by
 intro X V; exact (congrArg minusO (t.face s trivial U g X V)).trans (surf_paint ..)


lemma minusO_zero : minusO (0:Cipher n) = 0 := Subtype.ext (show 0 - ((0:ℂ) • (1:FC (Dwell n))) = 0 by simp)

lemma minusO_add : minusO (x+y)=minusO x+minusO y := by
 apply Subtype.ext
 change x.val+y.val - ((x.val ∅ ∅+y.val ∅ ∅) • 1)=(x.val - (x.val ∅ ∅) • 1)+(y.val - (y.val ∅ ∅) • 1)
 rw [add_smul]; abel

lemma minusO_crown {x:Cipher n}(t:ℂ)(p:x.val=t • 1) :minusO x=0:=by
 apply Subtype.ext; change x.val - x.val ∅ ∅ • 1=0; rw [p]
 simp [Matrix.smul_apply]

def Zaffre (F:RegBudget n) (p:BudgetPoint)(k:ℕ) : Prop :=
 ∀ X, k<sizeB p X → frosting F X=0

lemma Zaffre.sweet {k:ℕ}{Z:RegBudget n} (e:Zaffre Z p k)(F:RegBudget n)
    (t: k<sizeB p X): frosting (Z+F) X=frosting F X :=by
 funext V; change minusO (Z X V+ F X V)=_
 have h:minusO (Z X V)=0:=congrFun (e X t) V
 rw [minusO_add,h,zero_add]; rfl


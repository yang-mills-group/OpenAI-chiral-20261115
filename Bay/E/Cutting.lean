import Bay.E.Sample

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell


namespace Silk
open Buffered Lifted D StressExchange

open Buffered.Afterglow.Tower SlabMark
open Girt
open scoped YM.CF.Buffered

local notation "Ways" => Buffered.Family

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow Journey Tower Tapestry VacuumSelection
local notation "VΩ"=>VacuumSelection.Spine
set_option maxRecDepth 5000


variable {S:Finset Cover}{K:Calibration}{o:Cover}{b:ℕ}
local notation "S₀"=>Band o b


lemma qbHue {r:ℕ→Ways K}{f:Ways K}(h:BQueue S r f)
  (v:∀ᶠ i in atTop, Neutral K (r i)):Neutral K f:=by
 intro n g x
 have u(y): Tendsto (fun i=>r i n y) atTop (𝓝 (f n y)):=by
   refine Metric.tendsto_nhds.mpr fun ε p=> ?_
   filter_upwards[h.saved (ε/2) (by positivity)] with i t
   rw[dist_eq_norm];exact lt_of_le_of_lt (t n y) (half_lt_self p)
 exact tendsto_nhds_unique_of_eventuallyEq (u _) 
   (((by rw[show (⇑(twist (quantU (tradew (K.c n) g))))=(fun x=> (quantU (tradew (K.c n) g)).val * x * star (quantU (tradew (K.c n) g)).val) from funext (twist_formula _)]; fun_prop):Continuous ⇑(twist (quantU (tradew _ g)))).continuousAt.tendsto.comp (u _))
   (v.mono fun i h=>h n g x)

lemma coolAdd{f g:Ways K} (h: Neutral K f)(u:Neutral K g):Neutral K (f+g):=by
 intro m y x
 simp only[Pi.add_apply,h m y x,u m y x,map_add]
lemma coolSc {f:Ways K} (h: Neutral K f)(z:ℂ):Neutral K (z • f):=by
 intro m y x; simp only [Pi.smul_apply,h m y x,twist_scalar]
lemma coolFin{ι:Type}{g:ι→Ways K}(p:∀i,Neutral K (g i))(S:Finset ι):Neutral K (∑i∈S,g i):=by
 classical
 induction S using Finset.induction_on with
 | empty=> rw[sum_empty];exact fun n y x=>(map_zero _).symm
 | insert i _ h ih=>rw[sum_insert h];exact coolAdd (p i) ih

def flap (K:Calibration)(o:Cover)(b:ℕ):Finset Cover:=
  let S:=Band o b
  S ∪ Finset.univ.biUnion (fun i:Axis=> plow K i 1 S∪plow K i (-1) S)

variable (K) (q τ:ℝ)
abbrev zest(f:Silo Axis o b):Ways K:= ((q/τ^2:ℝ):ℂ) • nips K f
abbrev jest(f:Silo Axis o b)(i:Axis):Ways K:= (q:ℂ) • wing K f i
abbrev swerve(f:Silo Axis o b)(i j:Axis)(t:ℤ):Ways K:= relocate K i t (jest K q f j)
abbrev yieldY(f:Silo Axis o b): Ways K:=
 zest K q τ f+ (↑((τ^2)⁻¹:ℝ):ℂ) • (∑ i:Axis, (swerve K q f i i 1- swerve K q f i i (-1)))

variable {L t d:ℝ}{r:ℕ→Silo Axis o b}{f:Silo Axis o b}
lemma yieldsX (z:Hangs t d L r f):
 BQueue S₀ (fun n=>zest K q τ (r n)) (zest K q τ f)∧
 (∀j,BQueue S₀ (fun n=>jest K q (r n) j) (jest K q f j))∧
 BQueue (flap K o b) (fun n=>yieldY K q τ (r n)) (yieldY K q τ f):=by
 have B:=z.bloom K
 let v:=qbScale ((q/τ^2:ℝ):ℂ) B.1
 let J:=fun i=>qbScale (q:ℂ) (B.2 i)
 refine ⟨v,J,qbPlus (qbWider v (show S₀ ⊆ flap K o b from subset_union_left)) (qbScale (F:=fun n=>∑ i:Axis, (swerve K q (r n) i i 1 - swerve K q (r n) i i (-1))) (↑((τ^2)⁻¹:ℝ)) ?_)⟩
 apply qbSum; intro i _
 have y(f g:Ways K) : f-g=f+(-1:ℂ)•g:=by rw[neg_one_smul,sub_eq_add_neg]
 simp_rw[y]
 have hx:plow K i 1 S₀∪ plow K i (-1) S₀ ⊆ flap K o b:=
   (show plow K i 1 S₀∪ plow K i (-1) S₀ ⊆ Finset.univ.biUnion fun i=>plow K i 1 S₀ ∪plow K i (-1) S₀ from subset_biUnion_of_mem (fun i=>plow K i 1 S₀∪plow K i (-1) S₀) (mem_univ i)).trans subset_union_right
 exact qbPlus (qbWider ((J i).station i 1) (subset_union_left.trans hx))
   (qbScale _ (qbWider ((J i).station i (-1)) (subset_union_right.trans hx)))

#print axioms yieldsX
#print axioms yieldY
lemma coolZ(h:Hangs t d L r f)
 (u:∀n, Neutral K (nips K (r n))∧∀j,Neutral K (wing K (r n) j)):
 Neutral K (zest K q τ f)∧(∀j,Neutral K (jest K q f j))∧Neutral K (yieldY K q τ f):=by
 let p:=yieldsX K q τ h
 let v:=qbHue p.1 (Eventually.of_forall fun i=>coolSc (u i).1 _)
 let m:∀ j,Neutral K (jest K q f j):=fun j=> qbHue (p.2.1 j) (Eventually.of_forall fun i=> coolSc ((u i).2 j) _)
 refine ⟨v,m,coolAdd v (coolSc (coolFin ?_ _) _)⟩
 intro i
 rw [sub_eq_add_neg,←neg_one_smul ℂ]
 exact coolAdd (chime_cov _ _ _ (p.2.1 i|>.landing) (m i)) (coolSc (chime_cov _ _ _ (p.2.1 i|>.landing) (m i)) _)

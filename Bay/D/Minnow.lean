import Bay.D.Spark
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

namespace D
open Exterior Precision Nacre
open scoped ContDiff

open Carol Zephyr.Chern
-- uniform on stencil of that fixed width and cover center, including
-- H about the matter center (which needn't fix the block centered
-- geometrically one off).
open Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
local notation "VΩ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine
abbrev minnow(P:VΩ)(s i k m:ℕ)(a:Signed)(l:List Axis)(x y:Cover):ℝ→ℂ:=
    spout (fun z=> (regW P s i k z-tickA _) * scatter (wrap _ x) a m l (wrap _ y))
     (Zephyr.Chern.stream _)
lemma fry₀(P:VΩ)(s i k m:ℕ)(a:Signed)(x y:Cover):
    minnow P s i k m a [] x y=caul P s i k m [] (x+a.act y):=by
   funext z
   simp only [caul,minnow,spout,scatter,squareSum,playW,map_add,←wrap_signed]
lemma fry₁(P:VΩ)(s i k m:ℕ)(a:Signed)(d:Axis)(l:List Axis)(x y:Cover):
    minnow P s i k m a (d::l) x y=fun z=>∑ j∈range (2*m),minnow P s i k m a l x (nearCover y d m j) z:=by
   funext z
   simp only [minnow, spout, scatter,squareSum,stripSum,mul_sum, Matrix.trace_sum,wrapNear]

lemma northM(P:VΩ)(m:ℕ)(t:0 < m)(a:Signed)(l:List Axis)(x y:Cover):
   ∃δ, (0:ℝ)<δ ∧ ∀ᶠ s:ℕ in atTop,∀ i k,gem (minnow P s i k m a l x y) δ:=by
 induction l generalizing y with
 | nil=>
    simp only [fry₀]
    exact goldCup P m t [] _
 | cons j l ih=>
    let D:=range (2*m)
    have h:D.Nonempty:=⟨0,mem_range.mpr (by omega)⟩
    choose z p f using (fun v=>ih (nearCover y j m v))
    refine ⟨∑ v ∈ D,z v,sum_pos (fun i _=>p _) h,?_⟩
    filter_upwards [(eventually_all_finset D).mpr (fun v _=>f v)]
      with s hv i k
    rw[fry₁]; exact gemSum D h _ _ fun w v=> hv _ v i k
theorem starrySky(P:VΩ)(m:ℕ)(t:0 < m)(x:Cover):
   ∃δ,(0:ℝ)<δ ∧ ∀ᶠ s:ℕ in atTop,∀ i k a, gem
     (spout (play (wrap _ x) a m (regW P s i k)) (Zephyr.Chern.stream _)) δ:=by
 choose z q g using fun a=>northM P m t a (List.ofFn (id:Axis→Axis)) x 0
 letI:Nonempty Signed:= ⟨1⟩
 let u:=univ.inf' univ_nonempty z
 have h:0<u:= (Finset.lt_inf'_iff ..).mpr (fun i _=>q _)
 refine ⟨u,h,?_⟩

 filter_upwards [eventually_all.mpr g] with s hs i k a
 have b:= hs a i k
 unfold minnow at b;rw [map_zero] at b
 exact ⟨b.1,(show u≤z a from inf'_le _ (mem_univ a)).trans_lt b.2⟩
end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.starrySky

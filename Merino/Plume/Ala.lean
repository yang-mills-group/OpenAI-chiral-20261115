import Merino.Plume.Miniver
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3500
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Plume
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Drapes Metric
open _root_.Zephyr.Chern
open scoped Matrix Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Finset Swell

variable {n:Side}

open Py.Rate.LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Skye Scree Vale RG
open Py (hueW stemS pinpr)
variable (P:Spine)


open Cuff Hem Medal Lace
open Buffered Lifted Afterglow Journey Tower Tower.SlabMark

lemma positiveCt (C:Constellation):0<Ct C:=div_pos (Lace.shines _ _ C.oa) (by norm_num)

/-- True moving-plane squared OS norm and its uniformly positive credit,
even though moving in the corridor. That lamp is nonempty.
All limits *before* selecting a character.
Nothing here preserves this question by restriction to a single fiber. -/
structure Ala (P:Spine)(p:Bolts)
 (C:Constellation)(r:ℕ→ℕ)(s:ℕ)(F:ℕ→LinksC→ℂ)(g:LinksC→ℂ):Prop where
  path:∀ᶠ j in atTop,warrant P p C s (P.nomadic (r j)) (P.engine (r j)) (F j)
  rolls: Plump (Lattice.box (etch P s)) p.c F g
  placed(t:ℕ):BQueue (wall P s t) (half P s t ∘ F) (half P s t g)
  lit: lamp P s
  stellar {t:ℕ} :Strut (scaleM P s) t→
   Way P s t ∧ CovCover P.calibration (half P s t g) ∧
   ∃V:P.Vox pole s, V.val=half P s t g ∧
    (P.E s (both P s t g)).re= ‖P.piece pole s V‖^2 ∧
    Ct C*cost₀ P s t^2 ≤ ‖P.piece pole s V‖^2

abbrev Hill (P:Spine)(p:Bolts)(C:Constellation):Prop:=
 ∃ (r:ℕ→ℕ), StrictMono r ∧ ∀ᶠ s:ℕ in atTop,∃ F g,Ala P p C r s F g


variable (p:Bolts)
lemma aiming (C:Constellation)(h:twinkling P p C.α C.δ C.bigE C.r C.L)(A:P.NightCop):Hill P p C:=by
 obtain ⟨r,F,g,k,l,h⟩:=chooseRibbon P p C h A
 refine ⟨r,k,?_⟩
 filter_upwards [clears P,h] with s i b
 let D:=F s∘r
 have w:=l s
 have u:=k.tendsto_atTop.eventually b.2
 refine ⟨D,g s,u,w,fun t=> w.stillHalf P t,b.1,?_⟩
 intro t z
 obtain ⟨e,q⟩:=entering P (i t z) (fat w)
 let V:P.Vox pole s:=⟨_,e⟩
 have v:(P.E s (both P s t (g s))).re= ‖P.piece pole s V‖^2:=vocal P V rfl
 refine ⟨i t z,q,V,rfl,v,le_trans ?_ v.le⟩
 have lim:= (Complex.continuous_re.continuousAt).tendsto.comp (combined P w t k)
 refine ge_of_tendsto lim ?_
 filter_upwards [u] with j h
 obtain ⟨_,d,_,⟨T,c⟩,_,y⟩:=h
 change Ct C*cost₀ P s t^2 ≤ (compass P.run (P.nomadic (r j)) (P.engine (r j)) s
       (photo (glance (RegNum P s (P.nomadic (r j))) t (clearM P s) (F s (r j))))).re
 rw [y t]
 exact c.christened z


/-- Paid on exactly the chosen law retaining phase registration and jet. -/
lemma snowpack (Y:Dazzles P p)(A:P.NightCop):
    ∃ C:Constellation,twinkling P p C.α C.δ C.bigE C.r C.L ∧ Hill P p C:=by
 obtain ⟨α,δ,E,r,L,d,n,e,v,l,w⟩:=Y.beams
 have z:= Lace.shines hueInk _ d
 let C:Constellation:=⟨α,δ,E,r,L,leadCoin hueInk α/2,d,n,e,v,l,by positivity,le_rfl⟩
 exact ⟨C,w,aiming P p C w A⟩
end YM.CF.Merino.Plume

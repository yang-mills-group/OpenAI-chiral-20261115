import Zephyr.Satellite
import Zephyr.Chern.Tile
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 700000
noncomputable section
namespace Zephyr.Chern
open YM Lattice CF Tulip Filter Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection

/-- The Gram's actual input chiral kernel. Argument *supplied* to the call
(where used under Loom the argument isn't in general an identity
expression in first Pane). Directional test, generator & flux in `petals`
and `stream`. -/
def sparSite (j:ℕ){N:Side}(m:Male)(z:Cover)(t:ℝ):ℂ:=
  ∑ i:IS,Dial.spar j m (petals (stream N) t) (tag N z i) (tag N z i)

structure SprigFee (P:Spine) :Prop where
  actual (z:Cover): ∃ δ:ℝ,0<δ ∧
    ∀ᶠ s in atTop,∀ i k,
      let f:=sparSite (N:=age P.run i s) P.par.K.j (blood P.run i k s) z
      ∀ c:ℂ,Bud (f+Function.const _ c) ∧ δ<(bud (f+Function.const _ c) 2).re
  angular (z:Cover):
    ∃ (a r e:ℝ),0<a ∧ 0<e ∧ ∃ δ:ℝ,0<δ ∧ ∃ w,
    ∀ᶠ s in atTop,∀ i k, let N:=age P.run i s
                          let X:=funde P.par.K.j (blood P.run i k s) N
                          Nonempty (Bough e a r X) ∧
                            ∀ (t:Bough e a r X) u,Holds u w →
                            δ < (bud (sprig (t.sift u) (stream N) z) 2).re

theorem SprigFee.paid (P:Spine): SprigFee P:=by
  have hj:= hOne P.par
  constructor
  · intro z
    obtain ⟨d,hd,v,T⟩:= deep_flux hj z
    obtain ⟨w,G⟩:=germ hj
    refine ⟨d,hd,?_⟩
    filter_upwards [age_above P.run v,age_above P.run w] with s a b i k _ c
    let f:=sprig (funde P.par.K.j (blood P.run i k s) (age P.run i s)) (stream _) z
    have h: Bud f:=G (b i) _ _ z
    have t:= h.bloom.add (Bloom.constant c)
    change Bud (fun x=>f x+c) ∧ d < (bud (fun x=>f x+c) 2).re
    rw [t.bud_eq]
    refine ⟨t.1,?_⟩
    change d < (bud f 2+0).re
    rw [add_zero]
    exact T (a i) _
  intro z
  obtain ⟨a,r,e,y,_,x,l,T⟩:=funde_s _ hj
  obtain ⟨d,hd,w,v,A⟩:= tiled_flux hj z y x r
  refine ⟨a,r,e,y,x,d,hd,w,?_⟩
  filter_upwards [age_above P.run v,age_above P.run l] with s p t i k
  exact ⟨bough_exists (T _ _ (t i)),fun g u m=>(A (p i) g m).2⟩

#print axioms SprigFee.paid
#print axioms deep_flux
#print axioms tiled_flux
#print axioms Spine.planet_with_124

import YM.SU5.Relativistic.Crotch
import YM.SU5.Assay.Proscenium
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 590000
noncomputable section
namespace YM.CF.Papyrus.Franc.Meshy
open Function Filter NormedSpace Metric Fock Finset Thera MeasureTheory Lattice Cube Lat Fir Rush SU Scroll Skye Tulip Flare BPress.Spin.Blank
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered
open Lifted Pea Omelet Afterglow Satin Pannier Pannier.Chancel Pannier.Chancel.ScreeV Cliplet RG Tenant Scree Loaves
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
open Py.Rate (sites)
open Afterglow.Tower Afterglow.Journey

open Tower.SlabMark Tower.SlabMark.Etch
variable {K:Calibration}{F X:Buffered.Family K}{S:Finset Cover}{m:Side}{a n k d b r:ℕ}
  {M:Tulip.Male}{s τ η μ C B:ℝ}{σ x l u:Cover}
local notation "g" F:max T:max q:max => Galop K F T q m k M d b s τ η μ C B

lemma Galop.house {w:ℤ}(hp:g F S 1)(j:Muster s (K.c m) M)(t:House K w σ 0 S)
    (v:Located K w σ F x X):∃ T:Finset Cover, House K w σ x T ∧ (g X T 1):=by
 induction v with
 | start=> exact ⟨S,t,hp⟩
 | reflect i q _ ih=> obtain ⟨T,v,p⟩:=ih; exact ⟨_,v.reflect K w σ i q,p.inverted _ _ j⟩
 | go i q _ ih=> obtain ⟨T,v,p⟩:=ih; exact ⟨_,v.go K w σ i q,p.migrate i _ j⟩

lemma Galop.panel {w:ℕ}(hp:g F S 1)(j:Muster s (K.c m) M)(t:House K w σ 0 S)
    (z:Proscenium K.B w (K.c m) r)(e:Hall r l u)
    (v:Panel K w σ F l u n X):∃T:Finset Cover,(g X T n):=by
 let W (x:Cover):= {p:Cover| ∃ S:Finset Cover, p∈S∧House K w σ x S}
 obtain ⟨L,rfl,h,P,rfl⟩:=v
 suffices ∃T:Finset Cover,(g (castings K L) T L.length)∧∀p∈T,∃x∈L,p∈ W x.1 from ⟨_,this.choose_spec.1⟩
 induction L with
 | nil=> exact ⟨∅,⟨[],rfl,empty_subset _,rfl,⟨by simp,by simp⟩⟩,by simp⟩
 | cons y L ih=>
   obtain ⟨e',t'⟩:=h y (List.mem_cons_self)
   obtain ⟨U,u,c⟩:=hp.house j t t'
   have hl:=fun i v => h i (List.mem_cons_of_mem y v)
   obtain ⟨m0,m1⟩:=List.pairwise_cons.mp P; obtain ⟨T,a,r⟩:=ih hl m1
   have D:Disjoint (region U (K.c m)) (region T (K.c m)):=by
     apply disjoint_left.mpr; intro x hx px
     obtain ⟨b,w,rfl⟩:=mem_image.mp px
     obtain ⟨y,v0,V,x',v1⟩:=r b w
     exact disjoint_left.mp (z.disjoint e e' (hl y v0).1 (m0 y v0) u v1) hx (mem_image_of_mem _ x')
   refine ⟨U∪T,by rw [List.length_cons,add_comm]; exact c.line a D,?_⟩
   intro p hp; rcases mem_union.mp hp with hp | hp
   · exact ⟨y,List.mem_cons_self,U,hp,u⟩
   obtain ⟨y,hm,v⟩:=r p hp; exact ⟨_,List.mem_cons_of_mem _ hm,v⟩

open Tapestry
/-- From one plaque Galop and torus pricing of tender to all checkers. -/
lemma Galop.mosaic {w:ℕ}(hp:g F S 1)(j:Muster s (K.c m) M)(t:House K w σ 0 S)
    (z:Proscenium K.B w (K.c m) r)
    (N:Side)(e:K.c m=N)(U:Mark N→ℂ)
    (h:∀L:List (Cliplet N 1), Battalion M k d b s τ η μ C B L→ ((Etch.ratio K.B w:ℕ):ℝ)⁻¹*sites N ≤ (L.length:ℝ) → ‖U (probe L)‖ ≤ Real.exp (L.length*(3*μ))):
    Mosaic w σ r F (Real.exp (3*μ)) (fun f=> U (Tapestry.arrange _ _ e (f m))):=by
 subst N
 intro _ _ n a b X y
 obtain ⟨T,u⟩:= hp.panel j t z b y
 obtain ⟨L,rfl,_,c,p⟩:=u.ticket
 change ‖U (X m)‖ ≤ _
 rw [←c,←Real.exp_nat_mul]
 exact h L p (z.density' a)
end YM.CF.Papyrus.Franc.Meshy

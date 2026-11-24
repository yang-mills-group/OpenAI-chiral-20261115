import YM.CF.BPress.Peel.Read
/-! Long tickets instantiated. Wide supports. Congruence of `$ρ.ψ` for heavy calls. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Peel
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Sugar.Crew Grid Env Bands Vesper Hazel Hazel.Letters Net Fock Spin Spin.Paint Habitat Meadow.Frame Meadow Meadow.Tent
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.L2Operator InnerProductSpace YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}{R: Hangar (More N)}
open Palmer Contour Along Sheet
variable {H: Sugar.Crew A} {t T S E P: Seal (BlockY A R)}{i : BlockY A R}{q : A.Index}{k r:ℕ}{X: Sugar.Stage N}
namespace Spine
lemma Arcing (x:mState N A): Set.EqOn (A.atmospheric (H.skyio x)) (H.port x) (A.air):=by
 let B:=H.skyio x; rw [← show A.skyH (H.port x)=H.skyio x from H.Z.roll_sky ..]; exact A.sky_air _ -- tune rewrites
variable {U:Support (More N)}{x y: Visit A R H}
abbrev halos (S : Seal (BlockY A R))(r:ℕ) := broad (shape A R) S r
theorem long_sp (Q:Host R H)(p:Floor A R H.Z (Magnified U X H) S)(t:Rights R B H.L H.y r): Spine H X U (halos S 6):=by
 let u(x:Visit A R H):=fU x.val
 let η:= Magnified U X H; have ht(x y:Visit A R H)(q:Along x.val y.val (halos S 6)) : Lattice.Agrees η (H.port (u x)) (H.port (u y)) ∧ ∀ i∈A.nc,∀ z∈ richT A η i, parseY H (u x) i z=parseY H (u y) i z :=by
    let x':=u x; let y':=u y; let g:= H.skyio; have hc := q.mono (b_up (shape A R) (A:=S) le_rfl (by norm_num : 2≤6)); let φ:= layout (A:=A); have he(w:mState N A)(i:A.Index)(a : i∈A.nc): let h:= φ w; h i=(fun j=>w.1.2 (i-1,j),fun j=>w.1.2 (i,j)):= if_neg (mem_sdiff.mp a).2; have hw : Locale.Track A R S (layout (u x)) (layout (u y)):= ⟨fun i j a t=>by rw [show layout (u x) i=_ from he (u x) i a,show layout (u y) i=_ from he (u y) i a]; exact (hc.controls (i-1,j) (b_blank _ _ _ t)).2.1,fun i j a t=>by rw [show layout (u x) i=_ from he (u x) i a,show layout (u y) i=_ from he (u y) i a]; exact (hc.controls (i,j) (b_blank _ _ _ t)).2.1⟩ -- tune pair function matching
    let hc'(i:A.Hcols)(f):= hc.controls i f; let q:Ear A R S x'.2.2.1 y'.2.2.1:= fun i t=> hc.horrors i (b_blank _ _ _ t); obtain ⟨v,E⟩:= p.lightV t hw q H.F Q.size Q.hearth (u x).1.1 (u y).1.1 (u x).2.1 (u y).2.1 (fun i h=> ⟨(hc' i h).1,(hc' i h).2.2⟩); refine ⟨v, fun i a z p'=>?_⟩; let k:= A.mark i; have hp(w:mState N A): parseY H w i=k.book (H.Z.deck k (k.reads (A.atmospheric (g w))) (summit A H.T H.y (φ w) (g w) i)):= by
       unfold parseY Meadow.Frame.ψ atlasG; have ht: k.reads (H.port w)=k.reads (A.atmospheric (H.skyio w)):= (k.reads_crown _ _ (Arcing w|>.mono (A.crown_air i ((A.nc_index ..).1 a)))).symm; rw [ht, show scroll H w i=summit A H.T H.y (φ w) (g w) i from ?_]; exact (A.putF_air H.T H.y (Arcing w) i ((φ w) i)).symm -- tune
    rw [hp,hp]; unfold Tunnel.book; split; next u => exact p.coup E hw q a (x:=z 0) (t:=Fin.tail z) ((event_eta z).symm ▸ p') _ -- tune signature
    next u=>rfl
 refine ⟨fun i h j v=>(broad_mem ..).2 ⟨_,p.shape_at _ h,(bay_mem _).1 (stem_bay _ _ v)⟩,fun x y h=> (ht x y h).1,fun x y h=> (ht x y h).2⟩
end Spine
end YM.CF.BPress.Peel

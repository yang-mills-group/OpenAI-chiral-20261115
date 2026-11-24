import YM.CF.BPress.Peel.Spare
import YM.CF.BPress.Sugar.Report
/-!
reader price spine. Wide support charged on ANY micro terms. `$F.Z.fares` frame reads needed only where specified (+ Borem). `RichT` grant. -/
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
abbrev zoomM (H:Sugar.Crew A):=9*H.tile.R+1
abbrev zoomX(X: Sugar.Stage N) := 9*X.tile.R+X.W.T.val+1
abbrev fundP(X:Sugar.Stage N) (H:Sugar.Crew A) := zoomX X + zoomM H
abbrev Magnified (S:Support (More N))(X:Sugar.Stage N)(H:Sugar.Crew A):= halo (fundP X H) S
structure Seer (H:Sugar.Crew A)(R:Hangar (More N))(X:Sugar.Stage N)(k:ℕ):Prop where
 charter : Charter H R X k
 frameTilt : H.tile.r=1
 timeTilt : X.tile.r=1
 depth : ∀ i:A.Index, 2*umbra B+zoomM H ≤ Meadow.Tent.body (A.mark i) -- tune
variable (Q:Seer H R X k) {U:Support (More N)}{x y:Visit A R H}
abbrev scroll (H:Sugar.Crew A)(x:mState N A)(i:A.Index):=knot (T:=H.T) (y:=H.y) A (layout x) (H.port x) i
abbrev parseY(H:Sugar.Crew A)(x:mState N A)(i:A.Index):= Meadow.Frame.ψ (A.mark i) H.Z (H.port x) (scroll H x i)
-- readings for all endpoint sites in Magnified.Zone. Pointer halo stems.
structure Spine (H:Sugar.Crew A)(X:Sugar.Stage N)(U:Support (More N))(t:Seal (BlockY A R)): Prop where
 pay(i:Site (More N))(p:i∈Magnified U X H): Peel.stem (plan A R i) 6⊆ t
 raw(x y:Visit A R H)(w:Along x.val y.val t): Lattice.Agrees (Magnified U X H) (H.port (fU x.val)) (H.port (fU y.val))
 spirit(x y:Visit A R H)(w:Along x.val y.val t) (i:A.Index)(p:i∈ A.nc)(z:Site (More N))(v:z∈richT A (Magnified U X H) i): parseY H (fU x.val) i z= parseY H (fU y.val) i z
-- strength projection.H.Enlarge.
lemma halo_sail (S:Support (More N)){u v:ℕ}{x y:Site (More N)}(h:x∈halo u S)(p:separation x y≤v) : y∈halo (u+v) S:=by obtain ⟨x,t,h⟩:=halo_spec.mp h; exact halo_spec.mpr ⟨_,t,(separation_triangle ..).trans (add_le_add h p)⟩
lemma halo_xy {x y:Site (More N)}{r:ℕ}: x∈ halo r {y} ↔ separation y x≤r:=by simp [halo_spec]
namespace Spine
variable (G:Spine H X U t)
local notation "Tℳ"=>Magnified U X H
variable {a z w: Site (More N)} (p:Along x.val y.val t)
include Q
lemma deepLens {i:A.Index}(u:a∈ A.band i)(h:a∉ Meadow.cloak (A.mark i) (body (A.mark i)))(v:z∈ Lattice.halo (zoomM H) {a}): peek A i z:=by
 have he: body (A.mark i)< burial (A.mark i) a:= lt_of_not_ge fun e=> h (mem_filter.mpr ⟨u,e⟩) -- tune
 obtain ⟨k,l,t⟩:= (A.mark i).internal a|>.mp u; rw [Tent.burial_rise (A.mark i) l t] at he; unfold distanceQ at he
 have ht:= Q.depth i; let n:=2*umbra B+zoomM H; have hp:n≤ k∧k+n≤(A.mark i).n.val:=by unfold n; omega --
 exact deep_m (near_in (i:=i) (u:=n) (x:=a) (y:=z) ⟨k,hp.1,hp.2,t⟩ ((delta_at a z 0).trans (halo_xy.1 v)) (Nat.le_add_left ..)) (by unfold n; omega)
omit Q
lemma axial0 (i:A.Index)(p:i∈ A.nc)(x:mState N A) : (A.mark i).axial (H.port x)=1:=Tunnel.no_axial (A.mark i) _ (fun j v=> (H.Z.roll_hold A (layout (A:=A) x) (H.skyio x) x.2.2.1) j (A.poles_s i (by rw [storesN,if_neg (mem_sdiff.mp p).2]; exact v))) -- tune F_roll
include p Q G
lemma pointers (k:ℕ)(h:k≤6)(e:a∈Tℳ) : Peel.stem (plan A R a) k⊆ t:= (stem_mid _ h).trans (G.pay _ e) -- tune no p Q but include cost performance
lemma faces_m (e:a∈Tℳ) : ((H.tape (fU x.val)).frameN a)= (H.tape (fU y.val)).frameN a:=by
 have he(i)(x:mState N A) : (H.tape x).h i=H.T.give H.y (tower H x i.1) i.2 (x.1.2 i):=by unfold Crew.tape Letters.ballot; change centerH A (layout x) (H.port x) H.T H.y i= _; rw [skyline_t,centerH]; change _= H.T.give H.y _ _ _; unfold Sheet.Atlas.frame; exact congrArg _ (congrFun (flash_code A x.1.2) i)
 rw [Letter.frameN,Letter.frameN,he,he]; exact p.gives Q.charter.port _ (pointers Q G p 2 (by norm_num) e)
lemma seaZ {i:A.Index}(h:i∈ A.nc) (v:z∈Tℳ)(e:z∈ A.band i): haloM (A.mark i) (scroll H (fU x.val) i) z= haloM (A.mark i) (scroll H (fU y.val) i) z:= ((canopy A _ _ H.T H.y (mem_sdiff.mp h).2 z e)).trans ((faces_m Q G p v).trans ((canopy A _ _ H.T H.y (mem_sdiff.mp h).2 z e)).symm) -- tune p
end Spine
end YM.CF.BPress.Peel

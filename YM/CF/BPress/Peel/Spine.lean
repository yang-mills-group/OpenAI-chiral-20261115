import YM.CF.BPress.Peel.Script
/-! both tile procedures covered using pregrant micro enlargement. -/
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
variable {H: Sugar.Crew A} {t T S P: Seal (BlockY A R)}{i : BlockY A R}{q : A.Index}{k r:ℕ}{X: Sugar.Stage N}
namespace Spine
variable (Q:Seer H R X k) {U:Support (More N)}{x y:Visit A R H}
variable (G:Spine H X U t)
local notation "Tℳ"=>Magnified U X H
local notation "x₁"=>fU x.val
local notation "x₂"=>fU y.val
variable {a z w: Site (More N)} (p:Along x.val y.val t)
include Q p G
lemma codeQ (e:a∈Tℳ): (H.tape x₁).color a=(H.tape x₂).color a:=by
 let T':=Locale.panel A a; have he(v:mState N A): (H.tape v).color a=v.1.2 T':= congrFun (flash_code A v.1.2) _; rw [he,he]; exact (p.controls T' (G.pay _ e (stem_home ..))).2.1
lemma trunkY (u:a∈halo (zoomX X) U)(h:q∈ A.nc)(v:a∈A.band q): ferns (A.mark q) H.Z (H.port x₁) (scroll H x₁ q) H.tile a=ferns (A.mark q) H.Z (H.port x₂) (scroll H x₂ q) H.tile a:=by
 let W:= A.mark q; let n:=9*H.tile.R; let D:= halo (zoomM H) {a}; have ho(z:Site (More N))(t:z∈D):z∈Tℳ:=halo_sail U u (halo_xy.1 t); let ϕ(z:mState N A):= parseY H z q; let θ(z:mState N A):= headM W (scroll H z q); have hh(b:Site (More N))(v:b∈ A.band q)(t:b∈D):θ x₁ b=θ x₂ b:= congrArg (fun g:SU.E=> scaledV g⁻¹ Seed) (G.seaZ Q p h (ho b t) v) -- tune Dial
 unfold ferns; split; exact hh a v (halo_subset _ _ (mem_singleton_self a)); next z=>
    have hv(b:Site (More N))(u:b∈ D):b∈A.band q∧ϕ x₁ b=ϕ x₂ b:= let Ly:= deepLens Q v z u; ⟨own_band Ly,G.spirit x y p q h b (mem_filter.mpr ⟨ho b u,Ly⟩)⟩; have hp(z:mState N A):W.orient (H.port z)=H.port z:=by unfold Tunnel.orient; rw [show W.axial _=1 from (axial0 _ h _)]; ext i; simp [Lattice.gauge] -- tune field; ext may overreach
    apply congrArg₂ (fun g:SU.E => scaledV g⁻¹) (hv a (halo_subset _ _ (mem_singleton_self _))).2; unfold tea; rw [show (A.mark q).orient (H.port x₁)= _ from hp x₁,show (A.mark q).orient (H.port x₂)=_ from hp x₂]; let Y(x:mState N A):= gauge (ϕ x) (H.port x); let V(x:mState N A):= shuffle (ϕ x) (θ x)
    change tree H.tile W.mem _ (Y x₁) (V x₁) a=tree H.tile W.mem _ (Y x₂) (V x₂) a; have hg:halo n {a}⊆D:= Corona.halo_mono (Nat.le_succ _) le_rfl; apply (tree_read (k:=H.tile) Q.frameTilt (Y x₁) (V x₁) W.mem (Meadow.cloak W W.lips) (Y x₂) (V x₂) a (fun _ _=>⟨Iff.rfl,Iff.rfl⟩))
    · intro i t; have h₁:= hv i.1 (hg t); have hj: endAt i∈ D:= halo_xy.mpr (le_trans (separation_triangle a i.1 (endAt i)) (Nat.add_le_add (halo_xy.1 t) (oneTouch i.1 i.2))); have h₂:= hv (endAt i) hj; unfold moss; split; next g=> unfold Y Lattice.gauge; rw [h₁.2,h₂.2,G.raw x y p i (ho i.1 (hg t)) (ho _ hj)] -- tune ends
      · rfl
    intro i t'; have h₁:= hv i (hg t'); unfold Meadow.crop; split; next f=> apply congrArg₂ scaledV h₁.2 (hh i h₁.1 (hg t'))
    next f=> rfl
lemma brush0 (i:A.Index)(h:a∈ A.band i)(u:a∈halo (zoomX X) U): let v:= H.tape x₁; let w:= H.tape x₂; v.plant i a=w.plant i a ∧ ∀ t,v.brush i t a=w.brush i t a:=by
 intro v w; change Stamps.plant _ _ _ _ _ _ _= Stamps.plant H.Z (H.port x₂) _ _ _ _ a ∧ ∀ t, Stamps.brush _ _ _ _ _ _ _ a= Stamps.brush _ _ _ _ _ _ _ a; by_cases p':i∉A.nc; · have ht:i∈A.dc:= Classical.byContradiction (fun h=>p' (mem_sdiff.mpr ⟨mem_univ _,h⟩)); simp only [Stamps.plant, Stamps.brush,if_pos ht]; simp
 let Hi:=not_not.mp p'; let e:= (mem_sdiff.mp Hi).2; let W:=A.mark i; have hx(m: mState N A): (W).axial (H.port m)=1:= axial0 i Hi m; change Stamps.plant H.Z (H.port x₁) _ _ _ _ a= Stamps.plant H.Z (H.port x₂) _ _ _ _ a ∧ _; have hf:= G.trunkY Q p u Hi h; unfold Stamps.plant Stamps.brush; -- tune rhs Stamps.brush need `v` not unfolded?? change both
 simp_rw [if_neg e,sprigs,Meadow.Frame.whole]; -- may not both arms
 constructor; · exact congrArg₂ (fun g:SU.E => scaledV g⁻¹) (((congrFun (hx x₁) a).trans (congrFun (hx x₂) a|>.symm))) hf
 intro t; apply congrArg₂ (fun g:SU.E => swivelC g⁻¹) (((congrFun (hx x₁) a).trans (congrFun (hx x₂) a|>.symm))); unfold stalk; split; next t=> exact congrArg (fun k:SU.E=> swivelC k⁻¹ _) (seaZ Q G p Hi (Corona.halo_mono (Nat.le_add_right (zoomX X) _) le_rfl u) h)
 next r=> exact congrArg (fun i:Sprout=> SU.Pair.fullM i.val) hf
lemma interest_cost(h:a∈halo (zoomX X) U) : Lily.interest A (H.tape x₁) a=Lily.interest A (H.tape x₂) a:=by
 unfold Lily.interest; split; next v=> exact (brush0 Q G p _ (show a∈A.band (citizen A a v) from Exists.choose_spec v) h).2 _
 next v=>rfl
end Spine
end YM.CF.BPress.Peel

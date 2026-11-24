import YM.CF.BPress.Peel.Spine
/-! Material.Mark reading receipts all.IQ. -/
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
variable {a z w: Site (More N)} (p:Peek H t x.val y.val)
variable {e d c:ℝ}
local notation "ps_"=> peeking t _ _ p
local notation "ξL"=> halo (zoomX X) U
include Q p G
lemma alive (h:a∈ξL) : a∈Tℳ:= Corona.halo_mono (Nat.le_add_right (zoomX X) (zoomM H)) le_rfl h -- tune
lemma danger_seen (v:z∈Tℳ) : z∈Danger A R X.W (debts H x.val) ↔ z∈ Danger A R X.W (debts H y.val):=by
 have he:= (ps_).masks (H:=H) (G.pointers Q (ps_) 2 (by norm_num) v); simp only [Danger,mem_filter,mem_univ,true_and, Near,he]
lemma seesP {i:Site N}(u:node i∈Tℳ) : (i∈ Picks A R (debts H x.val)↔ i∈ Picks A R (debts H y.val)) ∧ (i∈specialB X.W A R (debts H x.val)↔ i ∈ specialB X.W A R (debts H y.val)):=by
 have h:= (ps_).masks (H:=H) (G.pay _ u); simp only [Picks,specialB,mem_filter,mem_univ,true_and]; unfold Local at h; -- Good is ¬ Local w defeq panel but h unfolded not here
 exact ⟨ and_congr Iff.rfl (not_congr h),and_congr h Iff.rfl⟩
lemma seesG (a)(h:a∈ξL): (H.tape x₁).G a=(H.tape x₂).G a:=by
 unfold Letter.G; split; next w=> exact (G.brush0 Q (ps_) (citizen A a w) w.choose_spec h).1
 next w=> rw [codeQ Q G (ps_) (alive Q G p h)] -- opacity includes notation tuner
lemma seesH (v:ℝ)(h:a∈ξL) : (H.tape x₁).H X.W v a=(H.tape x₂).H X.W v a:=by
 have he:=G.codeQ Q (ps_) (alive Q G p h); unfold Letter.H; split
 next w=>
   split; next t=> unfold Letter.amend; rw [faces_m Q G (ps_) (alive Q G p h),he]
                                                                                                           -- tune
   next u=> exact (G.brush0 Q (ps_) _ w.choose_spec h).2 v
 next w=> rw [he]
lemma peekWide {u:ℕ}(h:z∈U)(v:a∈halo u {z})(p:u≤zoomX X): a∈ξL:= Corona.halo_mono p (singleton_subset_iff.mpr h) v -- tune include p here clash
variable (F:Rented R H X d e k c)
include F
lemma utensils : Lattice.Agrees Tℳ (H.utensil x₁) (H.utensil x₂):=by intro i h ℓ; exact Q.charter.to_read F p i (pointers Q G (ps_) 2 (by norm_num) h) (G.raw x y (ps_) i h ℓ) -- tune order
lemma finger (h:a∈ U) : H.thread R X x₁ a=H.thread R X x₂ a:=by
 let V:= H.utensil; let u:= fun x:mState N A=> (H.tape x).G; let Z:=safe A R X.W; let t:=9*X.tile.R; have he:t+1≤zoomX X:=by unfold zoomX t; omega
 have hb(i)(v:i∈halo t {a}):i∈ξL:= peekWide Q G p h v (le_trans (Nat.le_succ _) he); apply tree_read Q.timeTilt (V x₁) (u x₁) univ (Z (debts H y.val)) (V x₂) (u x₂) a (fun i l=> ⟨Iff.rfl,?r⟩) (?s) (?d); case r=> exact mem_compl.trans ((not_congr (danger_seen Q G p (G.alive Q p (hb i l)))).trans mem_compl.symm) -- tune case syntax
 case s=>
    intro i l; have ht: endAt i∈ ξL:= peekWide Q G p h (halo_xy.2 ((separation_triangle a i.1 (endAt i)).trans (Nat.add_le_add (halo_xy.1 l) (oneTouch i.1 i.2)))) he; unfold moss; split; exact utensils Q G p F i (G.alive Q p (hb i.1 l)) (G.alive Q p ht); rfl
 case d=> intro i l; unfold Meadow.crop; split; exact G.seesG Q p i (hb i l); rfl
lemma sees_t (h:z∈U) (v:ℝ): H.fury R X x₁ v z=H.fury R X x₂ v z:=by
 let S:=debts H x.val; let T:=debts H y.val; unfold fury Stage.tower Kactual; rw [show blink A X.W R (H.unsea R x₁) z=blink A X.W R (H.unsea R x₂) z from ?_]; split; next w=> exact congrArg (fun q:Sprout=> SU.Pair.fullM q.val) (finger Q G p F h)
 next w=> exact G.seesH Q p _ (halo_subset _ _ h)
 refine tSee (S:=S) (T:=T) (x:=z) (fun i v=> G.danger_seen Q p (alive Q G p (peekWide Q G p h v (by unfold zoomX; omega))))
omit F
open Engine Shot Driver
variable {V:Driver N}
variable (F:Rented R H X V.d e k c)(t':Stage.Stamp A R X V)
local notation "α₀" => ΓStage F t'
lemma hasP : Plain.Along U ((α₀) (party A R H x)).val ((α₀) (party A R H y)).val:=by
 let S:=debts H x.val; let T:=debts H y.val; let x':=fU x.val; let y':=fU y.val
 refine ⟨agrees_mono (utensils Q G p F) (show U⊆Tℳ from halo_subset ..),fun i z=> finger Q G p F z,fun i z=> ?_,fun i z K=>?_⟩ -- tune function x param
 · change decide (i∈ Picks A R S)=decide (i ∈ Picks A R T); simp only [show (i∈ Picks A R S ↔ i∈Picks A R T ) from (seesP Q G p (halo_subset _ _ z)).1] -- tune
 let U(v: ℝ):= sees_t Q G p F z v; apply ContinuousMap.ext; intro x; cases K; exact U x.val; exact congrArg (fun f=> deriv f x.val) (funext U)
lemma Cam (u:ℝ) (B:ℕ): Camera (grim R H X u x₁) V.decks ((α₀) (party A R H x)) ((α₀) (party A R H y)) U (grim R H X u x₂) B (P:=V.Beta):=by
 let W:= (ps_); let W':Lattice.Agrees _ _ _:= G.raw _ _ W; have he:∀ i∈ U,plan A R i∈ t:= fun i h=> G.pay i (halo_subset _ _ h) (stem_home ..); refine ⟨Plain.Along.price0 (hasP Q G p F t'),agrees_mono W' (show U⊆Tℳ from halo_subset ..),fun i h=> W.tags i (he i h), fun i v=> ?_, fun i v=>?_⟩
 · refine ⟨?_,?_, interest_cost Q G W (halo_subset _ _ v), Iff.rfl⟩; · exact (congrArg (fun p:Habitat.Upled SU.Slot=> Habitat.Upled.decode p (2:ℝ)) ((hasP Q G p F t').arms _ v false))
   have K:= seesP Q G p (halo_subset _ _ v); change yKick _ _ _ _= yKick _ _ _ _; unfold yKick; simp only [(show i∈H.areaC R X x₁ ↔ i∈ H.areaC R X x₂ from K.2), show Crew.can x₁ i=Crew.can x₂ i from W.cylinders _ (he _ v)]
 exact prod_congr rfl fun j u=> congrArg (fun v:Circle=> (v:ℂ)) (W.locks _ (he _ (v (Spark.dorm_sub (X:=Vesper.harbor i) B (i.property.2 u))))) -- signature tune
end Spine
end YM.CF.BPress.Peel

import YM.SU5.FiniteGaugeData.Galope.StrataC
import YM.SU5.FiniteGaugeData.Cuprite.Spiny
import YM.SU5.FiniteGaugeData.Brique.Pike
/-!
# Vapor: new Pose charges
Supply small fields ON TILES around any high-s resolution, shallow mean-drift on invoice all with pledge slope. Keep ph clocks. K fixed post-interest precision & epoch, NOT relying on planar exhaustion of torus.Bills.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 500000
set_option linter.flexible false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Cuprite
open Function NormedSpace Filter Finset MeasureTheory Lattice RG Wilson AnalyticBridge Metric Pressure Galope CF CF.Pastry CF.Py.Rate
open SU Fock Reduction Reduction.Jersey Reduction.Drama Reduction.Drama.Pack Reduction.Hutch Cube Lat Window Presidio Tenant Skye Scree Graph
open Rush Scroll Peaks Tap Tulip Fir -- tune
open Avenue RouteM Next.Rank Spindle
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
variable {n:Side}{G:Gauge}{t p r d a b:ℝ}{k M R w:ℕ}
namespace Spirit
open Beamer Press
abbrev κ(w:ℕ):= coreN w
abbrev η(w:ℕ) := coreN w+w
def deckY (V:Config G n)(t:ℝ)(w:ℕ):= glow (Steve.misses V t) (lic w)
abbrev coverN (V:Config G n)(t:ℝ)(w k:ℕ): Finset (Site n):= (deckY V t w).biUnion (Spindle.patch k)
def discE (V:Config G n)(t:ℝ)(w:ℕ): Finset (Site n):= univ \ coverN V t w (coreN w)
abbrev κf(x:ℕ):ℝ:= tB (coreN x)
variable (V:Config G n)(h:Intro n w)
-- cores toll for unit seats
include h
lemma retired (t:ℝ): ((discE V t w).card:ℝ) ≤ (diamC/(w:ℝ)^2) *Fintype.card (Site n) + κf w *(Steve.misses V t).card := by
 let A:=Steve.misses V t; let Z:=glow A (lic w); let v:=discE V t w; let d:=disc Z (κ w); let G:=coverN V t w (κ w); have he:v=univ\G:=rfl
 have ht: buy Z (κ w)⊆ G ×ˢ Hor:=by
   intro y e; obtain ⟨i,g,t⟩:=mem_biUnion.mp e; obtain ⟨p,r⟩:=mem_product.mp (show y∈ _ from t); apply mem_product.mpr; exact ⟨mem_biUnion.mpr ⟨i,g,(mem_filter.mp p).1⟩,r⟩ -- may need V type shadow G.
 have hp: parcelM Z (κ w)≤ G.card*3:=by rw [←count_hor,←card_product]; exact card_le_card ht
 have hg: v.card*3≤d:=by
    have he': v.card+G.card= Fintype.card (Site n):=he ▸ ((card_sdiff_add_card_eq_card (subset_univ G)).trans card_univ); have hv:= disc_book (glow_in A (lic w)) (show coreN w ≤ lic w by unfold lic; omega); change d+parcelM Z (κ w)=3*Fintype.card (Site n)+1 at hv -- tune mul
    omega
 have hx: (v.card:ℝ) ≤ d:=by exact_mod_cast le_trans (show v.card≤v.card*3 by omega) hg
 have hq:= h.1; let W:ℝ:=w; have hw:0< W:=by unfold W; exact_mod_cast (lt_of_lt_of_le (by decide:0<(2:ℕ)) hq)
 let C:ℝ:= Fintype.card (Site n); have e: ((d:ℝ)+1)*W^2 ≤ diamC*C + (A.card:ℝ)*κf w*W^2 := qualify h A
 apply le_trans hx; apply le_of_mul_le_mul_right _ (pow_pos hw 2); convert (e.trans' (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg W))) using 1; change (diamC/W^2 * C+ κf w *(A.card:ℝ))*_ =_; field_simp
-- payment at any good tile suffices lamp on ANY core η; common for later reconstruction of Mark.Couples all at same orientation. Match on X' = actual Loom.
local notation "G5" => SU.group
variable {Y:Loom n}(K:Roof n t d k Y)(X:Orbit n) -- tune
omit h
include K
local notation "o'"=> More n
lemma tower (q:p≤t)(aw:k≤w)(i:Site (More n))(hv':i∈deckY X.1 p w): Agrees (Spindle.patch (η w) i) X.1 (Y X):=by -- `(i∈...)` syntax? tune type
 intro e x y; symm; apply K.lamp; apply Finset.disjoint_left.mpr; intro b g h
 obtain ⟨f,r,u⟩:= (RG.flags_spec ..).mp g; apply u.not_ge; apply le_trans _ q; apply le_of_not_gt; intro v
 -- pay tile base remains good by η+w+4.
 have hv: f∈Steve.misses X.1 p:= mem_filter.mpr ⟨mem_univ _, v⟩
 obtain ⟨a,w',H⟩:= halo_spec.mp h; have he: a∈ Spindle.patch (η w) i:=(show ends e⊆ Spindle.patch (η w) i from insert_subset_iff.mpr ⟨x,singleton_subset_iff.mpr y⟩) w'
 have hp: separation b f.1 ≤ 4:=by rw [separation_comm]; exact Extra.Iteration.Shapes.visits_dist _ _ _ (List.mem_toFinset.mp r)
 apply Press.uprise hv' _ f.2 _ hv; apply Avenue.patch_includes (η w+k+4) (lic w) _ i (Avenue.extend i b f.1 hp (Avenue.extend i a b H he)); unfold η lic; omega
abbrev Mosquito(n:Side) := Seat n → SU.E
structure CoversU (X:Orbit n)(Y:Loom n)(w:ℕ)(p r u:ℝ) (g:Mosquito n):Prop where
 Intro : Intro (More n) w
 beds : ∀ i∈deckY X.1 p w, let S:= Spindle.patch (η w) i; let U:= gauge g X.1; let V:=gauge g (Y X); Agrees S X.1 (Y X) ∧ Agrees S U V ∧ (∀ e ∈ Room i (η w),SU.group.chord (U e) ≤ r) ∧ Tulip.fare S (profile U) 1 ≤u ∧ Tulip.fare S (profile V) 1 ≤u
lemma config (u:0<r)(q:p≤t)(v:0≤p)(aw:k≤w)(hg:Intro (More n) w)(e:∀ i:SU.group.El, SU.group.chord i≤ balanceX (lic w) p → ‖brand i-1‖≤ r): CoversU X Y w p (balanceX (lic w) p) (((η w+η w+1)^4*4:ℕ)*(r+r)) (Press.mapA X.1 (deckY X.1 p w) (lic w)):=by
 let Z:= deckY X.1 p w; let G:= Press.mapA X.1 Z (lic w); let V₀:=X.1; let U:= gauge G V₀; let V:=gauge G (Y X); refine ⟨hg,fun i h=>?_⟩; let S:= Spindle.patch (η w) i; have hk: Agrees S X.1 (Y X):= tower K X q aw i h; have heq: Agrees S U V:=Skye.tied S V₀ (Y X) G G hk (fun i _=>rfl)
 have hx(x:reach n)(hV:x∈ Room i (η w)): SU.group.chord (U x) ≤ balanceX (lic w) p:=by
    have ht: Spindle.patch (η w) i⊆ Spindle.patch (lic w) i:= Avenue.patch_includes _ _ (by unfold lic η; omega) _; obtain ⟨a,b⟩:= (mem_filter.mp hV).2;
    apply Press.cargoF (Z:=Z) (A:=Steve.misses V₀ p) (k:=w) V₀ V₀ (le_refl Z) h hg.2.1 (by unfold lic; omega) (fun i _=>rfl) p v (fun j g=>le_of_not_gt (fun w=>g (mem_filter.mpr ⟨mem_univ _,w⟩))) x (mem_filter.mpr ⟨mem_univ _,ht a,ht b⟩) -- tune reach
 change Agrees S X.1 (Y X) ∧ Agrees S U V ∧ _; refine ⟨hk, heq, hx,?_,?_⟩
 · apply le_trans (Peaks.payment U (profile U) r r (by rw [sub_self,norm_zero]; exact u) S (fun j p=>e _ (hx j p))); gcongr; exact_mod_cast Spindle.broad i (η w)
 apply le_trans (Peaks.payment V (profile V) r r (by rw [sub_self,norm_zero]; exact u) S (fun j p=> by rw [←heq j (mem_filter.mp p).2.1 (mem_filter.mp p).2.2]; exact e _ (hx j p))); gcongr; exact_mod_cast Spindle.broad i (η w)
omit K
-- eventual for ANY PP clock envelope
variable {ε:ℝ}
lemma rate_req (u:0<ε)(he:0<a) (ht:0<t)(hw:k ≤ w): ∀ᶠ x in atTop,∀ (p:BudgetPoint), p.threshold=temp x→∀ N:Side,Intro (More N) w →∀ Y:Loom N,Roof N t d k Y→∀ X:Orbit N, ∃ g,CoversU X Y w p.threshold ε a g:=by
 let k:=η w; let V:ℕ:=(k+k+1)^4*4; let K:ℝ:= V; have hv:0<K:= by unfold K V; positivity
 let R':= a/(2*K); have hR : 0<R':=by unfold R'; positivity
 have hs: {x:SU.E | ‖brand x-1‖ ≤ R'}∈𝓝 (1:SU.E):=(show Continuous fun x:SU.E=> ‖brand x-1‖ from (Dial.spinD.sub continuous_const).norm).continuousAt.eventually (ge_mem_nhds (by simpa only [brand_one,sub_self,norm_zero] using hR))
 obtain ⟨R,hRh,v⟩:= Next.Rank.surrounds SU.group _ hs; have hl:= Galope.Cold.soft.θA.close (by norm_num); have hh:Tendsto (fun x=> Press.balanceX (lic w) (temp x)) atTop (𝓝 0):=by simpa [Press.balanceX] using hl.const_mul (4*(lic w:ℝ)) -- tune
 filter_upwards [hl.eventually (ge_mem_nhds ht), hh.eventually (ge_mem_nhds u), hh.eventually (ge_mem_nhds hRh)] with z b d' q p h n g Y Z x;
 let M:= lic w; let T:= balanceX (lic w) p.threshold; let V₀:= Press.mapA x.1 (deckY x.1 p.threshold w) M; have hz: (V:ℝ)*(R'+R')= a:=by change K*(R'+R')=a; unfold R'; field_simp; ring -- tune
 have he:CoversU x Y w p.threshold T ((V:ℝ)*(R'+R'))  V₀ := config Z x hR (h ▸ b) p.threshold_pos.le hw g (fun i p'=> v (le_trans p' (show T≤R from (by unfold T; rw [h]; exact q)))) -- tune implicit
 rw [hz] at he; refine ⟨V₀,g,?_⟩ -- existential g pick unify
 intro i l; obtain ⟨A,B,C,hf,F⟩:= he.beds i l; exact ⟨A,B,fun e l=> (C e l).trans (by unfold T; rw [h]; exact d'),hf,F⟩
end Spirit
end YM.SU5.FiniteGaugeData.Cuprite

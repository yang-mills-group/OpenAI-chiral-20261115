import YM.CF.BPress.Peel.Pom
/-! Geometry of roof enquiries. Poly use `potions` on visits. 
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Peel
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Sugar.Crew Grid Env Bands Vesper Hazel Hazel.Letters Net
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}{R: Hangar (More N)}
open Tunnel Palmer Contour Along Sheet
attribute [local instance] Gauge.frobInner
variable {H: Crew A} {t T S E P: Seal (BlockY A R)}{i : BlockY A R}{q : A.Index}{k r:ℕ}
-- increase grants: $r ≥ Reach
abbrev attach (X:Stage N) (k:ℕ) := X.W.M+(2*k+20)
structure Charter (H:Crew A)(R:Hangar (More N))(X:Stage N)(k:ℕ) :Prop where
 port : Host R H
 pitch : attach X k+4 ≤ R.L.val
 care : attach X k+4 ≤ Wealth.cloak B
variable {X:Stage N}{e c d :ℝ}
variable (F:Rented R H X d e k c) (Q:Charter H R X k)
-- useful flags lemma independent of k F.Use both ends
lemma spread(x y:Micro (More N))(v a:Support (More N))(t:Lattice.halo 4 v ⊆ a)(p:Lattice.Agrees a x y)(e:ℝ): v ∩ RG.flags e x=v∩ RG.flags e y:=by
 have he(x y:Micro (More N))(p:Lattice.Agrees a x y)(i:Site (More N))(f:i∈v)(q:i∈flags e x): i∈flags e y:=by
    obtain ⟨j,g,h⟩:= flags_spec ..|>.1 q; have ht:touched j⊆a:=fun z p=> t (halo_spec.mpr ⟨i,f,(separation_triangle i j.1 z).trans (Nat.add_le_add ((separation_comm ..).le.trans (Work.E01.sep_touched j i g)) (Work.E01.sep_touched j z p))⟩); refine (flags_spec ..).2 ⟨j,g, (show faceValue x j= faceValue y j from ?_) ▸ h⟩; exact travel_local j.1 _ x y (fun i b c=> (agrees_mono p (show _ from ht)) i (List.mem_toFinset.mpr b) (List.mem_toFinset.mpr c)) -- tune
 ext i; simp only [mem_inter]; exact and_congr_right fun t=>⟨he x y p i t, he y x (fun i v g=>(p i v g).symm) i t⟩
namespace Charter
variable {x y:Visit A R H}{s:BlockY A R}{S t:Seal (BlockY A R)}{a v:Site (More N)}(p:S∈Camp x.val H)
include F
lemma actu {x:Visit A R H}(h:a∈flags e (H.port (fU x.val))) : a∈ H.flag (fU x.val):=by obtain ⟨i,x,p⟩:= flags_spec ..|>.1 h; exact (flags_spec ..).2 ⟨i,x,F.stop.trans_lt p⟩
-- consumes! F.pay transport δ.Reader.
include p Q
lemma contractU (h:a∈flags e (H.port (fU x.val)))(q':a∈ Room q S (attach X k) 40) : a∈ Room q S X.W.U 1:=by
 let f:=F.pay (fU x.val) x.property; obtain ⟨v,hv,-⟩:= f.blaze a (actu F h); have hc:= (mem_filter.mp q').1; have hp:q=v:=(moment_p A ((Nat.le_succ _|>.trans ?_)) hc).symm.trans (moment_gap A hv); swap; · exact (Nat.add_le_add_left (by norm_num : 1≤4) _).trans Q.care
 rw [hp]; obtain ⟨z,t,d⟩:= (at_petal.mpr (f.flood a a (actu F h) (by simp)).2|>mem_biUnion.mp); refine mem_filter.mpr ⟨Lattice.halo_subset _ _ hv, mem_biUnion.mpr ⟨z,?_,d⟩⟩; obtain ⟨j,ht,hg⟩:= mem_biUnion.mp ((mem_filter.mp q').2); refine memberQ H x.val (fat_m x.val t) p ht ((bay_mem _).mp (stem_bay z (fixedR+fixedR) (?_ ))) -- tune j z p span orientation
 exact stem_mid (R:=R) z (by norm_num [fixedR] : 1+40 ≤ _) (stem_join (r:=1) (t:=40) d (stem_flip hg))
lemma keepsR {l:Link (More N)} (h:l.1∈ Room q S X.W.U 2): Week (Room q S (attach X k) 40) (ends l) (flags e (H.port (fU x.val))) k:=by
 let U:=X.W.U; let a:=attach X k; have hp:U+(2*k+20)≤a:=Nat.add_le_add_right (X.W.um) _; have hd:2*k+20≤ a:= le_trans (Nat.le_add_left ..) hp
 have hu : a ≤ R.L.val:=(Nat.le_add_right ..).trans Q.pitch; have hv:a ≤ Wealth.cloak B:=(Nat.le_add_right ..).trans Q.care
 apply keepsL _ _ _ k _ _
 · intro i b; obtain ⟨j,d,b⟩:=halo_spec.mp b; obtain ⟨a,g⟩:=mem_inter.mp d; have ht:= contractU F Q p a g; refine (rooms_m hp (by norm_num : 1+1 ≤40)) (extend_ _ _ ht (hp.trans hv) (hd.trans hu) b) -- tune unification q' time hp
 intro i b; obtain ⟨j,d,b⟩:=halo_spec.mp b; have h':separation l.1 j≤1:=by rcases mem_insert.mp d with g|g; simp [g]; rw [mem_singleton.mp g]; exact oneTouch ..
 refine (rooms_m hp (by norm_num : 2+1 ≤40)) (extend_ _ _ h (hp.trans hv) (hd.trans hu) ((separation_triangle l.1 j i).trans ?_)); omega
omit p F
include Q
lemma agreesR (w:Along x.val y.val (Contour.station fan S)): let T:= Room q S (attach X k+4) 41; Agrees T (H.port (fU x.val)) (H.port (fU y.val)):=by
 intro T l h h'; let u:= (mem_filter.mp (show l.1∈ Room q S (attach X k+4) 41 from h)); apply w.stokes Q.port.hearth Q.port.size l ((inside_iff ..).2 ⟨reach_m _ _ Q.care u.1, reach_m _ _ Q.care (mem_filter.mp (show l.1+step l.2∈T from h')).1⟩); exact fun z a=> petalsInStation (41+1) (by norm_num [fixedR]) (petal_grow (show plan A R l.1∈petal S 41 from u.2) a) -- tune implicit i
include F p Q
lemma comparison {l:Link (More N)} (h:l.1∈ Room q S X.W.U 2)(w:Along x.val y.val (Contour.station fan S))(v:S∈Camp y.val H) : H.utensil (fU x.val) l= H.utensil (fU y.val) l:=by
 let S':= Room q S (attach X k) 40; let U':=Room q S (attach X k+4) 41; have hu: S' ⊆ U':= rooms_m (Nat.le_add_right ..) (by norm_num)
 have hm:halo 4 S'⊆ U':=by intro i p; obtain ⟨i,p,g⟩:= halo_spec.mp p; exact extend_ i _ p Q.care ((Nat.le_add_left ..).trans Q.pitch) g
 let A':= H.harborT (fU x.val); let B':=H.harborT (fU y.val); have he:Agrees U' A'.1 B'.1:= agreesR Q w; exact F.roof.transmission _ _ _ _ S' (ends l) (spread A'.1 B'.1 S' U' hm he e) (keepsR F Q p h) (keepsR F Q v h) (agrees_mono he (Finset.coe_subset.mpr hu)) (fun i a=> w.tags _ (petalsInStation 40 (by norm_num [fixedR]) ((mem_filter.mp a).2))) l (by simp) (by simp)
end Charter
end YM.CF.BPress.Peel

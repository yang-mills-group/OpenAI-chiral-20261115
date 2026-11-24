import YM.CF.BPress.Peel.Short
import YM.CF.BPress.Honey.Wheat
/-! Scalar prices depart Lambert law. use with Visits. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Peel
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData Grid Along Honey Recipe
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}
variable {R:Hangar (More N)} {H:Crew A}{V:GramM N} {F: Recipe (A:=A) V} {ζ a k C' D τ:ℝ}
variable (Q:Budgeting H F τ k D ζ a C') {x y:Visit A R H}
structure Mangrove (R:Hangar (More N))(K:Crew A)(M:ℕ):Prop where
 raw: Wander (K.P.reach K.y) (6*M) ≤ R.L.val
 tail: K.P.heightClose K.y ≤ R.L.val
variable (p:Mangrove R H F.M)
namespace Mangrove
-- Thin $canonical$ true Theta all.Ang.Price.Energy. signatures tune implicit names
local notation "ξ₁"=> party A R H x
local notation "ξ₂"=> party A R H y
variable {S:Seal (BlockY A R)} {U:Support (More N)}
include Q p
lemma μPitch : H.P.reach H.y ≤ R.L.val:= by have h:= p.raw; unfold Wander at h; omega
lemma copy : 6*F.M ≤R.L.val:=by have h:=p.raw; unfold Wander at h; omega
variable (g:Along x.val y.val S)
include g
lemma turns (i:A.Hcols){r:ℕ}(h:Peel.stem (own A R i) 1⊆ S)(u:r≤R.L.val) : ∀ j∈columnBall A i r, own A R j∈ S:=fun j f=>h (Peel.radial i j f u) -- tune
lemma sailsL (i:A.Hcols)(t:Peel.stem (own A R i) 1⊆ S): leftY H F (ξ₁).val i= leftY H F (ξ₂).val i:=by
 have H' (r:ℕ)(p':r≤ R.L.val)(f:Fills A→Seal A.Hcols→ A.Hcols→ℝ)(v:smallRead f r) : f (fU x.val).2.1.1 (fU x.val).1.1 i=f (fU y.val).2.1.1 (fU y.val).1.1 i:= v _ _ _ _ _ (fun j f=>(g.controls j (turns Q p g i t p' j f)).1) (fun j f=>(g.controls _ (turns Q p g i t p' j f)).2.2.1)
 exact congrArg₂ (·+·) (H' _ (μPitch Q p) _ (lTerm_loc Q.summer.seen)) (H' _ p.raw _ (rTerm_loc Q.fromT Q.summer.seen)) -- tune
lemma tailRead (u:Seal A.Hcols)(t:u.image (own A R)⊆S): tailY H F (ξ₁).val u = tailY H F (ξ₂).val u:= Q.jac.tail_zone _ _ _ _ fun i p=> (g.controls _ (t (mem_image_of_mem _ p))).1 -- tune args
lemma refit (u:A.Air)(t:Peel.stem (own A R u.1) 1⊆ S): let f(x:mState N A):=softAl A H.κ H.y (H.skyio x) H.T; f (fU x.val) u= f (fU y.val) u:=by
 intro f; unfold f softAl; rw [← Budgeting.chooser ξ₁,← Budgeting.chooser ξ₂]; -- maybe doesn't match
 have hv:= (g.controls u.1 (t (stem_home ..))).1; unfold Wealth.low soft; simp_rw [hv, g.sky_tap (H:=H) Q.summer.seen (μPitch Q p) _ t] -- tune defeq
lemma central_ (i:Root (More N))(v:retained A F.M i)(r:Site (More N))(t:r∈ Wealth.depot F.M i): plan A R r∈ Peel.stem (own A R (block A F.M i)) 1:=by -- `r∈` syntax fix
 let h:= t; have hu:= Hazel.moment_p A le_rfl (near_zone Q.high i v h) -- drop
 have he:delta (Fin.tail (central i)) (Fin.tail r)≤R.L.val:=by apply (tail_sep ..).trans; refine le_trans (b:=F.M+2) (halo_xy.mp (central_mem F.M i |>.2.2 h)) ?_; have hv:= copy Q p; have hx:=Q.high.large; omega
 exact (stem_t ..).2 ⟨hu,tang_rad R _ _ he⟩
lemma diameterM (i:Root (More N))(h:retained A F.M i)(t:Peel.stem (own A R (block A F.M i)) 2⊆ S): Agrees (Wealth.depot F.M i) (H.port (ξ₁).val) (H.port (ξ₂).val):=by
 intro j v u; have he:Peel.stem (plan A R j.1) 1⊆ S:=fun k p'=>t (stem_join (r:=1) (t:=1) (central_ Q p g i h j.1 v) p'); exact g.stokes Q.summer.seen (μPitch Q p) j (inside_iff ..|>.mpr ⟨near_zone Q.high i h v,near_zone Q.high i h u⟩) he
lemma forceForm (i:Root (More N))(h:retained A F.M i)(t: Peel.stem (own A R (block A F.M i)) 2⊆ S): form V.path F.M i (perturbY H (ξ₁).val)=form V.path F.M i (perturbY H (ξ₂).val):=by
 have hv : 3*F.M ≤ R.L.val:= by have he:=copy Q p; omega
 exact shape_seen F.M V.path i h Q.high _ _ (fun j f=> refit Q p g j (fun i' u=> t (stem_join (r:=1) (t:=1) (Peel.radial _ _ (danger_sub i A _ f) hv) u))) -- tune
lemma tinRead(i: Root (More N))(t:Peel.stem (own A R (block A F.M i)) 2⊆ S):tinW H F (ξ₁).val i=tinW H F (ξ₂).val i:=by
 by_cases b:retained A F.M i; swap; · simp [tinW,Θ,b] -- tune outer
 have v: 3*F.M≤R.L.val:=by have hx:=copy Q p; omega
 have he: regular (X:=A) (M:=F.M) (ξ₁).val.1.1 i↔ regular (X:=A) (M:=F.M) (ξ₂).val.1.1 i:=use_same (fun j p'=>(g.controls j (t (stem_mid _ (by norm_num : 1≤2) (Peel.radial _ _ p' v)))).1); unfold tinW; simp only [Θ,mem_filter,mem_univ,true_and, he]; split; next p'=>
    unfold mellow error; rw [(merit _ _ _ _ _ F.work Q.chef Q.ageP i).1.loc _ _ (diameterM Q p g i b t)]; unfold first second; rw [forceForm Q p g i b t] -- tune
 next v=>rfl
lemma coldRead (i:A.Hcols)(v: Peel.stem (own A R i) 3 ⊆ S): cold H F (ξ₁).val i=cold H F (ξ₂).val i:=by
 have hp:Peel.stem (own A R i) 1⊆ S:=(stem_mid _ (by norm_num)).trans v; have hm(a:ℕ)(v:a≤R.L.val):state (columnBall A i a) (ξ₁).val.1.1 (ξ₂).val.1.1:=fun j t=> (g.controls _ (hp (Peel.radial i j t v))).1; unfold cold; simp only [show i∈ (ξ₁).val.1.1 ↔ i∈(ξ₂).val.1.1 from (g.controls i (hp (stem_home ..))).1]; split; next p'=>
    have hf:= Q.jac.local_burden (H.P.heightClose H.y) i _ _ (hm _ p.tail); unfold Recipe.force; rw [hf]; apply congrArg (· - Real.log (job_m B.D H.J H.y)); apply congrArg (·+ _); unfold Wealth.pays; rw [book_local _ i (hm _ (copy Q p))]; apply sum_congr rfl; intro j l; have he:= (mem_filter.mp (show j∈bookS _ _ _ _ from l)).1; have H': retained A F.M j:=(mem_filter.mp he).2; have hv':3*F.M≤R.L.val:=by have h:=copy Q p; omega
    have ht:Peel.stem (own A R (block A F.M j)) 2⊆S:=fun _ t=> v (stem_join (r:=1) (t:=2) (stem_flip (Peel.radial _ _ (danger_sub j _ _ (mem_inter.mp (book_t _ l)).2) hv')) t); unfold spent; rw [(merit _ _ _ _ _ F.work Q.chef Q.ageP j).1.loc _ _ (diameterM Q p g j H' ht)]; unfold first; rw [forceForm Q p g j H' ht]
 next v=>rfl -- tuning abst
end Mangrove
end YM.CF.BPress.Peel

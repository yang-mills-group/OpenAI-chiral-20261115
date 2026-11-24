import YM.CF.DPress.FD.Stock.Past
/-! Actual Roof legality of the `min_s Soup` Basic family. Adapt general `sun` dive
 and `Week` conditions; not claiming the output is an actual small-range map of its
 two regulator arguments. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Spire Skye Cash Deck MeasureTheory Cube SU Lat Finset Wilson Laurent
open scoped Topology BigOperators ENNReal NNReal Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{I:Type}[Fintype I]{r d:ℕ}{u t:ℝ}
namespace Spoke
variable (X:Scout I n u t r) (f:ℕ→ℝ→I)
local notation "D"=> Support (More n)
lemma Basic_more{P:Pane n→Pane n}(p:Basic n P u t r)(v:r ≤ d): Basic n P u t d:=⟨p.legal,p.meas,fun X i g=> p.covers X i (Disjoint.mono_right (show win r i⊆_ from Turf.windowP v (Finset.Subset.refl _)) g),fun X Y i h=> p.shore _ _ _ (agrees_mono h (Finset.coe_subset.mpr (Turf.windowP v (Finset.Subset.refl _))))⟩
lemma extendB {H: D}{i:reach n}{c:Ids n}{Y:Pane n}(u:H.Nonempty) :well X f H Y i c=mend (X.X (f H.card (bonnet H c).1)) (bonnet H c).2.1 Y i:= if_pos u
lemma shadow {i:reach n}{V:Orbit n}{Q:Pane n→Pane n}(p:Basic n Q u t d) (h:¬(soup (RG.flags u V.1) d i).Nonempty) : glow X f d V i= Q V.1 i:= by
 rw [glow,well,if_neg h,p.covers _ _ (not_not.mp (fun v=> h ((pieV ..).2 v)))]
lemma lit_g (i:Ids n) (Y:Pane n)(p:r≤d): RG.flags t (glow X f d (Y,i))=∅:=by
 let G:=glow X f d (Y,i); apply Skye.broad; intro x; let A:=RG.touched x; let S:=soup (RG.flags u Y) d;
 obtain ⟨Z,w,z⟩ :∃ Z:Pane n, RG.flags t Z=∅ ∧ Agrees A G Z :=by
    by_cases v:∃ i,Skye.ends i⊆ A∧ (S i).Nonempty; swap
    · obtain ⟨I⟩:= ok X.V.c; refine ⟨X.X I Y,(X.basicF _).legal Y,fun i u k=>?_⟩; exact shadow X f (V:=(Y, _)) (Basic_more (X.basicF I) p) (fun h=> v ⟨i,by rw [Skye.ends,insert_subset_iff,singleton_subset_iff]; exact ⟨u,k⟩,h⟩)
    obtain ⟨a,e,t'⟩:=v; let k:=bonnet (S a) i; let Q:=mend (X.X (f (S a).card k.1)) k.2.1; have ht:Basic n Q u t d:=Basic_more (mine (X.basicF _) _) p; refine ⟨Q Y,ht.legal Y,fun y p v=>?_⟩; by_cases h:(S y).Nonempty; swap; · exact shadow X f ht h
    have hj : ends y ⊆ A:= Finset.insert_subset p (Finset.singleton_subset_iff.mpr v);
    have hg(z:Seat n)(p:z∈ A)(y:Seat n)(q:y∈ A):separation z y ≤ 20:= (separation_triangle z x.1 y).trans ((add_le_add ((separation_comm ..).trans_le (Work.E01.sep_touched x z p)) (Work.E01.sep_touched x y q)).trans (by norm_num))
    change well X f (S y) Y y i= _; rw [show S y=S a from Finset.Subset.antisymm (dives (b:=a) t' (fun i x j y=> hg i (hj x) j (e y))) (dives h (fun i x j y=> hg i (e x) j (hj y)))]; exact extendB X f t'
 by_contra! p; let k:= travel_local x.1 (square _ _) G Z (fun i t v=> z i (List.mem_toFinset.mpr t) (List.mem_toFinset.mpr v)); have hz:x.1∈ RG.flags t Z:= (RG.flags_spec ..).mpr ⟨x,by simp [RG.touched,square,visits], (show faceValue G x=faceValue Z x from k) ▸ p⟩; simp [w] at hz
lemma trans_g{U V:Pane n}{S Z:D}{A B:Ids n}(z:r≤d)(p:Z∩ RG.flags u U=Z∩ RG.flags u V)(w:Week Z S (RG.flags u U) d)(h:Week Z S (RG.flags u V) d)(v:Agrees Z U V)(q:Set.EqOn A B Z):Agrees S (glow X f d (U,A)) (glow X f d (V,B)):=by
 intro i t l; let E:=soup (RG.flags u U) d i; let F:=soup (RG.flags u V) d i; have hv:ends i ⊆ S:= Finset.insert_subset t (Finset.singleton_subset_iff.mpr l); have hx:=w.all i hv; have ht:Agrees (win d i) U V:= agrees_mono v (Finset.coe_subset.mpr hx); have hg(x:Seat n)(p:x∈ E):x∈Z:=w.mask _ hv _ p (halo_subset _ _ (mem_singleton_self x));
 change well X f E U i A= well X f F V i B; rw [show F=E from ?_]; swap; · exact (suppC _ _ Z d i (by rw [inter_comm, inter_comm (RG.flags u V),p]) hx (w.mask _ hv) (h.mask _ hv)).symm
 unfold well; split; next g=> rw [show bonnet E A=bonnet E B from ?_,(Basic_more (mine (X.basicF _) _) z).shore U V i ht]; unfold bonnet; rw [mastL E (priorP A) (priorP B) (fun i t=> congrArg Prod.fst (q (hg i t))),q (hg _ (mastP E g _).1)]
 next g=> exact ht i (halo_subset _ _ (by simp)) (halo_subset _ _ (by simp))
lemma ray_t (v:r≤d)(X' Y:Pane n)(A B:Ids n)(Z S: D)(p:Z∩ RG.flags u X'=Z∩ RG.flags u Y)(w:Week Z S (RG.flags u X') d)(h:Week Z S (RG.flags u Y) d)(k:Agrees Z X' Y)(m:Set.EqOn A B Z):Agrees S (ray X f d (X',A)) (ray X f d (Y,B)):=by
 let U:= gauge (frameP A) X'; let V:= gauge (frameP B) Y; have he:RG.flags u U=RG.flags u X':= RG.gauge_flags ..; have hf:RG.flags u V=RG.flags u Y:=RG.gauge_flags ..
 have hg:= trans_g X f v (U:=U) (V:=V) (by rwa [he,hf]) (he.symm ▸ w) (hf.symm ▸ h) (tied _ _ _ _ _ k (fun i p=> by unfold frameP; rw [m p])) m -- watch ambiguous
 intro i vi wi; let hp:ends i⊆S:= Finset.insert_subset vi (Finset.singleton_subset_iff.mpr wi); let hx:ends i⊆Z:=(halo_subset d _).trans (w.all i hp); unfold ray; simp only [Lattice.gauge, frameP,Pi.inv_apply, m (show i.1∈↑Z from hx (by simp)),m (show i.1+step i.2 ∈↑Z from hx (by simp))] -- unfolds frameP in gw body not defeq for use?
 exact congrArg (fun v=>_*v*_) (hg i vi wi)
end Spoke
end YM.CF.DPress.FD

import YM.SU5.FiniteGaugeData.Brique.Rushmore
import YM.Next.RANK.LoomNative

/-!
Geometry for the many-mode measurements. Here boxes at gauge spacing wrap by `More n` while the sparse taps wrap by `n`. All purchases which finally use the norm estimate are on a literal fit, not at aliased supports. Re-use the native trunk lemmas for the mask (exact finite spindle, all fields).
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin Window.Brique Heat
open Reed (Fine)
attribute [local instance] opCStarAlgebra
-- `open Next.Rank.Spindle` ? shadow other `Word` etc. prefer qualified
open Next.Rank
open scoped Classical
variable {r n d m g h w:ℕ} {x o y:Cover}{N:Side}

abbrev scape (o:Cover)(r:ℕ): Finset Cover:= (Lattice.box r).image (fun a=>a+o)
lemma sap{x o:Cover}{r:ℕ}: x∈scape o r ↔ x-o∈Lattice.box r:=by
 constructor <;> intro hx
 · obtain ⟨a,u,rfl⟩:= mem_image.mp hx; simpa using u
 exact mem_image.mpr ⟨_,hx,sub_add_cancel ..⟩
lemma sap_box{x o:Cover}{r:ℕ}: x∈scape o r ↔ ∀ a:Axis,o a-r ≤ x a ∧ x a ≤ o a+r := by
 rw [sap,Lattice.box_test]; constructor <;> intro h
 · intro a; have i:=h.1 a; have j:=h.2 a; rw [Pi.sub_apply] at i j; omega
 constructor <;> intro a <;> rw [Pi.sub_apply] <;> have t:=h a <;> omega
lemma scape_shape(o:Cover)(r:ℕ): ∀ a:Axis,∃ p:ℤ, ∀ x∈ scape o r,p≤x a∧x a ≤ p+(2*r:ℕ):= by
 intro a; refine ⟨o a-r,fun x hx=>?_⟩; have he:=sap_box.mp hx a; omega
lemma scape_mono (h:r ≤ m): scape o r ⊆ scape o m:=fun x hx=> sap_box.mpr (fun a => by have he:=sap_box.mp hx a; omega)
lemma sap_here (x:Cover)(r:ℕ): x∈scape x r:=sap_box.mpr fun a=>by omega
lemma sap_along(h:x∈scape o r)(u:y∈scape x m): y∈ scape o (r+m):= sap_box.mpr (fun a=> by have he:=sap_box.mp h a; have hu:=sap_box.mp u a; omega)
lemma spindle_PATCH (o:Cover)(r:ℕ)(n:Side): region (scape o r) n= Spindle.patch r (wrap (More n) o):= by
 rw [Spindle.patch_eq]; unfold region scape; rw [image_image]; exact image_congr fun a _=> map_add (wrap (More n)) a o
lemma halo_walk(P r:ℕ)(o:Cover)(n:Side): Lattice.halo r (region (scape o P) n) ⊆ region (scape o (P+r)) n:=by
 rw [spindle_PATCH,spindle_PATCH]; intro x hx; obtain ⟨y,h,v⟩:= halo_spec.mp hx; exact (Spindle.doors x).2 ((separation_triangle ..).trans (add_le_add ((Spindle.doors y).1 h) v))
lemma vision_box {y:Cover}(p:x∈scape o r){u:Walk}(h:y∈visits x u): y∈ scape o (r+u.length):= by
 induction u generalizing x y r with
 | nil => rw [show y=x from List.mem_singleton.mp h]; exact p
 | cons i u ih=>
    rcases List.mem_cons.mp h with v|v; exact scape_mono (show r ≤ r+ (i::u).length by omega) (v ▸ p)
    have he:x+i.vec∈ scape o (r+1):=sap_along p (sap_box.mpr (fun a=>by
       simp only [Pi.add_apply, Nat.cast_one]; rw [Step.vec]; split <;> (simp only [Pi.neg_apply,step_apply] <;> split) <;> omega))
    have hz:r+1+u.length=r+(i::u).length:=by rw [List.length_cons]; omega
    exact hz ▸ ih he v
-- Ahead placement at scale of W. Plane dilation user chosen separately after pick. Need Y.read no covariance of state assumptions.
lemma habitat(a:Axis)(r l:ℕ)(z:ℤ): ∃ o:Cover,Ahead a z l (scape (nodeC o) r):= by
 refine ⟨(fun _=>|z|+r+l),?_⟩; intro x hx; apply le_trans ?_ ((sap_box.mp hx a).1); simp only [nodeC,Pi.add_apply,two_smul,Pi.one_apply]; change _ ≤ ((|z|+r+l)+(|z|+r+l)+1)- r; have he:=abs_nonneg z; have hp:= le_abs_self z; omega

abbrev Sept(m:ℕ):=Four (Fin m)
private abbrev dotL(d m:ℕ)(x:Sept m):Cover:=fun i=> ↑((d+1)*(x i).val)
private def ditL(d m:ℕ)(x:Sept m)(i:Axis):ℕ:= ((d+1)*(x i).val)
def vergeCover (y:Cover)(d m:ℕ): Finset Cover:= univ.image (fun x: Sept m=>y+dotL d m x)
-- p (ceil). ensures cardinal; pilot bound diagonal, sparse off diagonal. 
def spreadB(d m:ℕ):ℕ:=2*(d+1)*m
lemma chordC(p:x∈vergeCover y d m): nodeC x∈scape (nodeC y) (spreadB d m):=by
 obtain ⟨u,h,rfl⟩:=mem_image.mp p; apply sap_box.mpr; intro a
 let k:ℕ:=ditL d m u a; have he:k<(d+1)*m:=Nat.mul_lt_mul_of_pos_left (u a).isLt (by omega); change (nodeC y a - (spreadB d m:ℕ) ≤ _ ∧ _)
 simp only [nodeC, Pi.add_apply, two_smul,Pi.one_apply,spreadB,mul_assoc (2:ℕ) (d+1) m,dotL]; unfold k ditL at he; omega
lemma chordN (u:Finset Cover)(m:Side): (u.image (wrap m)).image node= region (u.image nodeC) m := by unfold region; rw [image_image,image_image]; exact image_congr fun a _=> node_of ..
abbrev vergeNative(y:Cover)(d m:ℕ)(M:Side):= (vergeCover y d m).image (wrap M)
private lemma card_cover (y:Cover)(d m:ℕ): (vergeCover y d m).card=m^4:=by
 unfold vergeCover; rw [card_image_of_injective,card_univ]; · simp [Sept,Four,Axis]
 intro a b e; funext i; apply Fin.ext; apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos d); rw [←Nat.cast_inj (R:=ℤ)]; exact congr_fun (add_left_cancel e) i
local notation "N̂"=> vergeNative y d m N
lemma cardinalN (p:Roomy (scape (nodeC y) r) N)(h: spreadB d m ≤ r): (N̂).card=m^4:=by
 unfold vergeNative; rw [←card_cover y d,Finset.card_image_of_injOn]; intro a u b v eq; apply nodeC_inj; apply (roomy_hosp _ p).1 (scape_mono h (chordC u)) (scape_mono h (chordC v)); rw [←node_of,←node_of,eq]
lemma reachN (w:ℕ): halo w ((N̂).image node) ⊆ region (scape (nodeC y) (spreadB d m+w)) N:= by
 unfold vergeNative; rw [chordN]
 have hv:region ((vergeCover y d m).image nodeC) N⊆ region (scape (nodeC y) (spreadB d m)) N:=Finset.image_subset_image fun i v=>by obtain ⟨x,p,rfl⟩:=mem_image.mp v; exact chordC p
 intro i hi; apply halo_walk (spreadB d m) w (nodeC y) N; obtain ⟨x,t,u⟩:=halo_spec.mp hi; exact halo_spec.mpr ⟨x,hv t,u⟩
lemma sparse_stretch (p:2*(2*r+1)<(More N).val)(K: spreadB d m ≤ r) : Sparse d (N̂):=by
 intro a q b Q h; obtain ⟨u,U,rfl⟩:=mem_image.mp q; obtain ⟨v,V,rfl⟩:=mem_image.mp Q; rw [node_of,node_of,separation,←map_sub];
 have he:=Spindle.borne p (nodeC u-nodeC v) (sap.mp (show nodeC u∈ scape (nodeC v) (2*r) from sap_box.mpr (fun i=>by have hz:=sap_box.mp (scape_mono K (chordC U)) i; have hx:=sap_box.mp (scape_mono K (chordC V)) i; omega)))
 have x:u≠v:=fun g=> h (g ▸ rfl); obtain ⟨t,g,rfl⟩:= mem_image.mp U; obtain ⟨s,k,rfl⟩:= mem_image.mp V; obtain ⟨i,I⟩:=Function.ne_iff.mp (show s≠t from fun e=>x (e ▸ rfl))
 refine lt_of_lt_of_le ?_ (component_le _ i); rw [he]; simp only [Pi.sub_apply,nodeC,Pi.add_apply,two_smul,Pi.one_apply,dotL]
 have G : (s i).val≠ (t i).val:= fun p=>I (Fin.ext p); rcases lt_or_gt_of_ne G with u|u
 all_goals have F:=Nat.mul_le_mul_left (d+1) u; rw [Nat.mul_succ] at F; omega

abbrev rateD (r:ℕ):= 2*r
abbrev sphereR (r J:ℕ):ℕ:=10*(r+J+10) -- marker stencil for Cash
lemma manner(q d w m g:ℕ)(h:2*w+q+10+g ≤ m):
    rateD (sphereR (spreadB d m+w+w) q)+g ≤ allotL d*m:= by
 unfold sphereR spreadB allotL rateD; rw [Nat.mul_assoc 2 (d+1) m,Nat.mul_assoc 100 (d+1) m]; have he:m ≤ (d+1)*m:=by simp [add_mul]
 omega
end YM.CF.Buffered.Afterglow.Hierarchy.Quest

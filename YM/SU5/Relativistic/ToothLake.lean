import YM.SU5.Relativistic.Baker
import YM.SU5.FiniteGaugeData.Pannier.PaleFace
import YM.CF.BPress.Spin.Window
/-! # geometric patching for LOCAL flat comparison. Small relative seam for any given Winter margin.
 Supports of marks NEVER required to be adapted to this tiling. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open _root_.YM.CF.Papyrus.Mosaic
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {N C:Side}(L:Ratio C (More N)){r w k:ℕ}
private def heart (w:ℕ)(x:Site C): Seat N:=setDown L x (fun _=>w)
private lemma hearts (h:L.count.val=2*w+1)(i:Site C) (x:Site L.count): setDown L i x∈BlockP w (heart L w i):=by
 let c:=heart L w i; let Y: Site L.count:=fun _=> w; let Z:= (topUp x-topUp Y); have he(j): ((Y j): Per L.count).val=w:= ZMod.val_natCast_of_lt (by omega)
 rw [show setDown L i x=c+wrap (More N) Z from (by unfold c heart Z setDown; rw [map_sub]; abel), blocks_test,add_comm]; apply Work.E08.separation_box_add _
 refine box_test.mpr ⟨fun j=>?_,fun j=>?_⟩
 all_goals
    first|change -(w:ℤ) ≤ ((x j).val:ℤ)-(((Y j).val):ℤ)|change (((x j).val):ℤ)-(((Y j).val):ℤ) ≤ (w:ℤ)
    rw [he j]; have ht: (x j).val<L.count.val:= ZMod.val_lt _; omega
private lemma blockTall (o:Seat N)(h:2*k<(More N).val): (BlockP k o).card=(2*k+1)^4:=by
 rw [show BlockP k o = bay (terr (More N)) o k from (by ext; rw [blocks_test,bay_mem]; rfl),BPress.Spin.Eye.volume _ h]; congr 2; omega
private lemma certain (h:L.count.val=2*w+1)(x:Site C) (q:2*w < (More N).val) : univ.image (setDown L x) = BlockP w (heart L w x):=by
 apply eq_of_subset_of_card_le; · exact image_subset_iff.mpr (fun i _=>hearts L h x i)
 rw [card_image_of_injective _ (fun i j z=>congrArg Prod.snd (show (x,i)=(x,j) from set_inj L z)),card_univ,Lattice.site_card,blockTall _ q,h] -- include L blockTall? not included
private lemma pole_id (h:L.count.val=2*w+1)(x:Site C)(q:2*w < (More N).val){v: Seat N}(z:v∈BlockP w (heart L w x)): (slot L|>.symm v).1=x:=by
 rw [← certain L h x q] at z; obtain ⟨i,_,rfl⟩:= mem_image.mp z; change ((slot L).symm (slot L (x,i))).1=x; simp
private lemma weightS (h:L.count.val=2*w+1)(q:2*w < (More N).val)(t:r≤w)(F:Finset (Site C)) :
    (F.biUnion fun i=> BlockP r (heart L w i)).card=F.card * (2*r+1)^4:=by
 rw [card_biUnion]; · simp only [blockTall (heart L w _) (show 2*r < (More N).val by omega),sum_const,nsmul_eq_mul,Nat.cast_id]
 intro i g j p y; apply Finset.disjoint_left.mpr; intro z a b; apply y; exact (pole_id L h i q (blocks_test.mpr ((blocks_test.mp a).trans t))).symm.trans (pole_id L h j q (blocks_test.mpr ((blocks_test.mp b).trans t)))
private lemma arboreal(h:L.count.val=2*w+1)(q:2*w < (More N).val) {r k:ℕ}(Y:Pane N)(F: Finset (Site C))(e: r+k+1≤ w) (m:Seat N→ E) (a:ℝ)(O:∀ i∈F, Rightful (BlockP w (heart L w i)) (gauge m Y) 1 a) :
    Rightful (Lattice.halo k (F.biUnion fun i=>BlockP r (heart L w i))) (gauge m Y) 1 a:=by
 intro j hX; obtain ⟨g,hk,v⟩:= halo_spec.mp (mem_filter.mp hX).2.1 -- lost membership hp
 obtain ⟨i,ip,f⟩:=mem_biUnion.mp hk
 let c:=heart L w i; have hv: separation c j.1≤r+k:= (separation_triangle c g j.1).trans (Nat.add_le_add ((blocks_test).mp f) v)
 exact O i ip j (mem_filter.mpr ⟨mem_univ _,blocks_test.mpr (hv.trans (by omega)),blocks_test.mpr ((separation_triangle ..).trans ((Nat.add_le_add hv (Work.E01.sep_step_le j.1 j.2)).trans e))⟩)
-- Existence of one local gauge on large volumes. Geometry outside and flags finite. mask pay.
lemma wallMaps (h:L.count.val=2*w+1)(q:2*(w+1)<(More N).val){B:ℝ}(Y:Pane N)(v a:ℝ)(f:∀ x:Seat N, Disjoint (BlockP (w+1) x) (RG.flags v Y) → Rightful (BlockP w x) (gauge (stampG x Y) Y) 1 a)(t:r+k+1≤w)
    (e: ((Lattice.halo (w+1) (RG.flags v Y)).card:ℝ) ≤ B) :
    ∃ S:Finset (Seat N),∃ m:Seat N→ E, Rightful (Lattice.halo k S) (gauge m Y) 1 a ∧ (Sᶜ.card:ℝ) ≤ (C.val:ℝ)^4* ((2*w+1:ℝ)^4-(2*r+1:ℝ)^4)+ B*(2*r+1:ℝ)^4 :=by
 let F':= (univ : Finset (Site C)).filter fun i=> heart L w i∈ Lattice.halo (w+1) (RG.flags v Y)
 let F:= F'ᶜ; let S:= F.biUnion fun i=> BlockP r (heart L w i); let m(x:Seat N):E:= stampG (heart L w ((slot L).symm x).1) Y x
 have hr(x)(d:x∈F): Disjoint (BlockP (w+1) (heart L w x)) (RG.flags v Y):=by
    apply Finset.disjoint_left.mpr; intro i z y; exact mem_compl.mp d (mem_filter.mpr ⟨mem_univ _,halo_spec.mpr ⟨i,y,(separation_comm ..).trans_le (blocks_test.mp z)⟩⟩)
 have hm:(F'.card:ℝ)≤ B:=by
    rw [← card_image_of_injective _ (show Injective (heart L w) from fun i j e=> congrArg Prod.fst ((slot L).injective (show slot L (i,fun _=>(w:Per L.count))=slot L (j,fun _=>(w:Per L.count)) from e)))]
    apply (Nat.cast_le.mpr (card_le_card _)).trans e; exact image_subset_iff.mpr (fun i h=> (mem_filter.mp h).2)
 have hu:2*w<(More N).val:=by omega
 refine ⟨S,m,arboreal L h hu Y F t m a (fun i u=>?_),?_⟩
 · let H:= heart L w i; apply (riotPort ..).2; intro j y; have hp(x:Seat N)(p:x∈BlockP w H):m x=stampG H Y x:=by unfold m H; rw [pole_id L h i hu p]
   rw [show Lattice.gauge m Y j=Lattice.gauge (stampG H Y) Y j from (by unfold Lattice.gauge; rw [hp _ (mem_filter.mp y).2.1,hp _ (mem_filter.mp y).2.2])]; exact (riotPort ..).1 (f _ (hr i u)) j y
 have hs:F.card+F'.card=C.val^4:=by rw [show F=F'ᶜ from rfl,card_compl_add_card,site_card]
 have hv':((Sᶜ.card+F.card*(2*r+1)^4:ℕ):ℝ)=C.val^4*(2*w+1:ℝ)^4:=by
    rw [←weightS L h hu (by omega) F, show Sᶜ.card+S.card=Fintype.card (Seat N) from card_compl_add_card _,Lattice.site_card,L.exact_size,h]; push_cast; ring
 have hh: (F.card:ℝ)=(C.val:ℝ)^4-F'.card:=eq_sub_of_add_eq (by exact_mod_cast hs); push_cast at hv'; rw [hh] at hv'; linarith [mul_le_mul_of_nonneg_right hm (show 0 ≤ (2*r+1:ℝ)^4 by positivity)] -- parentheses
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.wallMaps

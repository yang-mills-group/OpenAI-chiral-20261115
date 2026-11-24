import YM.SU5.Relativistic.Antlers
/-! # From Layout specs to horizontal budget and Column authentication -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Lifted Afterglow Tapestry Branch Tenant Skye Cliplet RG Brace Crest Crest.Sleet Crest.Sleet.UpStart Satin Tower.SlabMark
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n m:ℕ}(d A:ℕ){K:Calibration}
lemma lumin (F:Waxy)(S:Finset ℤ):∀ᶠ n:ℕ in atTop,∀ (x:ℤ) (w:WalkA), tack w x ∈ district S 0 F→∀ i:Fin 3,(w i).natAbs ≤ n:=by
 let V:=district S 0 F; let s:= V.sup fun x=> (Finset.univ : Finset Axis).sup (fun i=> (x i).natAbs); refine (eventually_ge_atTop s).mono (fun n p x w h i=>?_)
 let u:=tack w x; have he: (u i.castSucc).natAbs ≤ s:= (le_sup (f:=fun j:Axis=> (u j).natAbs) (mem_univ i.castSucc)).trans (le_sup (f:=fun x:Cover=> (Finset.univ:Finset Axis).sup (fun i=>(x i).natAbs)) h); rw [show u i.castSucc=w i from tack_left ..] at he; exact he.trans p
abbrev hatch (m:ℕ)(d:ℕ) := 8*((d+1)*m)
lemma horizon_cost (F:Waxy)(V:ℕ):∀ᶠ m:ℕ in atTop, ∃ X:Cover, Transom TA (loftH m d A V F) X (hatch m d):=by
 filter_upwards [lumin F (TwistT A),eventually_ge_atTop V,eventually_ge_atTop 1] with m h e p
 let v:=2*((d:ℤ)*(m:ℤ))+1; let L:=-(2*(m:ℤ)); let P:= (v+2*(m:ℤ)); let X:Cover:= fun _=> L
 refine ⟨X,fun i t u w=>?_⟩
 induction i using Fin.lastCases with
 | last=> exact (t rfl).elim
 | cast i=>
    let j:=i.castSucc
    have hX:P≤X j+hatch m d:=by
       unfold X P L v hatch; push_cast; have hf:(1:ℤ)≤ m:= by exact_mod_cast p
       nlinarith only [mul_nonneg (show 0≤ (d:ℤ) by positivity) (show 0≤(m:ℤ) by omega),hf]
    have hs(z:Cover)(g:z∈stains m d A F):X j≤nodeC z j∧ nodeC z j≤P:=by
       rcases mem_union.mp g with g|g
       · obtain ⟨l,_,rfl⟩:=mem_image.mp g; obtain ⟨a,q⟩:=base_span m d A l i; unfold X L P v j; omega
       obtain ⟨l,_,u⟩:=mem_biUnion.mp g; obtain ⟨k,_,u⟩:=mem_biUnion.mp u; obtain ⟨t,v',x⟩:=mem_biUnion.mp u; obtain ⟨y,xq,rfl⟩:=mem_image.mp x
       obtain ⟨a,q⟩:= base_span m d A l i; have hv:= h t y (by simpa only [zero_add] using drive_entry (0:Cover) F k _ t v' y xq) i
       rw [show nodeC (baseX m d A l+tack y t) j=nodeC (baseX m d A l) j+2*y i by unfold j; simp [nodeC,baseX]; ring]
       unfold X L P v j; omega
    rcases mem_union.mp w with g|g
    · rcases mem_union.mp g with g|g
      · have he:archH A j=0:=by simp [archH,j]
        have hu: X j≤0:=by unfold X L; omega
        have hh:0≤P:=by unfold P v; positivity
        rcases mem_insert.mp g with g|g; subst u; exact ⟨he ▸ hu,he ▸ hh.trans hX⟩
        apply via_lim _ _ _ _ _ (he ▸ hu) (le_trans (he ▸ hh) hX) _ _ g; intro z v; exact ⟨(hs _ (mem_union_right _ v)).1,(hs _ (mem_union_right _ v)).2.trans hX⟩
      obtain ⟨u,vq,rfl⟩:= mem_image.mp g; exact ⟨(hs u vq).1,(hs u vq).2.trans hX⟩
    obtain ⟨a,_,u⟩:=mem_biUnion.mp g; obtain ⟨z,b,rfl⟩:=mem_image.mp u
    obtain ⟨g,f⟩:= base_span m d A a i; obtain ⟨b,e'⟩:=box_test.mp b; specialize b j; specialize e' j; change _≤v at f
    change L ≤ z j+nodeC (baseX m d A a) j∧ z j+_ ≤ _; constructor
    · unfold j at *; unfold L; omega
    apply le_trans _ hX; unfold j at *; unfold P; omega

lemma disperse (C:Finset Cover):∃ W:ℕ,∀ z∈C,∀ x∈C,∀ n:Side,W≤n.val→ lift (wrap n z-wrap n x)=z-x:=by
 let D(z:Cover):ℕ:= univ.sup fun i:Axis=> (z i).natAbs; let p:= C.sup D; have he(i:Cover)(g:i∈C)(j:Axis): (i j).natAbs≤p:= (le_sup (s:=Finset.univ) (f:=fun j:Axis=> (i j).natAbs) (mem_univ j)).trans (le_sup (f:=D) g)
 refine ⟨4*p+1,fun z h x t n u=>lift_eq_iff.mpr ⟨(map_sub ..).symm,fun i=>?_⟩⟩; have hz:=he z h i; have hv:=he x t i; simp only [Pi.sub_apply]; omega
lemma disperse_wrap (C:Finset Cover):∃ W:ℕ,∀ n:Side, W≤ n.val→Set.InjOn (wrap n) C:=by obtain ⟨W,x⟩:=disperse C; refine ⟨W,fun n p z t y g h=>?_⟩; have he:= x z t y g n p; rw [h] at he; exact sub_eq_zero.mp (he.symm.trans ((x y g y g n p).trans (sub_self _)))
lemma long_cost (C:Finset Cover)(o:Cover):∃ R:ℕ,∀ n:Side,∀ x∈C,separation (wrap n o) (wrap n x)≤ R:=by
 let D(x:Cover):= Finset.univ.sup fun i:Axis=> ((x-o) i).natAbs
 refine ⟨C.sup D,fun n x h=>?_⟩
 have hg:x-o∈box (D x):=by
    have he(i:Axis): ((x-o) i).natAbs≤D x:=Finset.le_sup (s:=Finset.univ) (f:=fun j:Axis=> ((x-o) j).natAbs) (mem_univ i)
    exact box_test.mpr ⟨fun i=>by have hp:=he i; omega,fun i=>by have hp:=he i; omega⟩
 have he:= Work.E08.separation_box_add (wrap n o) hg; rw [map_sub,sub_add_cancel] at he; exact he.trans (le_sup h)

lemma extras(V m:ℕ)(F:Waxy)(n:Side) : let G:= fun i=> wrap (More n) (nodeC (baseX m d A i)); let T:= Finset.univ.image G
        Lattice.halo V T ⊆ region (loftH m d A V F) n:=by
 intro G T x h; obtain ⟨y,u,e⟩:= halo_spec.mp h; obtain ⟨i,_,rfl⟩:=mem_image.mp u; let z:= lift (x-G i); have hx: z∈ box V:=by
    have he':pdist (x-G i) ≤ V:= (separation_comm ..).trans_le e; have ht(a:Axis): (z a).natAbs≤V:= (component_le _ a).trans he'
    exact box_test.mpr ⟨fun i=>by have hx:=ht i; omega,fun i=>by have hx:=ht i; omega⟩
 let L:= nodeC (baseX m d A i); refine mem_image.mpr ⟨z+L,mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ i,mem_image_of_mem _ hx⟩),?_⟩
 rw [map_add,show wrap _ z=x-G i from wrap_lift _]; exact sub_add_cancel ..

lemma lodges_cost (p:0<d)(q:ℕ)(h:q≤2*d)(m V:ℕ)(F:Waxy):∃ Z:ℕ,∀ n:Side,Z≤n.val→ let G:= fun i=> wrap (More n) (nodeC (baseX m d A i)); Injective G∧ Sparse q (Finset.univ.image G) ∧ Set.InjOn (wrap n) (stains m d A F)∧
    ∀ z∈ stains m d A F,march (wrap (More n) (archH A)) (wrap (More n) (nodeC z)) 1=TrackV (archH A) z:=by
 let C:= loftH m d A V F; obtain ⟨Z,t⟩:= disperse C; obtain ⟨U,s⟩:= disperse_wrap (stains m d A F); refine ⟨Z+U,fun n e=>?_⟩
 have f: Z ≤ (More n).val:=by change Z ≤ n.val * 2; omega
 intro G; let P(i):= nodeC (baseX m d A i)
 have hp(i j)(g:i≠j): 2*d ≤ separation (G i) (G j):=by
    obtain ⟨a,u⟩:= diverge m d A i j g; let k:= a.castSucc
    have ht: ((P i-P j) k).natAbs≤ separation (G i) (G j):= (show lift (G i-G j)=P i-P j from t (P i) (base_stay m d A V F _).2 (P j) (base_stay m d A V F _).2 (More n) f) ▸ component_le (G i-G j) k
    apply le_trans _ ht; change _ ≤ (nodeC (baseX m d A i) a.castSucc-nodeC (baseX m d A j) a.castSucc).natAbs; rw [← Int.natCast_natAbs] at u; omega
 refine ⟨fun i j u=>?_,?_,s n (by omega),fun z h=>?_⟩
 · by_contra v; have ht:=hp i j v; rw [u,separation_self] at ht; omega
 · intro a v y g t; obtain ⟨i,_,rfl⟩:=mem_image.mp v; obtain ⟨j,_,rfl⟩:=mem_image.mp g; exact h.trans (hp i j (fun x=>t (congrArg G x)))
 let x:=archH A; unfold march; rw [t (nodeC z) (span_soil m d A F z h) x (mem_union_left _ (mem_union_left _ (mem_insert_self ..))) (More n) f]; simp only [route, TrackV,axisRoute, Pi.sub_apply,Pi.zero_apply,sub_zero]; rfl
end YM.CF.Pannier.Chancel.ScreeV

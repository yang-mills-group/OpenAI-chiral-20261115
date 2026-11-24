import YM.CF.Acorn.Shod
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Lattice Cube Broc Drapes Tulip Peaks Brace Paige Rush Matrix Jet
open scoped Topology Matrix BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L B:Side}{ho:Odd L.val}{T:Script Male}{Y:Pricing j L ho T}{e:ℝ}{m:Side}(g:Grasp Y B e)(n:ℕ)(K:ℝ)(S:Broc.Table m B)
def farmX(S:Broc.Table m B) (e:ℝ):Light (Site (Domain m B)) (Castle m B e S) Unit where
 frame:=terr _
 rel R x y:=∀ i, Agrees R (x.val i) (y.val i)
 expands s t h x y p i j v u:=p i j (h v) (h u)
 dress _ x := x
def dealX(e:ℝ):Draw (Castle m B e S):=⟨fun E _ _ _ U f=>∀ x∈U,∀ i, TransK n (fun u=>(f u).val i) x K⟩
def capeX(S:Broc.Table m B):= (@univ Bool _) ×ˢ complexA m B S
abbrev Boat(m B:Side)(S:Broc.Table m B)(e:ℝ):= Sam (Shorn (e:=e) S)
def LUX(e:ℝ): Lit (Shorn S) (farmX S e) (capeX (m:=m)) where
 pollen _:= MeasurableEquiv.refl _
 level _:=MeasurePreserving.id _
 gauge _ _ _:=rfl
 phase:=sh_c S
 spread a b h i p:=mem_product.mpr ⟨mem_univ _,complex_up m B h (mem_product.mp p).2⟩
lemma capeL(x:Castle m B e S)(Q:Broc.Table m B):Bank (Shorn S x) (capeX Q):=by intro i hi j g; change j∈(if _ then _ else _) at g; split at g; obtain ⟨a,v,rfl⟩:= mem_image.mp g; exact mem_product.mpr ⟨mem_univ _,complex_down m B Q i.2 (mem_product.mp hi).2 v⟩; simp at g
lemma cape_h(Q:Broc.Table m B)(x y:Castle m B e S)(h:(farmX S e).rel Q x y)(t): sails (Shorn S x) (capeX Q) t=sails (Shorn S y) (capeX Q) t :=by
 apply prod_congr rfl; intro i v; rw [run_eq,run_eq]
 split; swap; rfl
 have hp:= (mem_product.mp v).2; exact water_limit _ _ _ _ _ (fun _ _=> rfl) (fun j a b=> h i.1 j ((mem_filter.mp hp).2 a) ((mem_filter.mp hp).2 b))
def artX(e:ℝ): Draw (Boat m B S e):=⟨fun E _ _ _ V f=>∀ x∈V,∀ i, TransK n (fun p=>(f p).val.1.val i) x K ∧ ToR n (fun p=>marr S i (f p).val.2) x K⟩
lemma played (h:1≤K):∃ C:ℝ,0≤C ∧∀ (m:Side)(S:Broc.Table m B), Inspired (dealX n K S e) (Shorn S) (artX n K S e) C n:=by
 obtain ⟨C,c,H⟩:= ryth n K B h; let V:=max C 1; have hx:C≤V:=le_max_left ..; have hv:1≤V:=le_max_right ..; have hl:0≤V:=zero_le_one.trans hv
 refine ⟨V,hl,fun m S=>⟨hl,fun E _ _ _ W w f p=>?_,?_⟩⟩
 · let M:=(fun i:Bool=> H m E W w (fun x=>(f x).val i) (fun x l=>p x l i))
   have hm(x)(g:x∈W)(t:I (Index m))(r:I (Index m)→Ballot):CashCold (fun u=>(Shorn S (f u)).run t r) x n V:=by
      let T:= M t.1; by_cases h:inky m B S t.1 t.2=t; simp_rw [run_eq,if_pos h]; refine ⟨(T.budget x g t.2 (marr S t.1 r)).mono hx,fun p=> T.cold x g _ _ p⟩ -- tune projections
      simp_rw [run_eq,if_neg h]; exact ⟨allows_const _ (by simpa),fun h=>False.elim (one_ne_zero h)⟩
   exact ⟨w,hl,fun x g t r=> (hm x g t r).1,fun x g t r=> (hm x g t r).2⟩
 intro E _ _ _ U W p t w f P F v h' x hx i
 refine ⟨fun j=> (P x (p hx) i j).germ ?_,fun j=> (allows_const _ ((vote_unit (marr S i v j)).trans_le h)).germ ?_⟩
 · filter_upwards [w.mem_nhds hx] with y s; exact (congrArg (fun x=>SU.fund (x.1.val i j)) (h' y s)).symm
 filter_upwards [w.mem_nhds hx] with y s; exact (congrArg (fun x=>(marr S i x.2 j).val) (h' y s)).symm
abbrev landX(e:ℝ):=newX (farmX S e) (dealX n K S e) n
def tentX(m B:Side)(S:Broc.Table m B): Broc.Table m B:=foam _ (8*B.val) S
def StemX (e:ℝ):Master (Boat m B S e) (Site (Domain m B)) where
 frame:=terr _
 moves T:= (LUX S e).botL.rel (tentX m B T)
 grow Q T h x y p:= (LUX S e).botL.expands _ _ (fun k hk=>by obtain ⟨i,g,w⟩:=mem_biUnion.mp hk; exact mem_biUnion.mpr ⟨i,h g,w⟩) x y p
 draw:= artX n K S e
 k:=n
def loyal (S:Broc.Table m B)(i:Bool)(x:Boat m B S e): Senso m g:=⟨(x.val.1.val i, starfish m B (x.val.1.val i) (marr S i x.val.2)),x.val.1.property.1 i,starK g.capY g.baseY.1 (x.val.1.property.1 i) (Acorn.lake S _ _ x.property i)⟩
lemma boil_x(K:ℝ)(t:1≤K): ∃ C:ℝ,1≤C ∧∀ m:Side,∀ S:Broc.Table m B,∀ i:Bool,Cop (Tier m B n e g.baseline C) (StemX n K S e) (loyal g S i):=by
 obtain ⟨C,c,H⟩:=star_cost n (zero_le_one.trans t) B
 refine ⟨C,t.trans c,fun m S i=>⟨rfl,rfl,?_,?_,?_⟩⟩
 · apply Continuous.subtype_mk
   let f:=fun x:Boat m B S e=> (x.val.1.val i,marr S i x.val.2)
   have he: Continuous f:=((show Continuous (fun f:Bool→Skin m B=> f i) from continuous_apply i).comp (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))).prodMk ((marr_c S _).comp (continuous_snd.comp continuous_subtype_val)) -- projections actually missing
   refine (continuous_fst.comp he).prodMk ?_
   exact (starfish_c g.capY g.baseY.1).comp_continuous (f:=f) he (fun x=>⟨x.val.1.property.1 i, Acorn.lake S _ _ x.property i⟩)
 · intro S' x y h; exact ⟨fun j v u=> h.1 i j (foam_in _ _ _ v) (foam_in _ _ _ u), honor _ _ S' (fun j p=>h.2 _ (mem_product.mpr ⟨mem_univ _,show (inky m B S i j).2∈_ from p⟩)) (h.1 i)⟩ -- tune
 intro E _ _ _ U h f H' x hx
 let P:=H' x hx i; let y:=f x
 exact ⟨fun j=>(P.1 j).mono c,H E _ _ _ x P.1 P.2 e _ g.baseY.1 (y.val.1.property.1 i) (Acorn.lake S _ _ y.property i) g.capY⟩
lemma silentX(K:ℝ)(R:Broc.Table m B)(t:Disjoint (tentX m B S) R)(x:Boat m B S e): (Tier m B n e g.baseline K).moves R (loyal g S false x) (loyal g S true x) :=by
 have hx:tentX m B R⊆Sᶜ:=by intro y p; obtain ⟨a,v,h⟩:=mem_biUnion.mp p; refine mem_compl.mpr fun u=> Finset.disjoint_left.mp t ?_ v; exact mem_biUnion.mpr ⟨y,u,(bay_mem _).mpr (by rw [(terr _).sym]; exact (bay_mem _).mp h)⟩
 exact ⟨fun i w p=> x.val.1.property.2 i (hx (foam_in _ _ R w)) (hx (foam_in _ _ R p)), honor _ _ R ((marr_same S _ _ _).less (complex_up m B hx)) (fun i v u=> x.val.1.property.2 i (hx v) (hx u))⟩
end YM.CF.Acorn

import SatinThinVillage
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 860000
set_option maxRecDepth 3600
noncomputable section
namespace YM.CF.Lamour.Bridge.Celeste.Clock
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye CF.Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed
open Py.Rate.Pannier
open Buffered.Afterglow
open Next.Rank.Thirst
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{N:Side}{j r p d Mθ:ℕ}{M:Tulip.Male}{ε ξ σ C D:ℝ}
open Regis.Head Garland Etch AnalyticBridge.VerifiedReset StressFlux RG Pressure
open Push.SectorMeasure Buffered.Lifted Scree
namespace Hookah.Blaze
variable {N n:Side}{G:Gauge}{I:Type} [Fintype I] (z:PlaqAxes→ℝ) (s:Signed) (x:Cover) {m c:ℕ} (a t:ℝ)
open scoped Classical
private lemma visit_at (b:PlaqAxes)(k y:Site n)(h:y∈touched (k,b)) : ∃ c d:Bool,k=atFace y ⟨b.val.1,c⟩ ⟨b.val.2,d⟩:=by
 simp only [touched,List.mem_toFinset, square,visits,Step.vec_pos,Step.vec_neg,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl|rfl|rfl|rfl
 · exact ⟨false,false,by simp [atFace]⟩
 · exact ⟨true,false,by simp [atFace,Step.vec]⟩
 · exact ⟨true,true,by simp only [atFace,↓reduceIte,Step.vec]; (try simp) <;> abel⟩
 · exact ⟨false,true,by simp only [atFace,Bool.false_eq_true,↓reduceIte,Step.vec]; (try simp) <;> abel⟩
 exact ⟨false,false,by simp only [atFace,Bool.false_eq_true,↓reduceIte]; abel⟩
noncomputable abbrev quadD (i:PlaqAxes)(q:Tray) := Lattice.oriented ⟨i.val.1,q.1⟩ ⟨i.val.2,q.2⟩
private lemma vertexP (U:Config G n): pingS t (halo m {0}) U ↔ ∀ y∈ halo m {(0:Site n)},∀ (i:PlaqAxes)(x:Tray), G.chord (travel U y (quadD i x)) < t:=by
 simp_rw [quadD,price_shift_pos G.chord U G.chord_inv (fun x y=> G.chord_conj ..)]; constructor; · intro h y p i j; apply h (atFace y ⟨i.val.1,j.1⟩ ⟨i.val.2,j.2⟩,i); exact not_disjoint_iff.mpr ⟨_,p,Square.touched_here _ _ _ i.property⟩
 rintro h ⟨f,b⟩ t; obtain ⟨g,x,y⟩:= not_disjoint_iff.mp t; obtain ⟨c,d,rfl⟩:=visit_at b f g y; exact h g x b (c,d)
private lemma process(y:Cover)(h:y∈box c) : wrap n y∈halo c {(0:Site n)}:= by
 refine halo_spec.mpr ⟨0,mem_singleton_self _,?_⟩; rw [separation_comm,separation,sub_zero]; exact Work.E01.pdist_wrap_le h
private lemma returnBox {x:Site n}(u:x∈halo c {0}): Lattice.lift x∈ box c:=by
 have hf:pdist x ≤ c:=by simpa [halo_spec,separation_comm (0:Site n) x,separation] using u
 refine box_test.mpr ⟨fun i=>?_,fun i=>?_⟩<;> have h:((Lattice.lift x) i).natAbs ≤ c:= (Finset.le_sup (s:=univ) (f:=fun i=>((Lattice.lift x) i).natAbs) (mem_univ i)).trans hf <;> omega -- named args
/- consultation uses the quad valuation of the stencil in the terrain. -/
def permitCover(U:CoverConfig G):Prop:=∀ y∈box m,∀ (i:PlaqAxes)(x:Tray),G.chord (travel U y (quadD i x)) < t
lemma coverV (U: Config G n): permitCover (m:=m) t (expandAt 0 U)↔ pingS t (halo m {0}) U:=by
 rw [vertexP]; unfold permitCover; simp_rw [travel_at,add_zero]; exact ⟨fun h i t b x=>wrap_lift i ▸ h _ (returnBox t) b x,fun h y t=> h _ (process y t)⟩
lemma on_shift {U:Config G n}: pull s x (expandAt 0 U)=expandAt (0:Site n) (pull s (wrap n x) U):=by
 rw [expandAt_pull,affine,Signed.act_zero,zero_add]; funext i; let j:=((posDir i.2).rotate s); let B:=s.act i.1; let g:=expandAt 0 U; have hx:j.read g (B+x)= j.read (expandAt (wrap n x) U) B:=by
    calc _ = j.read U (wrap n (B+x)):=by simpa [g,travel] using travel_at (0:Site n) U (B+x) [j]
         _ =_:=by rw [map_add]; simpa [travel] using (travel_at (wrap n x) U B [j]).symm
 change j.read _ _ = j.read _ (B+0); rw [add_zero]; exact hx
noncomputable def valueNear (m:ℕ) (x y:ℝ)(s:Signed)(b:Cover)(U: LinksC) : ℝ:= let V:=pull s b U; if permitCover (m:=m) y V then ∑ i:PlaqAxes, z i * ‖x • clover (G:=SU.group) V 0 i.val.1 i.val.2‖ ^2 else 0
abbrev valueFl:=valueNear z 10
lemma valueCovers (U:Pane N): valueFl z a t s x (onC N U)=kris z a t s (wrap (More N) x) U:=by
 unfold valueFl valueNear kris; simp only; unfold onC; rw [on_shift,coverV]; split; swap; rfl
 unfold petalWorth AnalyticBridge.VerifiedReset.petals; have he (i:PlaqAxes): clover (expandAt 0 (pull s (wrap (More N) x) U)) 0 i.val.1 i.val.2 = clover (pull s (wrap (More N) x) U) 0 i.val.1 i.val.2:=by unfold clover stencil plate; simp_rw [travel_at,map_zero,add_zero]
 simp_rw [he]
-- bounding cube and charges even before limits. choose real integer cube width maximal among atlas requirements once and for all lengths. Want orientation independent.
open scoped Pointwise
noncomputable def patioCore (X:Finset Cover) (s:Signed): Finset Cover:= (X ×ˢ (univ : Finset (PlaqAxes × Tray))).biUnion fun i=> (visits (s.act i.1) ((quadD i.2.1 i.2.2).map (·.rotate s))).toFinset
noncomputable def bottomFrame (X:Finset Cover) : Finset Cover:= insert (0:Cover) ((univ: Finset Signed).biUnion (patioCore X))
lemma bottom_center (X:Finset Cover) : (0:Cover)∈ bottomFrame X:=by unfold bottomFrame; simp only [mem_insert_self]
lemma bottom_face (X:Finset Cover) (s:Signed)(y:Cover)(j:PlaqAxes)(q:Tray)(a:Cover)(h:y∈X)(v:a∈ visits (s.act y) ((quadD j q).map (·.rotate s))): a ∈ bottomFrame X:=by unfold bottomFrame patioCore; exact mem_insert_of_mem (mem_biUnion.mpr ⟨s,mem_univ s,mem_biUnion.mpr ⟨(y,j,q),mem_product.mpr ⟨h,mem_univ _⟩,List.mem_toFinset.mpr v⟩⟩)
attribute [irreducible] bottomFrame
abbrev noonFrame:= bottomFrame (Lattice.box 10)
noncomputable def stencilFrame (x:Cover): Finset Cover:= noonFrame.image (fun y=> y+x)
@[simp] lemma loc_frame (x:Cover): x∈ stencilFrame x:= by unfold stencilFrame; exact mem_image.mpr ⟨(0:Cover),(show (0:Cover)∈ noonFrame from bottom_center (Lattice.box 10)),zero_add _⟩
private lemma visits_shift(Y R:Cover)(D:Walk): visits (Y+R) D= (visits Y D).map (fun x=> x+R):=by
 induction D generalizing Y R with | nil=>simp [visits]| cons i v ih=> simp only [visits,List.map_cons]; rw [add_right_comm Y, ih]
noncomputable def shadowFrame (x:Cover)(m:ℕ): Finset Cover:= (bottomFrame (Lattice.box m)).image (fun y=> y+x)
private lemma agrees_site(s:Signed)(x:Cover)(y:Cover)(z:y∈ Lattice.box m) (i:PlaqAxes)(q:Tray) {U V:LinksC}(g:Agrees (shadowFrame x m) U V): travel (pull s x U) y (quadD i q)= travel (pull s x V) y (quadD i q):=by
 rw [travel_pull,travel_pull]; let t:=s.act y; let W:=(quadD i q).map (·.rotate s); apply travel_local; have he(u:Cover)(v:u∈ visits (t+x) W):u∈ shadowFrame x m:=?_
 · exact fun e hx hy=>g e (he _ hx) (he _ hy)
 rw [visits_shift] at v; obtain ⟨a,p,rfl⟩:= List.mem_map.mp v; unfold shadowFrame; apply mem_image_of_mem _ (?_ : a∈ bottomFrame (Lattice.box m)); exact bottom_face (Lattice.box m) s y i q a z p
lemma permit_m(V:PairsC→ LinksC)(h:Continuous V)(m:ℕ):MeasurableSet {U:PairsC| permitCover (G:=SU.group) (m:=m) t (V U)}:=by
   let Q:=(Lattice.box m)×ˢ (univ:Finset (PlaqAxes × Tray));
   have hp:MeasurableSet {U:PairsC| permitCover (m:=m) t (V U)}:=by
      rw [show {U:PairsC| permitCover (m:=m) t (V U)}= ⋂ i:(↥Q), {U|SU.group.chord (travel (V U) i.val.1 (quadD i.val.2.1 i.val.2.2)) < t} from (?_)]
      refine MeasurableSet.iInter fun i=> isOpen_lt (by fun_prop) continuous_const |>.measurableSet
      ext i; refine ⟨fun t=> Set.mem_iInter.mpr fun q:Q=>?_,fun g u v j b=>?_⟩
      · exact t q.val.1 (mem_product.mp q.property).1 _ _
      exact Set.mem_iInter.mp g (⟨(u,j,b),mem_product.mpr ⟨v,mem_univ _⟩⟩: Q)
   exact hp
set_option maxHeartbeats 110000
lemma insideEnv : RG.Envelope ((fun (U:LinksC)=> (valueNear z m a t s x U:ℂ)) ∘ (Prod.fst : PairsC→_)):=by
 let V(U:PairsC):= pull s x U.1; let S(U:LinksC):= ∑ i:PlaqAxes, z i * ‖a • clover U 0 i.val.1 i.val.2‖ ^2; have h:Continuous V:= (show Continuous (pull s x : LinksC→ LinksC) from (by apply continuous_pi; intro i; let d:=(posDir i.2).rotate s; change Continuous (fun U:LinksC=> d.read U (affine s x i.1)); unfold Step.read; split <;> fun_prop)).comp continuous_fst; have hS:Continuous S:= continuous_finsetSum _ fun i _=> by unfold clover StressFlux.stencil; fun_prop
 have hp: MeasurableSet {U:PairsC| permitCover (m:=m) t (V U)}:=permit_m t V h m
 let g(i:PairsC):= if permitCover (m:=m) t (V i) then S (V i) else 0
 exact Girt.pole_w g Complex.ofReal Complex.continuous_ofReal (Envelope.piece hp (Env.compact (hS.comp h)) (Envelope.const (0:ℝ))) -- g composition with coe_ite defeq? tune
lemma insideRead (i j:LinksC)(h:Agrees (shadowFrame x m) i j) : valueNear z m a t s x i=valueNear z m a t s x j:=by
 unfold valueNear; dsimp only; have he(y z w)(t:y∈ Lattice.box m):= agrees_site s x y t z w h; split_ifs with p q q
 · refine sum_congr rfl fun k _=> ?_
   let T:= pull s x i; let V:= pull s x j
   have hp(v:Tray): StressFlux.plate T 0 ⟨k.val.1,v.1⟩ ⟨k.val.2,v.2⟩=StressFlux.plate V 0 ⟨k.val.1,v.1⟩ ⟨k.val.2,v.2⟩:=congrArg SU.group.curvature (he 0 k v (center_box _))
   unfold clover StressFlux.stencil; dsimp only [T,V] at hp
   have hA: plate (pull s x i) 0 (posDir k.val.1) (posDir k.val.2)=plate (pull s x j) 0 (posDir k.val.1) (posDir k.val.2):= hp (false,false); have hB: plate (pull s x i) 0 (posDir k.val.1) (negDir k.val.2)=plate (pull s x j) 0 (posDir k.val.1) (negDir k.val.2):= hp (false,true); have hC: plate (pull s x i) 0 (negDir k.val.1) (posDir k.val.2)=plate (pull s x j) 0 (negDir k.val.1) (posDir k.val.2):= hp (true,false); have hD: plate (pull s x i) 0 (negDir k.val.1) (negDir k.val.2)=plate (pull s x j) 0 (negDir k.val.1) (negDir k.val.2):= hp (true,true); rw [hA,hB,hC,hD]
   
 · exact (q fun y hy j w=> he y j w hy ▸ p y hy j w).elim
 · exact (p fun y hy j w=> (he y j w hy).symm ▸ q y hy j w).elim
 rfl
lemma insideNear : Coeff true (shadowFrame x m) ((fun (U:LinksC)=> (valueNear z m a t s x U: ℂ)) ∘ Prod.fst):=by
 exact ⟨fun v=>by contradiction,insideEnv .., fun _ _ p _=>congrArg ((↑):ℝ→ℂ) (insideRead z s x a t _ _ p)⟩

lemma insideFl : Coeff true (stencilFrame x) ((fun (U:LinksC)=> (valueFl z a t s x U: ℂ)) ∘ Prod.fst):= by apply insideNear (m:=10) z s x a t
end Hookah.Blaze
end YM.CF.Lamour.Bridge.Celeste.Clock
#print axioms YM.CF.Lamour.Bridge.Celeste.Clock.Hookah.Blaze.insideFl

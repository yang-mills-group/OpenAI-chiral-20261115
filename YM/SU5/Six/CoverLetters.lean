import YM.SU5.Six.Bipocket
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
set_option maxHeartbeats 400000
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow.Tapestry Tower
/-!
# Bi-letter characterization on the *cover*

Span of matrices produced at a large observing m -> structure of a Family.
With BOTH Pane arguments unrestricted. Compare Diamond, Filigree, Atlas; here
we only have Borel Envelope (wide), and the letters need to charge their OWN
pockets at the coarse and fine stages -- not just the entire insertion stencil.
-/
variable (K:Calibration)(W:Bool)(S T D:Finset Cover)
-- at a single height: even or odd `InTest`; independent of links. (Used only
-- at appropriate parity and support.)
def LinkIndependent (K:Calibration)(f:Buffered.Family K):Prop:=∀ m x y,f m x=f m y
namespace LinkIndependent
variable {K}
lemma zero': LinkIndependent K 0:=fun _ _ _=>rfl
lemma one': LinkIndependent K 1:=fun _ _ _=>rfl
variable {f g:Buffered.Family K} (h:LinkIndependent K f)
include h
lemma plus' (v:LinkIndependent K g):LinkIndependent K (f+g):= fun i x y=>congrArg₂ (·+·) (h i x y) (v i x y)
lemma scale' (z:ℂ): LinkIndependent K (z • f):= fun i x y=>congrArg (z • ·) (h i x y)
lemma mul' (v:LinkIndependent K g):LinkIndependent K (f*g):= fun i x y=>congrArg₂ (·*·) (h i x y) (v i x y)
end LinkIndependent

-- true for the creator. spin selection literal.
def SinglePocket (u:Bool) : Submodule ℂ (Buffered.Family K):= Submodule.span ℂ {f|∃ (x:Cover)(i:SpinIdx)(b:SU.Slot), nodeC x∈ S ∧ (Window.family b).2=W ∧
  if u then (i∈plusHalf ∧ f=creation K x i b) else (i∉plusHalf ∧ f=removal K x i b)}
lemma pocket_creation {x:Cover}{i:SpinIdx}{b:SU.Slot}(p:nodeC x∈ S)(h:(Window.family b).2=W)(t:i∈plusHalf) : creation K x i b ∈ SinglePocket K W S true:=
  Submodule.subset_span (show _∈_ from ⟨x,i,b,p,h,if_pos rfl ▸ ⟨t,rfl⟩⟩)
lemma pocket_removal {x:Cover}{i:SpinIdx}{b:SU.Slot}(p:nodeC x∈ S)(h:(Window.family b).2=W)(t:i∉plusHalf) : removal K x i b ∈ SinglePocket K W S false:= by
  apply Submodule.subset_span
  exact ⟨x,i,b,p,h,by simp only [Bool.false_eq_true,↓reduceIte]; exact ⟨t,trivial⟩⟩
lemma pocket_test (u:Bool){f:Buffered.Family K}(h:f∈SinglePocket K W S u): InTest K true S true f ∧ LinkIndependent K f:= by
  refine Submodule.span_induction (p:=fun f _=> InTest _ _ _ _ f∧ LinkIndependent K f)
    (fun f t=>?_) ⟨.zero,.zero'⟩ (fun _ _ _ _ r t=> ⟨.add r.1 t.1,r.2.plus' t.2⟩)
    (fun a _ _ t=> ⟨.smul a t.1,t.2.scale' a⟩) h
  obtain ⟨x,i,b,p,_,t⟩:= t
  split at t
  · obtain ⟨h,rfl⟩:= t; exact ⟨.creator b h p, fun _ _ _=>rfl⟩
  obtain ⟨h,rfl⟩:= t; exact ⟨.remover b h p, fun _ _ _=>rfl⟩

def RawPair : Submodule ℂ (Buffered.Family K):= Submodule.span ℂ {f|∃ x ∈ SinglePocket K W T false, ∃ y ∈ SinglePocket K W S true, f=x*y}
def DressedPair : Submodule ℂ (Buffered.Family K):= Submodule.span ℂ {f|∃ g:PairsC→ℂ, Coeff true D g∧∃ x∈ RawPair K W S T, f=scalar K g*x}
lemma raw_test {f:Buffered.Family K}(h:f∈RawPair K W S T) : InTest K true (S∪T) false f∧LinkIndependent K f := by
  refine Submodule.span_induction (p:=fun f _=> InTest _ _ _ _ f∧LinkIndependent K f)
    (fun f t=>?_) ⟨.zero,.zero'⟩ (fun _ _ _ _ r t=> ⟨.add r.1 t.1,r.2.plus' t.2⟩)
    (fun a _ _ t=> ⟨.smul a t.1,t.2.scale' a⟩) h
  obtain ⟨x,p,y,r,rfl⟩:= t
  have he:= pocket_test K W T false p
  have ht:=pocket_test K W S true r
  exact ⟨InTest.mul (he.1.mono subset_union_right) (ht.1.mono subset_union_left),he.2.mul' ht.2⟩
lemma dressed_test {f:Buffered.Family K}(d:S∪T⊆D)(h:f∈DressedPair K W S T D): InTest K true D false f:= by
  refine Submodule.span_induction (p:=fun f _=> InTest _ _ _ _ f)
    (fun f t=>?_) .zero (fun _ _ _ _ r t=> .add r t) (fun a _ _ t=> .smul a t) h
  obtain ⟨g,v,x,y,rfl⟩:=t
  exact InTest.mul (InTest.seed v) ((raw_test K W S T y).1.mono d)

section oneHost
variable (m:Side)
local notation "α" => K.c m
local notation "Q" S:max=> Satin.region S (K.c m)
-- Lift a matrix satisfying the bi-criterion termwise at m; values constant on all links. Antiperiodic winding needed even if already embedded.
private def LiftsTo (V: Submodule ℂ (Buffered.Family K)) : Submodule ℂ (FC (Single (K.c m))) where
  carrier:={x|∃ f∈V, ∀ v:Fields (K.c m), f m v=x}
  zero_mem':= ⟨0,V.zero_mem,fun _=>rfl⟩
  smul_mem' a f h:=by obtain ⟨g,h,v⟩:=h; exact ⟨a • g,V.smul_mem a h,fun i=>congrArg (a • ·) (v i)⟩
  add_mem' h t:=by obtain ⟨f,h,v⟩:=h; obtain ⟨g,t,w⟩:=t; exact ⟨f+g,V.add_mem h t,fun i=>congrArg₂ (·+·) (v i) (w i)⟩
private lemma remove_lift (v:Ket (Single (K.c m))) (h:withinM (Tset (K.c m))ᶜ v)(p:withinM (speciesSet (K.c m) W) v)(u:withinM (modesIn (K.c m) (Q T)) v) : Fock.remove v ∈ LiftsTo K m (SinglePocket K W T false) := by
  let U:=LiftsTo K m (SinglePocket K W T false)
  nth_rw 1 [←basis_expand v]; unfold Fock.remove; rw [map_sum,star_sum]; apply U.sum_mem
  rintro ⟨⟨x,j⟩,t⟩ _; let i:=((x,j),t); rw [map_smul,star_smul]; by_cases hp:v.ofLp i=0; · rw [hp,star_zero,zero_smul]; exact U.zero_mem
  have hk(L:Finset (Single α))(q:withinM L v):i∈L:= Classical.byContradiction fun z=> hp ((within_test ..).1 q _ z)
  apply U.smul_mem
  obtain ⟨w,d,e⟩:=mem_image.mp ((modes_at ..).1 (hk _ u)); obtain ⟨k,a,b⟩:= Tower.wrap_nodes (K.c m) x w e; subst w
  let c:=winding α k
  refine ⟨c • removal K k j t,(SinglePocket K W T false).smul_mem c
    (pocket_removal K W T d ((mem_filter.mp (hk _ p)).2) (fun q=> mem_compl.mp (hk _ h) ((Window.mem_Tset ..).2 q))),?_⟩
  intro y; unfold removal basisC Fock.remove; simp only [Pi.smul_apply,map_smul,star_smul]; rw [show star (winding α k)=c from fee_real _, smul_smul, show c*c=1 from fee_one _,one_smul]; unfold Lifted.index; rw [b]
private lemma create_lift (v:Ket (Single (K.c m))) (h:withinM (Tset (K.c m)) v)(p:withinM (speciesSet (K.c m) W) v)(u:withinM (modesIn (K.c m) (Q S)) v) : create v ∈ LiftsTo K m (SinglePocket K W S true) := by
  let U:=LiftsTo K m (SinglePocket K W S true)
  nth_rw 1 [←basis_expand v]; rw [map_sum]; apply U.sum_mem
  rintro ⟨⟨x,j⟩,t⟩ _; let i:=((x,j),t); rw [map_smul]; by_cases hp:v.ofLp i=0; · rw [hp,zero_smul]; exact U.zero_mem
  have hk(L:Finset (Single α))(q:withinM L v):i∈L:= Classical.byContradiction fun z=> hp ((within_test ..).1 q _ z)
  apply U.smul_mem
  obtain ⟨w,d,e⟩:=mem_image.mp ((modes_at ..).1 (hk _ u)); obtain ⟨k,a,b⟩:= Tower.wrap_nodes (K.c m) x w e; subst w
  let c:=winding α k
  refine ⟨c • creation K k j t,(SinglePocket K W S true).smul_mem c
    (pocket_creation K W S d ((mem_filter.mp (hk _ p)).2) ((Window.mem_Tset ..).1 (hk _ h))),?_⟩
  intro y; unfold creation basisC; simp only [Pi.smul_apply,map_smul]; rw [smul_smul, show c*winding α k=1 from fee_one _,one_smul]; unfold Lifted.index; rw [b]
lemma bilift {x:FC (Single (K.c m))}(u:x∈bipocket (K.c m) W (Q S) (Q T)) :
    ∃ f ∈ RawPair K W S T, ∀ i, f m i=x:= by
  let R:=LiftsTo K m (RawPair K W S T)
  change x∈ R
  refine Submodule.span_induction (p:=fun x _=> x∈ R) (fun i t=>?_) R.zero_mem (fun _ _ _ _ a b=> R.add_mem a b) (fun r _ _ u=> R.smul_mem r u) u
  obtain ⟨a,b,h,p,t,v,w,q,rfl⟩:=t
  obtain ⟨f,p,x⟩:= create_lift K W S m a h p t
  obtain ⟨g,w,y⟩:= remove_lift K W T m b v w q
  exact ⟨g*f,Submodule.subset_span (show _∈_ from ⟨_,w,_,p,rfl⟩),fun t=> congrArg₂ (· * ·) (y t) (x t)⟩

-- One hospitable host with the bi-letter price suffices to determine the form
-- of all Family terms. Note finite-volume torus _at this height_, then transfer
-- to the cover by the Borel envelope coordinates.
lemma descend {f:Buffered.Family K}(u:Tower.Tivoli D (K.c m))(d:S∪T⊆D)(h:InTest K true D false f)
    (p:∀ v, f m v∈ bipocket (K.c m) W (Q S) (Q T)): f∈ DressedPair K W S T D:= by
  classical
  let R:=bipocket (K.c m) W (Q S) (Q T)
  let B:= Module.finBasis ℂ R
  let I:=Fin (Module.finrank ℂ R)
  choose F H Q' using fun i:I=> bilift K W S T m (B i).property
  let W'(x:PairsC): Fields α := replant D α x
  let V(x:Fields α): ↥R := ⟨f m x,p x⟩
  let X(i:I)(x:PairsC):ℂ := B.coord i (V (W' x))
  have E:= h.support m
  -- Avoid a norm switch inside the basis field
  have hv : Envelope V := by
    refine ⟨?_,?_⟩
    · exact (E.env.meas).subtype_mk
    obtain ⟨D,h⟩:= E.env.cost; exact ⟨D,h⟩
  have ht(i:I): Coeff true D (X i):= by
    refine ⟨fun _=> by contradiction,Girt.pole_w (V ∘ W') (B.coord i)
      (B.coord i).continuous_of_finiteDimensional (Env.along (g:=W') hv (replant_b ..)),?_⟩
    intro x y a b
    apply congrArg (B.coord i); exact Subtype.ext (E.dep _ _ (based D _ u _ _ a) (based D _ u _ _ b))
  let A:=∑ i, scalar K (X i)* F i
  have ha:A ∈ DressedPair K W S T D:= Submodule.sum_mem _ fun i _=>Submodule.subset_span (show _∈_ from ⟨_,ht i,_,H i,rfl⟩)
  have he:A m=f m:=by
    funext y; let L:=V y
    have hp : V (W' (onC α y.1,onC α y.2))= L:= Subtype.ext (E.dep _ _ (graft_native D _ u _) (graft_native D _ u _))
    have hg(i:I):(scalar K (X i)*F i) m y=B.coord i L • (B i).val:= by
      rw [Pi.mul_apply,Pi.mul_apply, Q' i]; change (X i _ • (1:FC _))* _= _; unfold X; rw [hp,Algebra.smul_mul_assoc,one_mul]
    unfold A; simp_rw [Finset.sum_apply,hg]
    have hf:L=∑ i,B.coord i L • B i:= (B.sum_repr L).symm
    change _=L.val; conv_rhs=>rw [hf];
    rw [Submodule.coe_sum]; try rfl
  exact Tower.box_ext K D (dressed_test K W S T D d ha) h u.hosp he ▸ ha
end oneHost


section converse
private lemma tidy_key (n:Side)(y:Cover)(i:SpinIdx)(b:SU.Slot)(T:Finset (Single n))(t:Lifted.index n y i b ∈ T): withinM T (basisC n y i b):= by unfold withinM basisC; rw [map_smul,within_basis _ _ t]
private lemma node_in (N:Side)(y:Cover)(i:SpinIdx)(b:SU.Slot)(t:nodeC y∈T) : withinM (modesIn N (Satin.region T N)) (basisC N y i b):= by
  apply tidy_key; rw [modes_at]; change node (wrap N y)∈_
  rw [node_of]; exact mem_image_of_mem _ t

lemma rawMatrix {f:Buffered.Family K}(h:f ∈ RawPair K W S T)(n:Side)(v:Fields (K.c n)) :
    f n v ∈ bipocket (K.c n) W (Satin.region S (K.c n)) (Satin.region T (K.c n)):= by
  let A:=bipocket (K.c n) W (Satin.region S (K.c n)) (Satin.region T (K.c n))
  refine Submodule.span_induction (p:=fun f _=> f n v∈A) (fun f h=>?_) A.zero_mem (fun _ _ _ _ p t=>A.add_mem p t) (fun z _ _ t=>A.smul_mem z t) h
  obtain ⟨x,p,y,t,rfl⟩:= h
  change x n v * y n v ∈ A
  refine Submodule.span_induction (p:=fun f _=> f n v * y n v ∈A) (fun f h=>?_) ?_ ?_ ?_ p
  · obtain ⟨z,i,b,h,q,u⟩:=h
    rw [if_neg Bool.false_ne_true] at u
    obtain ⟨w,rfl⟩:= u
    let R:=K.c n
    let f:=basisC R z i b
    change Fock.remove f * y n v ∈ A
    refine Submodule.span_induction (p:=fun g _=> Fock.remove f * g n v∈ A) (fun g v=>?_) ?_ ?_ ?_ t
    · -- potential v shadow. let proof
      obtain ⟨k,j,c,a,r,s⟩:= v
      rw [if_pos rfl] at s
      obtain ⟨e,rfl⟩:=s
      exact generator W R _ _ (tidy_key R k j c _ ((Window.mem_Tset ..).2 e))
        (tidy_key R k j c _ (mem_filter.mpr ⟨mem_univ _,r⟩)) (node_in S _ _ _ _ a)
        (tidy_key R z i b _ (mem_compl.mpr fun h=> w ((Window.mem_Tset ..).1 h)))
        (tidy_key R z i b _ (mem_filter.mpr ⟨mem_univ _,q⟩)) (node_in T _ _ _ _ h)
    · simp only [Pi.zero_apply,mul_zero]; exact A.zero_mem
    · intro x y _ _ h t; simp only [Pi.add_apply,mul_add]; exact A.add_mem h t
    intro c a _ h; simp only [Pi.smul_apply,Algebra.mul_smul_comm]; exact A.smul_mem c h
  · simp only [Pi.zero_apply,zero_mul]; exact A.zero_mem
  · intro a b _ _ h t; simp only [Pi.add_apply,add_mul]; exact A.add_mem h t
  intro c a _ h; simp only [Pi.smul_apply,Algebra.smul_mul_assoc]; exact A.smul_mem c h
lemma dressedMatrix {f:Buffered.Family K}(h:f ∈ DressedPair K W S T D)(n:Side)(v:Fields (K.c n)) :
    f n v ∈ bipocket (K.c n) W (Satin.region S (K.c n)) (Satin.region T (K.c n)):= by
  let A:=bipocket (K.c n) W (Satin.region S (K.c n)) (Satin.region T (K.c n))
  refine Submodule.span_induction (p:=fun f _=> f n v∈A) (fun f h=>?_) A.zero_mem (fun _ _ _ _ p t=>A.add_mem p t) (fun z _ _ t=>A.smul_mem z t) h
  obtain ⟨g,_,x,p,rfl⟩:=h
  change (g _ • (1:FC (Single (K.c n)))) * _ ∈ A
  rw [Algebra.smul_mul_assoc,one_mul]; exact A.smul_mem _ (rawMatrix K W S T p n v)
end converse
end YM.CF.Buffered.Afterglow.Six

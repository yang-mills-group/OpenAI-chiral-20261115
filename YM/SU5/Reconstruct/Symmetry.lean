import YM.SU5.Reconstruct.Notify
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 620000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
open Tower.Selected Set MeshClock Tapestry.Exhibition
open SelectionAnalysis Vacancy.Average
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  {L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H i k I E L B T t)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Dₚ" => D.toExhibition
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
local notation "χ" => Dome (tent Y H)
local notation "O" => Altitude.Cloud (Dome (tent Y H))
local notation "P₀" s:max => vistaFinish Y H s (Dₚ)

variable (C : ∀ i: Axis, Tower.Arena Y H G.history.circuit i 0 false)
variable (c: (displayAlgebra Y H D.univ_ G.history G.clipped 0 false (C 0)) →⋆ₐ[ℂ] ℂ)

/-! # A common coordinate system over the Pol assembly. Symmetry.
No overlap claimed for coincidence queries; require assignable stencils in given
regions with pairwise disjoint supports. No topological motion changing
window until conditions paid. Lattice here at physical fine costs. All mesh frames
lead to same Sch responses on Panel. -/

variable {σ:Type} {W : σ → Set RSpace}
variable (z:σ → placement Λ)
local notation "Pq" U:max=> Pol Y H U
local notation "Pn" k:max U:max=> PolAt Y H k U
local notation "tF"=> sch Y H D G C c

section systematics
variable (W : σ→ Set RSpace)(Z:List σ)
noncomputable def parkAt (Y:Course Λ (VolumeCape.Dream.Nimbus l))(F:σ→ Set RSpace)(x:σ→placement Λ)(u:σ): Set RSpace:= carried (physPos Λ (x u)) (F u)
-- public definition should not depend on l Y? remove later
variable (u v:σ→placement Λ)
local notation "M" p:max=>physPos Λ p
lemma parking_plus (g:placement Λ)(t:σ): parkAt Y W (fun i=>g+u i) t= carried (physPos Λ g) (parkAt Y W u t):=by unfold parkAt; rw [map_add,carried_plus]
/-- Canonical position relations at any height fully paying. Nat mesh infinite; CF signal units. -/
def detachedAt (W:σ→ Set RSpace) (Z:List σ) := Z.Pairwise (fun x y=> Disjoint (parkAt Y W u x) (parkAt Y W u y))
local notation "M₀" p:max=> parkAt Y W u p
noncomputable def routePol (z: σ→placement Λ) (x:∀ i,Pq (W i)) (a:σ) : Pq (parkAt Y W z a):=(animates_exists Y H D G (W a) (z a) (x a)).choose
lemma routed (y:σ→placement Λ)(x:∀ i,Pq (W i))(a:σ): Animates Y H D (y a) (x a).val (routePol Y H D G W y x a).val:=(animates_exists Y H D G (W a) (y a) (x a)).choose_spec
-- combine under localized algebra element in union. Reindex via same List or Perm.
def catRegion (U:σ→Set RSpace)(p:List σ): Set RSpace := ⋃ i∈p,U i
local notation "catU" Ω:max=> catRegion Ω
lemma catHead (i:σ) : catRegion W (i::Z)= W i ∪ catRegion W Z := by classical simp only [catRegion,List.mem_cons]; ext x; simp
lemma cat_apart (i:σ)(p:(i::Z).Pairwise (fun a b=> Disjoint (W a) (W b))) : Disjoint (W i) (catRegion W Z) := by
  unfold catRegion; refine Set.disjoint_left.mpr (fun _ v q=>?_)
  obtain ⟨a,r⟩:= Set.mem_iUnion.mp q; obtain ⟨b,w⟩:= Set.mem_iUnion.mp r
  exact Set.disjoint_left.mp ((List.pairwise_cons.mp p).1 a b) v w
lemma aggregate_level {n:ℕ}{x : σ→O}(h:∀ i∈Z,x i∈ Pn n (W i)): (Z.map x).prod ∈ Pn n (catRegion W Z):=by
 induction Z with
 | nil=> exact Subalgebra.one_mem _
 | cons i a ih=>
   rw [catHead W] -- wrong
   apply Subalgebra.mul_mem
   · exact isotone Y H Set.subset_union_left (h i (List.mem_cons_self))
   exact isotone Y H Set.subset_union_right (ih (fun i p=> h i (List.mem_cons_of_mem _ p)))
lemma aggregate_pol (x : ∀ i, Pq (W i)) : (Z.map fun i=> (x i).val).prod ∈ Pq (catRegion W Z):=by
 classical
 obtain ⟨n,u⟩:= ((Finset.eventually_all Z.toFinset).mpr (fun i h=>eventually_inside Y H (x i).property)).exists
 exact pol_of_level Y H (aggregate_level Y H W Z (fun i p=>u i (by simpa using p)))
include G in
lemma cat_product {p : σ→ O} {n:ℕ}(t:Z.Pairwise (fun a b=>Disjoint (W a) (W b)))(h:∀ i∈ Z, p i∈PolAt Y H n (W i)): (vistaFinish Y H n D.toExhibition) ((Z.map p).prod)=(Z.map fun i=> (P₀ n) (p i)).prod :=by
 induction Z with
 | nil =>
   simp only [List.map_nil,List.prod_nil]
   -- crown one
   let a:=pinhole χ n 1; rw [show (1:O)=pinhole χ n 1 from (map_one _).symm]; exact Decking.outcrop .. -- names order?
 | cons i z ih=>
   have ht := (List.pairwise_cons.mp t); have he : ∀i ∈ z,_ := fun j v=>h j (List.mem_cons_of_mem _ v)
   simp only [List.map_cons,List.prod_cons]
   rw [depart_pair Y H D.univ_ G D.toExhibition ((well_spec ..).1 (h i (List.mem_cons_self))).1 ((well_spec ..).1 (aggregate_level Y H W z he)).1 (Disjoint.preimage _ (cat_apart W z i t)), ih ht.2 he]
include G in
lemma compatible_suite (x y: ∀ i,Pq (W i)) (t:Z.Pairwise (fun a b=>Disjoint (W a) (W b)))(h:∀ i∈Z, Concurrent Y H D (x i).val (y i).val) : Concurrent Y H D ((Z.map fun i=> (x i).val).prod) ((Z.map fun i=>(y i).val).prod):= by
 induction Z with
 | nil=> exact conc_self ..
 | cons a l ih =>
   have hx : Concurrent Y H D ((l.map fun i=>(x i).val).prod) ((l.map fun i=>(y i).val).prod):= ih (List.pairwise_cons.mp t).2 (fun i v=>h i (List.mem_cons_of_mem _ v))
   simp only [List.map_cons,List.prod_cons]
   exact conc_mul Y H D G (cat_apart W l a t) (x a) (y a) (⟨_,aggregate_pol Y H W l x⟩) ⟨_,aggregate_pol Y H W l y⟩ (h _ (List.mem_cons_self)) hx
end systematics
variable (W:σ→ Set RSpace)(x:∀ i, Pol Y H (W i))
-- Now evaluate all such words in a common character explicitly. `poseValue` takes
-- positions on the dyadic-like mesh (our L-adic mesh); later continuations use
-- absolute positions in ℝ⁴. It is irrelevant which representatives are chosen.
variable (u:σ→placement Λ)
local notation "Mv"=> parkAt Y W u
local notation "Zₚ" v:max=> routePol Y H D G W v x
-- value unspecified on collisions
def poseValue (z:List σ) (u:σ→placement Λ): ℂ := sch Y H D G C c ((z.map fun i=>(routePol Y H D G W u x i).val).prod)
lemma posed (L:List σ)(t:L.Pairwise (fun i k=> Disjoint (Mv i) (Mv k)))(X:∀i, Pq (Mv i))(p:∀ i∈L, Animates Y H D (u i) (x i).val (X i).val) :
    poseValue Y H D G C c W x L u = sch Y H D G C c ((L.map fun i=> (X i).val).prod):=
   conc_read Y H D G C c ⟨_,aggregate_pol Y H Mv L (Zₚ u)⟩ ⟨_,aggregate_pol Y H Mv L X⟩ (compatible_suite Y H D G Mv L (Zₚ u) X t (fun i h=> animates_does Y H D (routed Y H D G W u x i) (p i h)))
section fin -- use frame carriers all, for crop can include all σ independent positions
variable (Z:List σ)
lemma compose_here (t:Z.Pairwise (fun i k=> Disjoint (Mv i) (Mv k)))(n:ℕ)(p:σ → Cover)(e:∀ i,u i=meshPos Λ n (p i))(h:∀ i,(x i).val∈ PolAt Y H n (W i)) :
    poseValue Y H D G C c W x Z u = sch Y H D G C c ((Z.map fun i=> parcelTo Y H D n (p i) (x i).val).prod):=by
 let X i : Pq (Mv i) := ⟨parcelTo Y H D n (p i) (x i).val, pol_of_level Y H (by rw [parkAt,e i]; exact parcel_mem Y H D (p i) n (h i))⟩ -- Lean type infer underscore
 exact posed Y H D G C c W x u _ t X (fun i h'=> (show Animates _ _ _ _ _ _ from (e i).symm ▸ parcel_animates Y H D G (W i) (h i) (p i)))
lemma poses_read (j:Axis)(t:Z.Pairwise (fun i k=> Disjoint (Mv i) (Mv k)))(n:ℕ)(p:σ → Cover)(e:∀ i,u i=meshPos Λ n (p i))(h:∀ i,(x i).val∈ PolAt Y H n (W i)) :
    poseValue Y H D G C c W x Z u = response Y H D.univ_ n Q Qt j false (C j) (inAxis Y H D G C c j)
      ((Z.map fun i=> relocateWorld Y H false (p i) (fieldArg Y H (vistaFinish Y H n D.toExhibition (x i).val))).prod):=by
 let X i:= parcelTo Y H D n (p i) (x i).val
 have hU (i:σ) (_: i∈ Z) : X i∈Pn n (Mv i):=by rw [parkAt,e i]; exact parcel_mem Y H D (p i) n (h i)
 rw [compose_here Y H D G C c W x u Z t n p e h, sch_axes Y H D G C c j n (inside_budget Y H (aggregate_level Y H Mv Z hU)), cat_product Y H D G Mv Z t hU]
 exact congrArg _ (trail Z) -- implicit match
where
 trail (L:List σ) : fieldArg Y H ((L.map fun i=> vistaFinish Y H n D.toExhibition (parcelTo Y H D n (p i) (x i).val)).prod)=(L.map fun i=> relocateWorld Y H false (p i) (fieldArg Y H (vistaFinish Y H n D.toExhibition (x i).val))).prod:=by
   induction L with
   | nil=> rfl
   | cons i L ih=>
     simp only [List.map_cons,List.prod_cons]; rw [tallied]
     refine Eq.trans ?_ (congrArg₂ (·*·) (marchOut Y H (p i)) ih); rfl
lemma poses_order {Q':List σ}(h:Z.Perm Q') : poseValue Y H D G C c W x Z u=poseValue Y H D G C c W x Q' u:=by
 unfold poseValue; rw [List.Perm.prod_eq (h.map _)]
lemma steady_at (t:Z.Pairwise (fun i k=> Disjoint (Mv i) (Mv k)))[Fintype σ](g:placement Λ) : poseValue Y H D G C c W x Z (fun i=> u i+g)=poseValue Y H D G C c W x Z u:=by
 have e (a i): parkAt Y W (fun u'=>u u'+a) i=carried (physPos Λ a) (Mv i):=by simpa only [add_comm a] using parking_plus Y W u a i
 have ht: Z.Pairwise (fun i k=> Disjoint (parkAt Y W (fun i=>u i+g) i) (parkAt Y W (fun i=>u i+g) k)) := t.imp (by intro a b p; rw [e,e]; exact carried_disjoint _ p)
 obtain ⟨n,v⟩:= ((Filter.eventually_all.mpr (fun i=> (contHeight (u i)).and (eventually_inside Y H (x i).property))).and (contHeight g)).exists
 obtain ⟨a,s⟩:= v.2; let p i:= (v.1 i).1.choose; have h i: (meshPos Λ n) (p i)=u i:= (v.1 i).1.choose_spec
 let d i:= p i+a; have hX i:(meshPos Λ n) (d i)= u i+g:=by unfold d; rw [map_add,h,s]
 rw [poses_read Y H D G C c W x (fun i=>u i+g) Z 0 ht n d (fun i=> (hX i).symm) (fun i=>(v.1 i).2), poses_read Y H D G C c W x u Z 0 t n p (fun i=> (h i).symm) (fun i=> (v.1 i).2) ]
 let X(i:σ):Marks K false:= fieldArg Y H (vistaFinish Y H n D.toExhibition (x i).val)
 let F(Z:List σ):Marks K false:= (Z.map fun i=> relocateWorld Y H false (p i) (X i)).prod
 let T'(Z:List σ):Marks K false:= (Z.map fun i=> relocateWorld Y H false (d i) (X i)).prod
 have hy (Z:List σ): T' Z= relocateWorld Y H false a (F Z):=by
   have hb:=march Y H a
   suffices h:∀ (z:List σ), T' z= relocateWorld Y H false a (F z) from h Z
   intro z; induction z with
   | nil =>
     exact (show T' []=fieldArg Y H (march Y H a 1) by rw [map_one]; rfl).trans (marchOut Y H a (x:=1))
   | cons i z ih=>
     change relocateWorld Y H false (d i) (X i)*T' z=relocateWorld Y H false a (relocateWorld Y H false (p i) (X i)* F z)
     rw [ih,show d i = a+p i from add_comm ..,←world_held]; apply Subtype.ext
     rw [world_val]; exact (congrArg₂ (·*·) (world_val Y H false _ _) (world_val Y H false _ _)).trans ((cad_prod ..).symm)
 change response _ _ V _ Q Qt _ _ _ _ (T' Z) = response _ _ V _ Q Qt _ _ _ _ (F Z)
 rw [hy,world_still]
end fin
end YM.CF.Buffered.Afterglow.Tower.Reconstruction

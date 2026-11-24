/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.FiniteGaugeData.Hills.Foliage
import YM.SU5.FiniteGaugeData.SalonG.Booking
import YM.Ground.Spectrum
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey
namespace Hills
variable (a b:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:Repertory Y h W' R a)
variable {x:W (tent Y h)}
local notation "F"=> Camera Y h a W' R A
local notation "X" s:max=> route Y h s a W' R A
local notation "Ω"=> orbitSeed Y h a W' R A
include A
section economy
variable (C:ℝ)
omit A in
private lemma translation_lips (f:W (tent Y h))(p: Locator Kₜ f S)(a:Axis)(z:ℤ) :‖reading Kₜ (hour Kₜ S a z) (clockW Kₜ a z f) (loc_tic Kₜ S a z p)‖ ≤ duration S*‖reading Kₜ S f p‖:=by
 obtain ⟨i,t⟩:= (roomy_sides (hour Kₜ S a z) Kₜ).exists; apply offered_bound (hour Kₜ S a z) Kₜ _ (roomy_hosp _ t); intro v; rw [reading_p]; exact RealWidth.tick a (width_read p i) _ v
lemma view_compact {U:Type*}(x:U→ W (tent Y h))(p:∀ i,Locator Kₜ (x i) S)(v:∀ i, ‖reading Kₜ S (x i) (p i)‖≤ C) : IsCompact (closure (Set.range ((route Y h s a W' R A) ∘ x))) := by
 obtain ⟨d,z,d',u⟩:= rent_uniform Y h S a; let y(i:U):= clockW Kₜ a z (x i); let S':= hour Kₜ S a z; have b(i:U):Locator Kₜ (y i) S':= loc_tic Kₜ S a z (p i); have w(i:U): Plan Y h a d (y i):=⟨S',u,b i⟩
 let H:= (StructureH Y h a W' R A).Unity; let B(i:U):= Wedge Y h s a d W' R A (w i) d'; have hx: IsCompact (closure (Set.range B)):= lounge Y h S' s a d W' R A d' (duration S*C) y w b (fun i=> le_trans (translation_lips Y h S _ (p i) a z) (mul_le_mul_of_nonneg_left (v i) (duration_pos S).le))
 have he: Continuous (social H) := ((broadcast H).mkContinuous 1 (fun f=> (social_bound (U:=H) f).trans_eq (one_mul _).symm)).continuous
 let A':= social H '' closure (Set.range B); have hp:IsCompact A':= hx.image he; refine hp.of_isClosed_subset isClosed_closure (closure_minimal ?_ hp.isClosed); rintro g ⟨i,rfl⟩; refine ⟨B i,subset_closure ⟨_,rfl⟩,?_⟩
 exact (route_formula Y h s a d W' R A (w i) d').symm.trans (stayP ..)
-- cost.M & E.Op.W.S.Vertex.Varying f.P. no Width assumption but local support
lemma route_budget : ∃ B:ℝ, 0<B∧ ∀ (x:W (tent Y h)) (p:Locator Kₜ x S), ‖route Y h s a W' R A x‖ ≤ B*‖reading Kₜ S x p‖:= by
 obtain ⟨d,t,u,e⟩:=rent_uniform Y h S a; let T':= hour Kₜ S a t;
 let C:=duration S; let w:=duration T'; let d':=venus Y h T' s a d; let B:=C*w/d'; have hC:0<C:=duration_pos S; have hw:0<w:=duration_pos T'; have ht:0<d':=Real.exp_pos _; refine ⟨B,by unfold B; positivity,fun x p=>?_⟩
 let z:= clockW Kₜ a t x; let b:=loc_tic Kₜ S a t p; let p' : Plan Y h a d z:= ⟨T',e,b⟩; rw [←stayP Y h s a a W' R A x t]; exact le_trans (guestPrice Y h s a d W' R A p' u) ((wedge_lip Y h T' s a d W' R A p' u b).trans (le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (translation_lips Y h S _ p _ _) hw.le) ht.le) (le_of_eq (by unfold B C d' w; ring))))
lemma reading_sub (f g:W (tent Y h))(p:Locator Kₜ f S)(t:Locator Kₜ g S)(e:Locator Kₜ (f-g) S): reading Kₜ S f p-reading Kₜ S g t=reading Kₜ S (f-g) e:= compose_inj S Kₜ (by rw [map_sub (f:=composeQ Kₜ S),reading_p,reading_p,reading_p]; rfl)
lemma route_price : ∃ B:ℝ, 0<B ∧ ∀ (x y:W (tent Y h))(p:Locator Kₜ x S)(t:Locator Kₜ y S),dist (route Y h s a W' R A x) (route Y h s a W' R A y)≤ B*dist (reading Kₜ S x p) (reading Kₜ S y t):=by
 obtain ⟨B,e,b⟩:=route_budget Y h S s a W' R A; refine ⟨B,e,fun x y p t=>?_⟩; have he:Locator Kₜ (x-y) S:=by rw [sub_eq_add_neg,←neg_one_smul (R:=ℂ) y]; exact locate_sum Kₜ S p (locate_scale _ _ _ t)
 rw [dist_eq_norm,dist_eq_norm,←map_sub,reading_sub Y h S a W' R A _ _ p t he]; exact b _ he
end economy
abbrev Speakers : Set ((Camera Y h a W' R A).Op):= {x| ∃ (s:ℕ) (f:W Kₜ),route Y h s a W' R A f=x}
def Boulevard : StarSubalgebra ℂ ((Camera Y h a W' R A).Op):= (StarAlgebra.adjoin ℂ (Speakers Y h a W' R A)).topologicalClosure
local notation "T"=> Speakers Y h a W' R A
local notation "B₀"=> Boulevard Y h a W' R A
lemma speaks (f:W (tent Y h)): route Y h s a W' R A f∈ Boulevard Y h a W' R A:= subset_closure (StarAlgebra.subset_adjoin ℂ _ (show (X s) f∈Speakers Y h a W' R A from ⟨s,f,rfl⟩))
abbrev KeySet : Type := (Boulevard Y h a W' R A:Type)
local notation "Ξ"=> Boulevard Y h a W' R A
lemma speaker_stars {x:(Camera Y h a W' R A).Op}(p:x∈ Speakers Y h a W' R A): star x∈ Speakers Y h a W' R A:= by obtain ⟨s,v,rfl⟩:=p; exact ⟨s,_, route_mirror Y h s a W' R A v⟩
lemma commSphere : ∀ x y:Boulevard Y h a W' R A, x*y=y*x:= by
 let U:= StarAlgebra.adjoin ℂ (Speakers Y h a W' R A); let V:= U.topologicalClosure
 have he {x y:(F).Op}(p:x∈ T)(v:y∈ T): x*y=y*x:=by
    obtain ⟨i,u,rfl⟩:=p; obtain ⟨j,v,rfl⟩:=v; exact commute_pt Y h a W' R A j i u v
 letI : IsMulCommutative U := StarAlgebra.isMulCommutative_adjoin ℂ (fun _ hx _ hy=>he hx hy) (fun _ hx y hy=> he hx (speaker_stars Y h a W' R A hy))
 letI := U.commSemiringTopologicalClosure (fun x y=> IsMulCommutative.is_comm.comm x y)
 exact fun (x y:U.topologicalClosure)=> mul_comm x y
lemma faith : ∀ p:Boulevard Y h a W' R A,p.val Ω=0 →p=0:=by
 intro p w; apply Subtype.ext; apply effectiveV Y h a W' R A _ w; intro i f; exact congrArg Subtype.val (commSphere Y h a W' R A ⟨_, speaks Y h i a W' R A f⟩ p)

lemma separableSp : TopologicalSpace.IsSeparable (Speakers Y h a W' R A):=by
 classical
 let U(s:Finset Cover)(r:ℕ):= Lobby Y h s r
 let V(A0:Finset Cover)(s r:ℕ):= Set.range ((route Y h s a W' R A) ∘ (fun i:Lobby Y h A0 r=>i.val))
 have he(s:ℕ)(S: Finset Cover)(r:ℕ): IsCompact (closure (V S s r)):= view_compact Y h S s a W' R A (C:=(r:ℕ)) (fun (i:U S r)=>i.val) (fun i=>Classical.choose i.property) (fun i=>Classical.choose_spec i.property) -- C expected ℝ
 apply (TopologicalSpace.IsSeparable.iUnion (fun S:Finset Cover=>TopologicalSpace.IsSeparable.iUnion (fun s:ℕ=>TopologicalSpace.IsSeparable.iUnion (fun r:ℕ=> ((he s S r).isSeparable).mono (subset_closure (s:=V S s r)))))).mono
 rintro v ⟨s,x,rfl⟩; obtain ⟨S,z⟩:= testimony Kₜ x; obtain ⟨r,h⟩:= exists_nat_ge ‖reading Kₜ S x z‖; exact Set.mem_iUnion.mpr ⟨S,Set.mem_iUnion.mpr ⟨s,Set.mem_iUnion.mpr ⟨r, ⟨⟨x,z,h⟩,rfl⟩⟩⟩⟩
section
-- include Work. B12 monoid
open Set
omit A
open scoped Pointwise
private lemma monoid_sep {X' : Type*} [Monoid X'] [TopologicalSpace X'] [ContinuousMul X']
    {s : Set X'} (h : TopologicalSpace.IsSeparable s) :
    TopologicalSpace.IsSeparable (Submonoid.closure s : Set X') := by
  have hp (n : ℕ) : TopologicalSpace.IsSeparable (s ^ n) := by
    induction n with
    | zero =>
      rw [pow_zero]; exact (countable_singleton (1 : X')).isSeparable
    | succ n ih =>
      rw [pow_succ, ← image_mul_prod]; exact (ih.prod h).image continuous_mul
  refine (TopologicalSpace.IsSeparable.iUnion hp).mono ?_
  intro x hx
  change x ∈ Submonoid.closure s at hx
  induction hx using Submonoid.closure_induction with
  | mem x hx => exact mem_iUnion.mpr ⟨1, by simpa using hx⟩
  | one => exact mem_iUnion.mpr ⟨0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨m, hm⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨n+m, by rw [pow_add]; exact mul_mem_mul hn hm⟩

end
open scoped Pointwise
lemma onBroadSep : ∃ u:ℕ→Boulevard Y h a W' R A,DenseRange u:= by
 have hT := separableSp Y h a W' R A
 have hV : TopologicalSpace.IsSeparable ((StarAlgebra.adjoin ℂ (Speakers Y h a W' R A)) : Set (F).Op):=by
    change TopologicalSpace.IsSeparable ((StarAlgebra.adjoin ℂ (T)).toSubalgebra.toSubmodule : Set (F).Op)
    rw [StarAlgebra.adjoin_eq_span,← Set.image_star]; exact (monoid_sep (hT.union (hT.image continuous_star))).span -- name image_star
 have he:TopologicalSpace.IsSeparable (Boulevard Y h a W' R A : Set (F).Op):= hV.closure
 haveI : TopologicalSpace.SeparableSpace ↥(Boulevard Y h a W' R A) := he.separableSpace
 exact ⟨TopologicalSpace.denseSeq _,TopologicalSpace.denseRange_denseSeq _⟩
#print axioms onBroadSep
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy

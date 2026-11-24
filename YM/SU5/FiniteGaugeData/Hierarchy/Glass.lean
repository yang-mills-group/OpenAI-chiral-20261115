import YM.SU5.FiniteGaugeData.Hierarchy.Vest
/-! # Reflection (any aligned axis and acting before/after advancement) -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra

open Girt Nacre Mir Phase RP
section ref
-- axis-generalization of InTest.reflection from Buffered.Eligible
variable {K : Calibration} {wide : Bool} {S : Finset Cover} {f g : Family K} {b : Bool}
variable (i₁ : Axis)(s : ℤ)
def reflector (i : Axis) (s : ℤ) (f : Family K) : Family K := fun m=> reflMark i s (f m)
abbrev refract (S:Finset Cover) := S.image ((plane i₁ s).motion)
local notation "Y" => @reflector K i₁ s
lemma ice_plus : Y (f+g)=Y f+Y g := funext fun _=> funext fun _=> theta_add ..
lemma ice_scale (a : ℂ) : Y (a • f)=star a • Y f := funext fun _=> funext fun _=> theta_smul ..
lemma ice_times : Y (f*g)=Y f*Y g := funext fun _=> funext fun _=> theta_mul ..
lemma ice_identity : Y 1=1 := funext fun _=> funext fun _=> theta_one _
private lemma opposite_spin : twist (pinLift i₁) (cutM plusHalf) = cutM plusHalfᶜ := by
 rw [dim_cut, raising,Fir.Adef.symm]; exact angleX (mirrorX i₁) true
private lemma reflected_scalar (f : PairsC→ℂ) (p : Coeff wide S f) : InTest K wide (S.image ((plane i₁ s).motion)) false (Y (scalar K f)) := by
 let F := moveC i₁ s; let g(x:PairsC):=star (f (F x.1,F x.2))
 have ht: Y (scalar K f)=scalar K g:= by funext m x; unfold scalar reflector reflMark; rw [theta_smul,theta_one]; apply congrArg (fun u :ℂ=> u • 1); unfold g; simp only [reflFields,Prod.map_fst, Prod.map_snd,reflect_onC]; rfl
 rw [ht]; refine .seed ⟨fun v=> ?_, Girt.pole_w _ star continuous_star (Env.along (g:=Prod.map F F) p.env ((move_cont ..).prodMap (move_cont ..)).measurable),fun x y a b=>?_⟩
 · obtain ⟨c,h,e⟩:= p.narrow v; refine ⟨fun x=>star (c (F x)),(h.comp (move_cont ..)).star,?_⟩; rw [show g=fun x=>star (f (F x.1,F x.2)) from rfl,e]; rfl
 exact congrArg star (p.locus (F x.1,F x.2) (F y.1,F y.2) (moved_agree _ _ a) (moved_agree _ _ b))
private lemma reflected_creation_eq (x : Cover) (i : SpinIdx) (b : SU.Slot) :
    Y (creation K x i b) = -Complex.I • ∑ j, star (Mir.pin i₁ j i) • removal K ((plane i₁ s).flee x) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold reflector reflMark creation removal
 rw [(flips_basisC i₁ s (K.c m) x i b).1]; unfold Fock.remove; simp only [map_sum,map_smul,star_sum,star_smul]
private lemma reflected_removal_eq (x : Cover) (i : SpinIdx) (b : SU.Slot) :
    Y (removal K x i b) = Complex.I • ∑ j, Mir.pin i₁ j i • creation K ((plane i₁ s).flee x) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold reflector reflMark creation removal
 rw [(flips_basisC i₁ s (K.c m) x i b).2]; simp only [map_sum,map_smul]
lemma reflects (p : InTest K wide S b f) : InTest K wide (S.image ((plane i₁ s).motion)) b (Y f) := by
 induction p with
 | @creator x i b t v=>
   rw [reflected_creation_eq]; refine .smul _ (InTest.sum _ _ (fun j _=> ?_)); by_cases w:j∉ plusHalf
   · refine .smul _ (.remover b w (mem_image.mpr ⟨_,v,Shape.mote ..⟩))
   rw [show pin i₁ j i=0 from Fine.entry (opposite_spin i₁) t (by simpa using not_not.mp w),star_zero,zero_smul]; exact .zero
 | @remover x i b t v=>
   rw [reflected_removal_eq]; refine .smul _ (InTest.sum _ _ (fun j _=> ?_)); by_cases w:j∈ plusHalf
   · refine .smul _ (.creator b w (mem_image.mpr ⟨_,v,Shape.mote ..⟩))
   have ht: twist (pinLift i₁) (cutM plusHalfᶜ)=cutM plusHalf:= by rw [dim_cut,map_sub,map_one,opposite_spin,dim_cut]; abel
   rw [show pin i₁ j i=0 from Fine.entry ht (by simpa only [mem_compl] using t) w, zero_smul]; exact .zero
 | seed p=> exact reflected_scalar i₁ s _ p
 | zero=> rw [show Y 0=0 from funext fun _=>funext fun _=> theta_zero _]; exact .zero
 | one=> rw [ice_identity]; exact .one
 | add _ _ a b=> rw [ice_plus]; exact .add a b
 | mul _ _ a b=> rw [ice_times]; exact .mul a b
 | smul a _ ih=> rw [ice_scale]; exact .smul _ ih
lemma ice_twice (p:InTest K wide S b f) : reflector i₁ s (reflector i₁ s f)=f:= funext fun m=> AtSupport.refl_refl i₁ s (p.support m)
lemma cold_twice (S: Finset Cover) : refract i₁ s (refract i₁ s S)=S:=by
  rw [refract,refract,image_image]; suffices h:(plane i₁ s).motion ∘ (plane i₁ s).motion=id by rw [h,image_id]
  funext x i; dsimp only [Function.comp_apply]; simp_rw [fling_move]; split_ifs <;> simp
variable (K) (S:Finset Cover) -- duplicate S explicit
def mirrorC : Catalog S →ₗ⋆[ℂ] Catalog (refract i₁ s S) where
  toFun f:= certifyAs (refract i₁ s S) K (reflector i₁ s (composeQ K S f)) (reflects i₁ s (compose_t S K f))
  map_add' f g:= by apply compose_inj (refract i₁ s S) K; rw [certified,map_add,map_add,certified,certified, ice_plus]
  map_smul' c f:= by apply compose_inj (refract i₁ s S) K; rw [certified,map_smul,map_smul,certified,ice_scale]; rfl
lemma mirrorC_id (x:Catalog S) : composeQ K (refract i₁ s S) (mirrorC K i₁ s S x)=reflector i₁ s (composeQ K S x):= certified _ _ _ (reflects i₁ s (compose_t S K x))
lemma mirror_cost (x:Catalog S):‖mirrorC K i₁ s S x‖ ≤ duration S*‖x‖:=by
  obtain ⟨m,h⟩:= (roomy_sides (refract i₁ s S) K).exists; refine offered_bound _ K _ (roomy_hosp _ h) (fun v=> ?_); rw [mirrorC_id,reflector,reflMark,theta_fee]; exact compose_price ..
def mirrorL := (mirrorC K i₁ s S).mkContinuous (duration S) (mirror_cost K i₁ s S)
lemma mirrorL_budget : ‖mirrorL K i₁ s S‖ ≤ duration S:=LinearMap.mkContinuous_norm_le _ (duration_pos S).le _
end ref
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
local notation "W₀" => GridStep Λ l S
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable {P:Call Λ l}{J:Wicket Λ l}
variable (K:Universal Y h u v I E)(R:Rolled Y h u v J P)
local notation "W"=> GridStep Λ l
section
variable (a:Axis)(z:ℤ)
local notation "M"=> refract a z
local notation "Z"=> (Λ.R.L.val * z : ℤ)
local notation "W'"=> refract a Z
-- sets equality useful if step lifted box uses this same padding instead of renting at a superset.
lemma grid_mirror : GridStep Λ l (refract a z S)= refract a (Λ.R.L.val*z) (GridStep Λ l S):=by
  let F(f:Cover):= Signed.act (R:=ℤ) (Signed.mirror a) f
  let x(x:Cover):= (plane a z).motion x; let y(x:Cover):= (plane a Z).motion x; let B:= Lattice.box (Λ.R.L.val*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J)
  have he (t:Cover)(u:Cover): y (u+Λ.R.L.val • t)=F u + Λ.R.L.val • x t := by
    ext i; have ht(u:Cover):F u i = if a=i then -u i else u i:=by by_cases h:a=i <;> simp [F,Signed.act, Signed.mirror,h]
    unfold y x; rw [fling_move,Pi.add_apply]; simp_rw [Pi.add_apply, Pi.smul_apply,nsmul_eq_mul,fling_move,ht]; split_ifs <;> ring
  classical
  have hx:(Lattice.box (Λ.R.L.val*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J)).image F=B:= box_covariant ..
  ext t; constructor
  · intro b; obtain ⟨x',u₁,v⟩:= mem_biUnion.mp b; obtain ⟨k,v₁,rfl⟩:= mem_image.mp u₁; obtain ⟨c,c',rfl⟩:= mem_image.mp v₁; obtain ⟨y,u₂,rfl⟩:= mem_image.mp v; change y∈ B at u₂; rw [← hx] at u₂; obtain ⟨d,d',rfl⟩:= mem_image.mp u₂; exact mem_image.mpr ⟨_,mem_biUnion.mpr ⟨_,mem_image_of_mem _ c',mem_image_of_mem (fun k=> k+Λ.R.L.val • c) d'⟩,he c d⟩
  intro t; obtain ⟨u,m,rfl⟩:= mem_image.mp t; obtain ⟨x',p,b⟩:= mem_biUnion.mp m; obtain ⟨k,pk,rfl⟩:=mem_image.mp p; obtain ⟨g,f,rfl⟩:=mem_image.mp b; have ht:F g∈B:= hx ▸ mem_image_of_mem F f
  exact mem_biUnion.mpr ⟨_,mem_image_of_mem _ (mem_image_of_mem x pk),mem_image.mpr ⟨_,ht,(he k g).symm⟩⟩
-- in the indicated ontology the *integer representative* `L^s * z` matters.
lemma sold_reflect (x:Family Kₜ): sold Y h s i (reflector a z x)=reflMark a z (sold Y h s i x):=by
  simp_rw [sold_v]; exact castR _ (terrain Y h (Y.ir i) s)
where castR {n m:Side}(x:Mark n) (p:n=m) : (show Mark m from p ▸ reflMark a z x)=reflMark a z (p ▸ x) := by subst m; rfl
lemma ingress_turn {D:Support (More (side Y i s))}{b:Bool}{f:Mark (side Y i s)}(h:AtSupport b D f)(p:(Y.voyage i).kick≤k)(u:s<Y.uv k) :
    ingress Y s i k (reflMark a z f) = reflMark a Z (ingress Y s i k f):=by
  let v:=(fullness Y i k p).cap_grant; let g:=(crease Y s i k p u)
  exact rising (apt (Y.ir i) Λ.block L₁ s) _ _ _ _ Λ.R.odd_side Chi.canonical _ _ _ a z (v.aligned s u) h (v.branch s u) ((Y.voyage i).ownership s).paid (Journey.legal Λ) g.1 g.2
lemma snag_turn (p:Offered Y S s i k)(t:Offered Y (refract a z S) s i k)(x:Catalog S):
    snag Y h (refract a z S) s i k (mirrorL Kₜ a z S x) =
      incl Kₜ (show refract a Z W₀ ⊆ GridStep Λ l (refract a z S) from (grid_mirror S a z).symm.le) (mirrorL Kₜ a Z W₀ (snag Y h S s i k x)):=by
  apply sold_catalog_inj Y h _ (s+1) i (roomy_hosp _ t.bill.upper)
  dsimp only; rw [incl_id,snag_pay Y h S s i k p,snag_pay Y h _ s i k t, transitionQ_apply,transitionQ_apply,show (mirrorL Kₜ _ _ S) _=mirrorC Kₜ _ _ S _ from rfl,show (mirrorL Kₜ _ _ W₀) _=mirrorC Kₜ _ _ W₀ _ from rfl,mirrorC_id,sold_reflect,exchanged,exchanged,mirrorC_id,sold_reflect]; exact ingress_turn Y s i k a z (sold_affair Y h S s i (compose_t ..)) p.calendar p.age
include K R
lemma turn_P (x:Catalog S):
    composeQ Kₜ ((W) ((M) S)) (P (refract a z S) s (mirrorL Kₜ a z S x)) = reflector a Z (composeQ Kₜ W₀ (P S s x)) := by
  obtain ⟨k,hp⟩:= eligible_exists Y u _ K.pick.grow_k
  let F:= incl Kₜ (show (W') W₀ ⊆(W) ((M) S) from (grid_mirror S a z).symm.le)
  have he := fun (S:Finset Cover) x=> audition _ _ (calls Y h S s R k hp) (tendsto_const_nhds (x:=x))
  have hv:P ((M) S) s (mirrorL Kₜ a z S x)=F (mirrorL Kₜ a Z W₀ (P S s x)):= tendsto_nhds_unique_of_eventuallyEq (he ((M) S) _) ((F.continuous.tendsto _).comp (((mirrorL Kₜ a Z W₀).continuous.tendsto _).comp (he S x))) (((eligible_offer Y h S s K k hp).and (eligible_offer Y h ((M) S) s K k hp)).mono fun i u=>snag_turn Y h S s _ _ a z u.1 u.2 x)
  rw [hv]; unfold F; rw [incl_id]; exact mirrorC_id ..
end
#print axioms turn_P
end YM.CF.Buffered.Afterglow.Hierarchy

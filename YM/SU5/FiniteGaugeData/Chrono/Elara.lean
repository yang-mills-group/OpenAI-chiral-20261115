import YM.SU5.FiniteGaugeData.Chrono.Simoom
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
variable {v u:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
namespace Chrono
open Nacre Heat Charm Playlist Show
variable (R:Universal Y h u v I E)(L:Rolled Y h u v J P)(a j:Axis)
local notation "η"=> reserve Λ l
-- Use Ahead half with margin for the GNS presentation. Distance in s persists and even INCREASES.
lemma Ahead.subh {y z:ℤ} (e:y≤z)(p:Ahead a z (reserve Λ l) S):Ahead a y (reserve Λ l) S:=fun x v=> (by specialize p x v; omega)
private lemma margin_adds {D w J:ℕ} {L:Side}{e:ℕ} (g:Margin L D w J e)(h:3≤ L.val): e+1+L.val*gross D w J ≤ L.val*e:=by
 have he: beforePad D≤r₁ L D:= by unfold r₁ beforePad; nlinarith
 unfold Margin r₃ at g; unfold gross; nlinarith -- layout
lemma grows_grid {x:ℤ}(p:0≤x)(e:Ahead a x (reserve Λ l) S): Ahead a (x+1) (reserve Λ l) (GridStep Λ l S) := by
  intro y v; obtain ⟨u,t,r⟩:= mem_biUnion.mp v; obtain ⟨k',s,rfl⟩:= mem_image.mp t; obtain ⟨u,h,rfl⟩:= mem_image.mp r
  specialize e k' s; let ℓ:= Λ.R.L.val; let d:= gross (aliasLaw Λ) (distanceLaw l) Λ.R.J
  have he : -((ℓ*d:ℕ):ℤ) ≤ u a:= (box_test.mp h).1 a; have hv:((reserve Λ l):ℤ)+1+↑(ℓ*d)≤ (ℓ:ℤ)*(reserve Λ l:ℤ):= by exact_mod_cast (margin_adds (Journey.prepared Λ l) Λ.R.coarse)
  have hL:3≤ ℓ:= Λ.R.coarse; rw [Pi.add_apply,Pi.smul_apply,nsmul_eq_mul]; change x+1+_ ≤ _+(ℓ:ℤ)*_; exact le_trans (by nlinarith : x+1+(reserve Λ l:ℤ) ≤ (ℓ:ℤ)*x+1+ (reserve Λ l:ℤ)) (by nlinarith)

variable (f:W (tent Y h))
abbrev Canaan (f:W (tent Y h))(b:ℤ) := ∃ S:Finset Cover,Ahead a b (reserve Λ l) S∧ Locator Kₜ f S
lemma Canaan.subh {b c:ℤ}(p:c≤b)(v:Canaan Y h a f b): Canaan Y h a f c:=by obtain ⟨s,t,v⟩:= v; exact ⟨s,Ahead.subh s a p t,v⟩ -- args supply
include R L in
lemma Canaan.next {b:ℤ}(p:0≤b)(v:Canaan Y h a f b):Canaan Y h a (Charm.next Y h s R L f) (b+1):=by obtain ⟨S,t,v⟩:= v; exact ⟨_, grows_grid S a p t,locate_next _ _ _ _ R L _ v⟩
lemma Canaan.flight {b:ℤ}(z:ℤ)(p:Canaan Y h a f b): Canaan Y h a (clockW Kₜ a z f) (b+(tic Kₜ:ℤ)*z):=by obtain ⟨S,t,v⟩:= p; exact ⟨hour Kₜ S a z,flightW Kₜ S a b z t,loc_tic Kₜ S a z v⟩
lemma Canaan.over {b:ℤ}(z:ℤ)(p:Canaan Y h a f b)(t:j≠a): Canaan Y h a (clockW Kₜ j z f) b:=by obtain ⟨S,u,v⟩:= p; exact ⟨_, platformL Kₜ S a j b z t u,loc_tic Kₜ S j z v⟩

def Portico : Subalgebra ℂ (W (tent Y h)) where
 carrier:={x | Canaan Y h a x 0}
 algebraMap_mem' t:=⟨∅,by simp [Ahead],by rw [Algebra.algebraMap_eq_smul_one]; exact locate_scale _ ∅ t (locate_one ..)⟩
 mul_mem' := by rintro x y ⟨U,o,t⟩ ⟨V,p,b⟩; exact ⟨U∪V,ahead_union U V a 0 o p,locate_join _ _ (locate_sub _ t subset_union_left) (locate_sub _ b subset_union_right)⟩
 add_mem' := by rintro x y ⟨U,o,t⟩ ⟨V,p,b⟩; exact ⟨U∪V,ahead_union U V a 0 o p,locate_sum _ _ (locate_sub _ t subset_union_left) (locate_sub _ b subset_union_right)⟩

abbrev Decko := (Portico Y h a:Type)
local notation "V'" => Vect Y h a 0
variable (x y:Decko Y h a)
lemma Decko.atlas : Canaan Y h a x.val 0:= x.property
lemma frame_b : frameQ Λ 0 s=0:=by unfold frameQ planeAt gaugeShift; simp
-- pulse insert reference
lemma seats : credit_at Y h s x.val∈ Half Y h a 0:=by
 obtain ⟨S,p,u⟩:= x.property; apply flow_active Kₜ; intro d; by_cases f:d=s
 · subst d; exact ⟨_,by rw [frame_b]; exact p, by rw [located_here]; exact u⟩
 exact ⟨∅, fun _ t=> False.elim (notMem_empty _ t),by rw [located_there _ _ _ _ _ f]; exact locate_one ..⟩
def seedling : Vect Y h a 0:= ⟨credit_at Y h s x.val,seats ..⟩
lemma seedling_one : seedling Y h s a 1=1:=by
 apply Subtype.ext; change credit_at Y h s _=1; unfold credit_at; rw [show (1:Decko Y h a).val=1 from rfl, located_one]; rfl
include R L
lemma daily (v:V'): Show.collapse Y h s R L v.val∈ Portico Y h a:=by
 unfold Show.collapse; rw [fills]; exact port_union Y h a _ _ _ fun j h'=> by
    have he:=located Y h s R L j a 0 ((active_iff (tent Y h) _ v.val).mp v.property j h'); rw [frame_b] at he; exact he
def days : Vect Y h a 0 →ₗ[ℂ] Decko Y h a where
 toFun v:= ⟨Show.collapse Y h s R L v.val, daily Y h s R L a v⟩
 map_add' _ _:= Subtype.ext (map_add ..)
 map_smul' _ _:= Subtype.ext (map_smul ..)
lemma fullDay : (days Y h s R L a) (seedling Y h s a x)=x:=by apply Subtype.ext; change Show.collapse Y h s R L (credit_at ..)= _; unfold credit_at Show.collapse flow; rw [fill_mode,one_smul,pulse_full]
lemma beams_days (x y:V')(t:Arrive Y h x.val s)(g:Arrive Y h y.val s):
    beams Y h R L a 0 x y= E s (helve Kₜ a (days Y h s R L a x).val (days Y h s R L a y).val).val:=by
  have hz:= foyer Y h s R L a 0 _ _ x.property y.property t g; dsimp only at hz; rw [frame_b] at hz; exact hz
private def marbleD : W (tent Y h) →ₗ[ℂ] W (tent Y h) where
 toFun := Charm.next Y h s R L
 map_add' := fun _ _=> next_sum ..
 map_smul' := fun _ _=> next_smul ..
def nectar : Decko Y h a →ₗ[ℂ] Decko Y h a where
 toFun v:= ⟨marbleD Y h s R L v.val,Canaan.subh Y h a _ zero_le_one (Canaan.next Y h s R L a v.val le_rfl v.property)⟩
 map_add' := fun _ _=> Subtype.ext (map_add ..)
 map_smul' := fun _ _=> Subtype.ext (map_smul ..)
lemma nectar_next (w:V')(t:Arrive Y h w.val s): (days Y h (s+1) R L a) w=nectar Y h s R L a ((days Y h s R L a) w):=by
 apply Subtype.ext; change Show.collapse Y h (s+1) R L w.val= marbleD Y h s R L (Show.collapse Y h s R L w.val); unfold Show.collapse; rw [fills,fills,map_sum]; refine sum_congr rfl fun i h'=>?_ ; rw [preRoll,(t i h') (s+1) (by omega), mul_one,map_smul]; rfl
-- clocks & reflection algebra commute promotion, gauge invariance included in Portico definition
lemma promote_clock (z:ℤ)(x:W (tent Y h)) :
  Charm.next Y h s R L (clockW Kₜ a z x) = clockW Kₜ a (Λ.R.L.val*z) (Charm.next Y h s R L x):=by
  unfold clockW; change Charm.next .. = fire Kₜ _ (Heat.gaugeShift Λ.block _) _; rw [next_mir,next_mir,mul_zero,show (Λ.R.L.val:ℤ)*Heat.gaugeShift (Kₜ).B z= Heat.gaugeShift Λ.block (Λ.R.L.val*z) from ?_]; change _* Heat.gaugeShift Λ.block z= _; unfold Heat.gaugeShift; ring -- gZ private transparency
#print axioms nectar_next
end Chrono
end YM.CF.Buffered.Afterglow.Hierarchy

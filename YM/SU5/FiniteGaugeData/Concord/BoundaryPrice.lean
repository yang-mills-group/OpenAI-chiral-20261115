import YM.SU5.FiniteGaugeData.Concord.Confluence
/-! # Positive reflection across levels, fenced supports

`far` is in the observed torus, can be issued e.g. when the two footprints are
opposite. Cartesian plane orientation a, gauge plane coordinate z (uses `Heat.gaugeShift` true
supported planes for `RP` itself). The support condition is on native anchored gauge sites including
margin `reserve` chosen in election. These facts pay positivity when the local algebra across
resolutions does not artificially set *equal* the overlapping readings at other resolutions.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock Heat
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable (s:ℕ) {i k:ℕ→ℕ}{S T:Finset Cover}
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Playhouse Λ l}
local notation "K"=> tent Y H
local notation "U"=> swept Λ l
local notation "Ω"=> ConeFilter Y i k
local notation "L"=> Λ.R.L
local notation "ℓ"=> reserve Λ l
variable (W:Traced Y H i k F E P) (a:Axis)(z:ℤ)
local notation "z'" => ((Λ.R.L.val:ℤ)*z)
local notation "ν" s:max n:max => side Y n s

lemma observe_turn (n:ℕ)(f:junior K) : observe Y H n s (turn (tent Y H) a z f).val=reflMark a z (observe Y H n s f.val):= by rw [turn_coe]; simp_rw [observe_formula]; exact InHouse.Copies.turn ..

section sharp
variable {n j:ℕ}(h:PairIdx Y s n j)
include h

local notation "Yc"=> Λ.Ctor (Y.ir n) s
local notation "A"=> steps Λ.V (Y.ir n) Λ.block (Y.uv j) s
local notation "G"=> apt (Y.ir n) Λ.block L s
local notation "X"=> ((Y.voyage n).X (Y.uv j))

lemma trip_facing (f:Mark (side Y n s))(t:AtSupport false univ f) : haul Y s n j (reflMark a z f)= reflMark a (Λ.R.L.val*z) (haul Y s n j f):=by
  let t':=(fullness Y n j h.1).cap_grant
  exact rising G A Λ.K.j ((X).wave s).val ((X).gram (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d ((X).gram (s+1)).beta ((Y.voyage n).CapeT s) a z (t'.aligned s h.2) t (t'.branch s h.2) ((Y.voyage n).ownership s).paid (Journey.legal Λ) (can_cane Y s h).1 (can_cane Y s h).2

lemma across_fence {S T:Finset (Site (More (side Y n s)))} (f g:Mark (side Y n s)) (p:AtSupport false S f)(t:AtSupport false T g)(q:∀ x∈S,∀ y∈T,2*(nearZero (aliasLaw Λ)+distanceLaw l)<separation x y) :
    haul Y s n j (f*g)= haul Y s n j f * haul Y s n j g:=by
  let t':=(fullness Y n j h.1).cap_grant
  exact separated_mult G A Λ.K.j ((X).wave s).val ((X).gram (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d ((X).gram (s+1)).beta ((Y.voyage n).CapeT s) (Journey.legal Λ) ((Y.voyage n).ownership s).paid.bill (t'.branch s h.2) (can_cane Y s h).1 (can_cane Y s h).2 f g p t (tissue Y n s) q
end sharp
local notation "f'"=> courseAdvance Y H s W

include W

lemma at_fires (f:junior K) :
    courseAdvance Y H s W (turn K a z f)= turn K a ((Λ.R.L.val:ℤ)*z) ((f') f):=by
  obtain ⟨S,t⟩:=supported K f; let F':= fixedPlay Y H s i f; have h:InHouse W S F' f:= InHouse.const t
  apply Sited.back_together (p:=⟨_,(h.blink a z).next⟩); refine Sited.fortuity (p:=⟨_, h.next.blink a z'⟩) ?_
  filter_upwards [timely_visit W.own.pick s, InHouse.paid h] with j t p; exact (trip_facing Y s a z t _ (p.mono (Finset.subset_univ _))).symm

-- asks the actual lower admissibility on the cone

def NoOverlap (Y:Course Λ (VolumeCape.Dream.Nimbus l))(s:ℕ)(i k:ℕ→ℕ)(S T:Finset Cover):Prop:= ∀ᶠ p:ℕ×ℕ in ConeFilter Y i k,
    ∀ x∈region S (side Y (i p.1) s),∀ y∈region T (side Y (i p.1) s),2*(nearZero (aliasLaw Λ)+distanceLaw l)<separation x y

lemma prefactor {x y:junior K} (p:x∈club K S)(t:y∈club K T)(h:NoOverlap Y s i k S T):
    courseAdvance Y H s W (x*y)= ((f') x)*((f') y):=by
  let B:= InHouse.const (W:=W) (s:=s) p; let V:=InHouse.const (W:=W) (s:=s) t
  let G:= (Sited.mul (p:=⟨_,B⟩) ⟨_,V⟩).advancing
  apply G.back_together; refine (Sited.mul (p:=⟨_,B.next⟩) ⟨_,V.next⟩).fortuity ?_
  filter_upwards [timely_visit W.own.pick s, h, B.paid,V.paid] with j p t v z; exact (across_fence Y s p _ _ v z t).symm -- h not sense

lemma ticket_separated (p:starboard a z (reserve Λ l) S) (t:starboard a z (reserve Λ l) T):
    NoOverlap Y s i k (shadow a z S) T:=by
  have he(T)(p:starboard a z ℓ T) : ∀ᶠ p:ℕ×ℕ in ConeFilter Y i k,region T (side Y (i p.1) s)⊆ band (side Y (i p.1) s) a z (reserve Λ l) := by
    refine (((momentum Y s).comp W.own.pick.grow_i.tendsto_atTop|>.comp ConeFilter.late_left).eventually (hosted (tent Y H) a z ℓ p)).mono ?_
    intro j p; exact Eq.mp (congrArg (fun (n:Side)=> region T n⊆ band n a z (reserve Λ l)) (terrain Y H (Y.ir _) s)) p
  refine ((he S p).and (he T t)).mono ?_
  intro j p x a' y t; obtain ⟨v,v',rfl⟩:= mem_image.mp a'; obtain ⟨v,tZ,rfl⟩:= mem_image.mp v'
  apply margin_separate a z (Journey.prepared Λ l) _ _ _ (p.2 t); rw [←Shape.anno]; exact mem_image_of_mem _ (p.1 (mem_image_of_mem _ tZ))

lemma wing_fence {x y:junior K} (p:x∈ wing K a z ℓ)(t:y∈wing K a z ℓ):
    courseAdvance Y H s W (turn K a z x*y)=turn K a z' (courseAdvance Y H s W x) * ((f') y):=by
  rw [←at_fires]; obtain ⟨T,h,v⟩:= p; obtain ⟨S,t,u⟩:=t; exact prefactor Y H s W (turn_support a z h) t (ticket_separated Y H s W a z v u)
lemma starboard_turn {x:junior K}(p:x∈wing K a z ℓ) : courseAdvance Y H s W x∈ wing K a z' (reserve Λ l):=by
  obtain ⟨T,v,h⟩:=p; exact ⟨_,travels Y H T s W x v,starboarded a z h⟩
omit W
-- native Grammar linear limits; retain precision
variable (V:Universal Y H i k F E)
include V
private lemma tallied (f:junior K) : E s f.val= Cabinet.audience Y H s V.pick f.val ∧ F s f.val=Cabinet.field Y H s V.pick f.val:=by
  let h : TestFamily K true f.val:= f.property; let t:= V.together s f.val h; let g:= (V.pick.booked Y H s h).2; have he:= funext fun n=> tendsto_nhds_unique (t.inner n) (g.inner n); exact ⟨tendsto_nhds_unique_of_eventuallyEq t.periods g.periods (Eventually.of_forall fun x=>congrFun he (i x)),he⟩

def intake : junior (tent Y H) →ₗ[ℂ] ℂ := ⟨⟨fun f=> V.pick.audience Y H s f.val,fun f g=> V.pick.addA Y H s f.property g.property⟩,fun a f=> V.pick.smulA Y H s a f.property⟩ -- path

def rent (n:ℕ):junior (tent Y H) →ₗ[ℂ] ℂ:= by
  let p:=V.pick; exact {
    toFun:=fun x=> p.field Y H s x.val n
    map_add':= fun x y=> congrFun (p.field_add Y H s x.property y.property) n
    map_smul':= fun a x=> congrFun (p.field_smul Y H s a x.property) n }

lemma intake_eq (f:junior K): intake Y H s V f=E s f.val:= (tallied Y H s V f).1.symm
lemma rent_eq (n:ℕ)(f:junior K): rent Y H s V n f= F s f.val n:= congrFun (tallied Y H s V f).2.symm n
lemma intake_funds (f:Palette S): intake Y H s V (music K S f)=finale Y H S s V f:= intake_eq ..
lemma rent_funds (n:ℕ)(f:Palette S):rent Y H s V n (music K S f)=gaugeEar Y H S s V n f:= rent_eq ..
lemma intake_one:intake Y H s V 1=1:= Cabinet.unitA Y H s V.pick
lemma rent_one (n:ℕ):rent Y H s V n 1=1:= V.pick.unit Y H s n

omit V
include W
lemma sponsor (f:junior K) : intake Y H s W.own f=intake Y H (s+1) W.own (courseAdvance Y H s W f):=by
  obtain ⟨S,t⟩:= supported K f; obtain ⟨x,rfl⟩:=music_rep K S f t; rw [courseAdvance_on,intake_funds,intake_funds]; exact congrArg (fun f:Music S=> f x) (Concord.consistent Y H S s W)
omit W

local notation "ζ"=> gaugeShift Λ.block z
include V

lemma diagonals (f:junior (tent Y H))(p:f∈ wing K a (gaugeShift Λ.block z) (reserve Λ l)):
    0 ≤ intake Y H s V (turn K a ζ f*f):=by
  let F:= turn K a ζ f*f; let Q':= V.pick; let pL: TestFamily K true F.val:= F.property; let t:= (Q'.booked Y H s pL).1
  obtain ⟨S,q,H'⟩:=p; apply ge_of_tendsto t.periods
  filter_upwards [((momentum Y s).comp Q'.grow_i.tendsto_atTop).eventually (hosted K a ζ ℓ H')] with r h
  apply ge_of_tendsto (t.inner (i r)); filter_upwards [Q'.pass Y H s (i r)] with n P'
  unfold hot; rw [dif_pos P'.depth]; exact (boxprice Y H (i r) (k n) P'.depth s P'.fire P'.enters).fund a z _ (((show InTest K true S false f.val from q).support _).mono h)
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.diagonals
#print axioms YM.CF.Buffered.Concord.at_fires
#print axioms YM.CF.Buffered.Concord.wing_fence
#print axioms YM.CF.Buffered.Concord.intake_eq

import YM.SU5.FiniteGaugeData.Concord.Journal
/-! # Cylinder realization in one history. Level marks and read formulas.

No assumption that `screen` is positive or that `W.true_read` includes mixed
markers. Actual `(Y.voyage i).X (Y.uv k)` for the whole evaluation. If using a
level-dependent product, specify meeting level p (above all contributors); must
certify height and **same** β horizon. Rally of unused levels does not change
the reading when qualified. For a tensor element using only these levels, placeholders for
other levels in splitting tensors/`observe` indexing below have NO effect.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 480000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical TensorProduct
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock Heat Girt
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale Style
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
-- name IR index n UV index d and fixed level s
variable (n d s:ℕ)

def grammar (n:Side) : Subalgebra ℂ (Mark n) where
  carrier := {f | AtSupport false univ f}
  mul_mem' := fun (x:AtSupport false univ _) (y:AtSupport false univ _) => x.mulM y
  add_mem' := fun x y=> AtSupport.addM x y
  algebraMap_mem' c:=by rw [Algebra.algebraMap_eq_smul_one]; exact AtSupport.smulM (AtSupport.oneM univ) c

abbrev Choreo (Y:Course Λ (VolumeCape.Dream.Nimbus l))(n s:ℕ):= grammar (side Y n s)

local notation "Tf" s:max => Choreo Y n s
local notation "K" => tent Y H
local notation "N" s:max=> side Y n s
local notation "𝒜" => steps Λ.V (Y.ir n) Λ.block (Y.uv d) s
local notation "P'"=> (Y.voyage n).X (Y.uv d)

lemma univ_haul (p: PairIdx Y s n d)(x:Tf s) : haul Y s n d x.val∈ Tf (s+1):=by
  let a:= (fullness Y n d p.1).cap_grant; have ht:=can_cane Y s p
  let G:=apt (Y.ir n) Λ.block Λ.R.L s; change AtSupport false univ (pushMark G _ _ _ _ _ _ _ _ _ _)
  exact (surround G 𝒜 Λ.K.j _ ((P').gram (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d _ ((Y.voyage n).CapeT s) (legal Λ) ((Y.voyage n).ownership s).paid.bill (a.branch s p.2) ht.1 ht.2 x.val (show AtSupport false univ x.val from x.property) (tissue Y n s) (a.aligned s p.2)).mono (subset_univ _)

def sceneL : junior (tent Y H)→ₐ[ℂ] Choreo Y n s where
  toFun f:= ⟨observe Y H n s f.val, (observe_support Y H n s (p:=(show TestFamily K true f.val from f.property).paid.choose_spec)).mono (subset_univ _)⟩
  map_add' f g:= Subtype.ext (observe_add ..)
  map_mul' f g:= Subtype.ext (observe_mul ..)
  map_one' := Subtype.ext (observe_one ..)
  map_zero' := Subtype.ext (show observe Y H n s 0=0 by rw [observe_formula,Pi.zero_apply,map_zero])
  commutes' x:= by simp_rw [Algebra.algebraMap_eq_smul_one]; apply Subtype.ext; change observe Y H n s (x • 1)= x • 1; rw [observe_scale,observe_one]

lemma scene_eq (x:junior K) : (sceneL Y H n s x).val=observe Y H n s x.val:=rfl

def scenic : Tf s →ₗ[ℂ] Tf (s+1):= if h: PairIdx Y s n d then
  { toFun x:= ⟨haul Y s n d x.val,univ_haul Y n d s h x⟩
    map_add' := fun x y=> Subtype.ext (haul_add _ _ h (show AtSupport false univ x.val from x.property).env (show AtSupport false univ y.val from y.property).env)
    map_smul' := fun x y=> Subtype.ext (haul_scale _ _ h (show AtSupport false univ y.val from y.property).env x) }
  else 0

lemma ticket_v (p:PairIdx Y s n d)(x:Tf s) : (scenic Y n d s x).val= haul Y s n d x.val:=by unfold scenic; rw [dif_pos p]; rfl

section tensor
variable {i k:ℕ→ℕ}
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Playhouse Λ l}
variable (W: Traced Y H i k F E P)
local notation "R"=> junior (tent Y H)
local notation "σ"=>fun s:ℕ=> ↥(Choreo Y n s)
local notation "α"=> fun j:ℕ=> (sceneL Y H n j).toLinearMap
local notation "ℙ"=> scenic Y n d

def stagewrap (f:ℕ→junior (tent Y H)) : Choreo Y n s := (Style.prefixTube (fun s=> ↥(Choreo Y n s)) (fun s=> (sceneL Y H n s).toLinearMap) ℙ s).soc f
lemma stage_begin (f:ℕ→R) : stagewrap Y H n d 0 f=sceneL Y H n 0 (f 0):=rfl
lemma stage_next (f:ℕ→R) : stagewrap Y H n d (s+1) f=scenic Y n d s (stagewrap Y H n d s f)*sceneL Y H n (s+1) (f (s+1)) := rfl

/-- Even before extracting gauge/covariant, keep exact CAR and link and Fock-space payload of a
full tensor. Restrict to its `Style.atLeast s` for identifying with correlation. -/
def realizeStage : Hallspace (tent Y H)→ₗ[ℂ] Choreo Y n s := Style.bill (fun s=> intake Y H s W.own) (fun s=> intake_one Y H s W.own) (fun s=> ↥(Choreo Y n s)) (fun s=> (sceneL Y H n s).toLinearMap) (scenic Y n d) s

lemma stage_e (f:ℕ→junior K)(p:Style.fits s f): realizeStage Y H n d s W (PiTensorProduct.tprod ℂ f)=stagewrap Y H n d s f:= Style.opens _ _ _ _ _ s p
lemma stage_run {x:Hallspace K}(p:x∈Style.atLeast s) : realizeStage Y H n d (s+1) W x= scenic Y n d s (realizeStage Y H n d s W x) := Style.vRun _ _ _ _ _ p (map_one (sceneL Y H n (s+1))) -- need q prop

lemma stage_unit (t:(Y.voyage n).kick ≤ d)(u:s≤Y.uv d) : realizeStage Y H n d s W 1=1:=by
  rw [PiTensorProduct.one_def,stage_e Y H n d s W (1:ℕ→junior K) Style.fits_one]; induction s with
  | zero=> exact map_one (sceneL Y H n 0)
  | succ s ih=>
    rw [stage_next,ih (show s≤_ from Nat.le_of_lt u), Pi.one_apply,map_one (sceneL Y H n (s+1)),mul_one]; apply Subtype.ext; rw [ticket_v Y n d s ⟨t,u⟩]; exact haul_one Y s ⟨t,u⟩

lemma stage_cameo (f:junior K)(p:(Y.voyage n).kick ≤ d)(t:s≤Y.uv d): realizeStage Y H n d s W (Style.stepFactor s f) = sceneL Y H n s f:=by
  rw [Style.insert_at,stage_e Y H n d s W _ (Style.visible s f)]
  cases s with
  | zero=> rw [stage_begin,update_self]
  | succ s=>
    let V :ℕ→junior K:= update 1 (s+1) f; let Y':= Style.prefixTube _ α ℙ s
    have ht: stagewrap Y H n d s V=stagewrap Y H n d s 1:=Y'.depends (fun i t=>update_of_ne (by omega) ..) -- test
    rw [stage_next,update_self,ht, ←stage_e Y H n d s W _ Style.fits_one, ←PiTensorProduct.one_def,stage_unit Y H n d s W p (Nat.le_of_lt t)]
    rw [show scenic Y n d s 1=1 from Subtype.ext ((ticket_v Y n d s ⟨p,t⟩ 1).trans (haul_one Y s ⟨p,t⟩)),one_mul]

local notation "U₀"=> (Y.voyage n).CapeT
local notation "X"=> ((Y.voyage n).X (Y.uv d)).gram

def reader (x:Hallspace (tent Y H)) : ℂ:= Journey.compass Y n d s (realizeStage Y H n d s W x).val

include W
lemma memorable {t:ℕ}{x:Hallspace K}(h:s≤t)(u:x∈Style.atLeast s)(p:(Y.voyage n).kick ≤ d)(q:t≤Y.uv d):
    reader Y H n d s W x=reader Y H n d t W x:=by -- x absent
  induction t,h using Nat.le_induction with
  | base=> rfl
  | succ j h ih=>
    let F:= realizeStage Y H n d j W x; let u':PairIdx Y j n d:= ⟨p,q⟩
    rw [ih (le_of_lt q)]; unfold reader; rw [stage_run Y H n d j W (Style.to_pepper ⊤ h u), ticket_v Y n d j u']; exact score_repeat Y j u' F.val F.property

lemma literal_ear (x:Hallspace (tent Y H))(p:(Y.voyage n).kick ≤ d)(t:s≤Y.uv d):
    let f:= (realizeStage Y H n d s W x).val
    let Z:= denZ ((X) s) Λ.U ((U₀) s); let U:=partitionZ ((X) s) Λ.U ((U₀) s)
    -- Y pivot β0, shared gauge timeline, both planner and shipment beta
    ((X) 0).beta=Λ.x ∧ U ≠ 0 ∧ Integrable (fun i=> letterRead (f (drawn ((U₀) s) i)) (Z i)) (city _) ∧
    reader Y H n d s W x=(∫ i:Orbit (side Y n s), inner ℂ (Dial.mateK _) (acts (f (drawn ((U₀) s) i)) (Z i)) ∂city _)/U:=
  let f':=realizeStage Y H n d s W x; let v:= (Y.each_level n d s p t); ⟨(fullness Y n d p).cap_pivot,v.valid, mark_integrable ((Y.voyage n).ownership s).paid.bill (show AtSupport false univ f'.val from f'.property).env (Marks.can_read _ _ _ _ v),rfl⟩

/-- Even wide stencil can be seen at physical cutoff **without asking for tags** (access by phase is as prescribed by FiniteGaugeData). -/
lemma microscopic_quote (x:Hallspace (tent Y H))(t:(Y.voyage n).kick ≤ d) :
    let m:=Y.uv d; let T:= (realizeStage Y H n d m W x).val
    let Z:= partitionZ (X m) Λ.U (U₀ m)
    Z ≠ 0 ∧ reader Y H n d m W x=(∫ v:Orbit (side Y n m), inner ℂ (Dial.mateK _) (acts (T (v.1,v.1)) (Vale.capP Λ.U (X m).beta (Y.meter.a m) v.1)) ∂city _)/Z := by
  intro m T Z; obtain ⟨h,v,g,p⟩:= literal_ear Y H n d m W x t le_rfl
  refine ⟨v,?_⟩; rw [p]; apply congrArg (· / Z); apply integral_congr_ae; apply Eventually.of_forall; intro i'; dsimp only
  let y:= (Y.voyage n).CapeT; change inner ℂ (Dial.mateK _) (acts (T _) (denZ ((X) m) Λ.U (y m) _))= _; rw [Y.whole]
  let U:=Y.meter.a m; by_cases p: flags U.threshold i'.1=∅
  · have he:y m i'= i'.1:= Vale.Grace.Robes.solar i' _ ((Y.history n d).roof m).paid U ((Y.history n d).pole m) p
    rw [show drawn (y m) i'= (i'.1,i'.1) from Prod.ext rfl he]
  have hh : Vale.capP Λ.U (X m).beta U i'.1=0:= Set.indicator_of_notMem (s:={x:Pane (N m)|flags U.threshold x=∅}) (a:=i'.1) p _
  rw [hh,map_zero,map_zero]
end tensor
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.literal_ear
#print axioms YM.CF.Buffered.Concord.memorable
#print axioms YM.CF.Buffered.Concord.microscopic_quote

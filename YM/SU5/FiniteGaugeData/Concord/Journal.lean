import YM.SU5.FiniteGaugeData.Concord.Cylinder
/-!
# One multi-resolution state. Positive reflected squares on this coupled algebra.

BEFORE vacuum and requiring positive-time buffer. Note the positivity on an individually eligible
word at `Every` would not without proof suffice for this full hierarchy's requirement (e.g. even
mixed common-section matrix). `Printed` not here. Derive ONLY on actual Y limits even
with period-dependent data. No claim of positive metric on any candidate fields away from these
current families. This is LP/RP on self-selected subsystem; still not reconstructing relativistic
dynamics.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical TensorProduct
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock Heat
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale Style
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable {i k:ℕ→ℕ}{s:ℕ}
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Playhouse Λ l}
local notation "K₀"=> tent Y H
local notation "U"=> swept Λ l
variable (W:Traced Y H i k F E P)
local notation "R'"=> fun k:ℕ=> courseAdvance Y H k W
local notation "E₀"=> fun k:ℕ=> intake Y H k W.own
include W

def issue (s:ℕ): Hallspace (tent Y H)→ₗ[ℂ] junior (tent Y H):= bill E₀ (fun n=> intake_one Y H n W.own) (fun _=> ↥(junior K₀)) (fun _=> LinearMap.id) R'
  s

-- for composing this valuation with E
abbrev starGem (s:ℕ)(x:Hallspace (tent Y H)) := intake Y H s W.own (issue Y H W s x)

lemma issue_extends (x:Hallspace K₀)(h:x∈ Style.atLeast (A:=↥(junior K₀)) s): issue Y H W (s+1) x=courseAdvance Y H s W (issue Y H W s x) := Style.vRun _ _ _ _ _ h rfl -- tune
lemma solo_issue (f:ℕ→ junior K₀) (t:Style.fits s f): issue Y H W s (PiTensorProduct.tprod ℂ f)=(Style.prefixTube _ (fun _=> LinearMap.id) (fun k:ℕ=>courseAdvance Y H k W) s).soc f:= Style.opens _ (fun s=> intake_one Y H s W.own) _ _ _ s t -- tune
lemma issue_one (s:ℕ): issue Y H W s 1=1:= by rw [PiTensorProduct.one_def, solo_issue Y H W _ Style.fits_one]; exact Style.prefix_nat (fun _=> ↥(junior K₀)) _ _ (fun _=> rfl) (fun s=> nilPass Y H s W) _
lemma singleIssue (s:ℕ)(f:junior K₀): issue Y H W s (Style.stepFactor s f)=f := Style.inclusion _ _ _ _ _ (fun _=>rfl) (fun s=> nilPass Y H s W) s f -- tune

omit W
def cameo (s:ℕ) : junior (tent Y H) →ₐ[ℂ] building (tent Y H) := (Style.stepFactor s).codRestrict (building K₀) (fun x=> Style.to_pub ⊤ s (Style.stepAt s x))

include W
lemma cameo_inj (s:ℕ) : Injective (cameo Y H s) := -- W may not included in def (not used); add irrelevant W if wants
  fun x y p=> Style.factor_inj (E:=E₀) (fun s=> intake_one Y H s W.own) (n:=s) (congrArg Subtype.val p)

lemma valuation {s t:ℕ}(x:building K₀) (d:s ≤ t)(p:x.val∈Style.atLeast (A:=↥(junior K₀)) s):
    starGem Y H W s x.val=starGem Y H W t x.val:=by
  induction t,d using Nat.le_induction with
  | base=>rfl
  | succ t d h=> exact h.trans (by rw [starGem,starGem,issue_extends Y H W x.val (to_pepper ⊤ d p)]; exact sponsor Y H t W (issue Y H W t x.val))

omit W
def floorLine (K:Calibration)(x:building K) := (Style.by_stages ⊤ x.val x.property).choose -- W not actually included
lemma floorLine_ok (K:Calibration)(x:building K): x.val∈Style.atLeast (floorLine K x):=(Style.by_stages ⊤ x.val x.property).choose_spec -- omit W

include W
private def target (x:building K₀):= starGem Y H W (floorLine K₀ x) x.val
private lemma levelled {x:building K₀}(t:x.val∈ Style.atLeast s) : target Y H W x= intake Y H s W.own (issue Y H W s x.val) :=
  (valuation Y H W x (le_max_left _ s) (floorLine_ok K₀ x)).trans (valuation Y H W x (le_max_right (floorLine K₀ x) s) t).symm

def portfolio : building (tent Y H) →ₗ[ℂ] ℂ where
  toFun := target Y H W
  map_add' x y:=by
    let t:= max (floorLine K₀ x) (floorLine K₀ y); let A:= Style.atLeast (A:=↥(junior K₀)) t
    have ht: x.val∈ A:= Style.to_pepper ⊤ (le_max_left ..) (floorLine_ok K₀ x); have he:y.val∈ A:= Style.to_pepper ⊤ (le_max_right ..) (floorLine_ok K₀ y)
    rw [levelled Y H W (s:=t) (x:=x+y) (A.add_mem ht he), levelled Y H W (s:=t) ht,levelled Y H W (s:=t) he]; change intake _ _ _ _ (issue _ _ _ _ (x.val+y.val))= _; rw [map_add,map_add]
  map_smul' a x:=by
    let t:= floorLine K₀ x; have p:x.val ∈ Style.atLeast t:= floorLine_ok K₀ x; rw [levelled Y H W (s:=t) (x:=a • x) ((Style.atLeast t).smul_mem p a)]; change intake _ _ _ _ (issue _ _ _ _ (a • x.val))= a • intake _ _ t W.own (issue _ _ W t x.val); rw [map_smul,map_smul]

lemma portfolio_hall {x:building K₀}(t:x.val∈Style.atLeast s) : portfolio Y H W x= E s (issue Y H W s x.val).val:= (levelled Y H W t).trans (intake_eq ..)
lemma portfolio_one : portfolio Y H W 1=1:=(levelled Y H W (x:=1) ((Style.atLeast 0).one_mem)).trans (by rw [Subalgebra.coe_one,issue_one,intake_one])
lemma cameo_physical (s:ℕ)(x:junior K₀) : portfolio Y H W (cameo Y H s x)= E s x.val:=
  (portfolio_hall Y H W (x:=cameo Y H s x) (Style.stepAt s x)).trans (congrArg (fun u:junior K₀=> E s u.val) (singleIssue Y H W s x)) -- tune implicit
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.portfolio_hall

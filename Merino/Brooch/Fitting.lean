import Merino.Brooch.Strip
import YM.SU5.Exchange.Pace.Cult

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Brooch
open Function Finset Fock Scroll Spire Sault
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Lattice Cube Scree Skye Sour Drapes Tulip Lat Branch Swell
open Thera Hest Levier
variable {N:Side}
local notation "Jk"=> Single N

open Dial Vow

open Tenant Tap RG Salt Filter Pressure Ione BPress Py.Rate.LocalLimit Preparation
open Py

def feeB(p:BudgetPoint)(m:ℕ)(h a c b r x:ℝ):ℝ:=
 dull 24 m p 32 h a c (exponentialR r x*b)
def feeF(p:BudgetPoint)(m:ℕ)(h a c b r x:ℝ):ℝ:=
 ep 24 m p 32 h a c b (exponentialR r x*b)
def Fcoat(L:Side)(p:BudgetPoint)(m:ℕ)(h a c b r x:ℝ):ℝ:=
 hueW L x*(feeF p m h a c b r x+ZxT L p x (feeF p m h a c b r x))
def Dcoat(L:Side)(p:BudgetPoint)(m:ℕ)(h a c b r x:ℝ):ℝ:=
 hueW L x*(feeB p m h a c b r x+ZxT L p x (feeF p m h a c b r x))/pinpr L x

variable(L:Side)(p:BudgetPoint)(m:ℕ)(h a c b r:ℝ)

lemma feeB_linear(x:ℝ):feeB p m h a c b r x=exponentialR r x*dull 24 m p 32 h a c b:=by
 unfold feeB dull txFee warFee oneWave foFee Brooch.stretch txFee; ring
lemma feeF_exp(x:ℝ):feeF p m h a c b r x=fhFee 24 p 32 h a c (wζ a m)+feeB p m h a c b r x+
 (bright 24 m p 32 h a c b+bright 24 m p 32 h a c b):=rfl


lemma fees_npl(k:0<r):NPL (Fcoat L p m h a c b r)∧ NPL (Dcoat L p m h a c b r):=by
 let V:=feeF p m h a c b r; let U:=feeB p m h a c b r; let γ:=pinpr L; let Z:=hueW L
 let F(x):ℝ:=spanV (radiusB x)*(radiusB x:ℝ)
 have ht:PL F:=PL_spanV.mul PL_radiusX
  -- prefer simp_rw to unfold U for denominator
 have hu:PL U:=by
   unfold U; simp_rw [funext (feeB_linear p m h a c b r)]
   exact (expConst r k).mul (PL.const _)
 have hv:PL V:=by
   unfold V; rw [funext (feeF_exp p m h a c b r)]
   exact ((PL.const _).add hu).add (PL.const _)

 refine ⟨(coolQ L).mul (hv.add ((tallCostP _ _ _ hv).pl)),?_⟩
 have hx:NPL (fun x=>Z x*rNPLΓ L p x /γ x):=by
    apply ((((coolDivPiece L).mul (PL_radiusX.pow 10)).const_mul ((16*(16*Sour.fernL 4)*(Real.exp 1 * (Real.exp 20 + 1)) / 1000)* chi_f p.order))).mono ?_
    filter_upwards with i; apply le_of_eq; apply congrArg abs; unfold Z rNPLΓ γ Ione.annual; unfold Ione.taxIns; ring
 let E(x):= 2*(F x*V x*rNPLΓ L p x)
 have hp:NPL (fun x=>Z x * E x /γ x):=by
    refine (((ht.mul hv).times hx).const_mul 2).mono ?_; filter_upwards with i; apply le_of_eq; apply congrArg abs; unfold E; ring
 have ht':NPL (fun x=> Z x * U x / γ x):=by
    apply ((tailω L r 10 k (by omega)).const_mul (dull 24 m p 32 h a c b)).mono ?_; filter_upwards with i; apply le_of_eq; apply congrArg abs; unfold Z U γ; rw [feeB_linear]; unfold exponentialR; ring
 apply (ht'.add (hp.add ((((ht.times hp|>.mul ((rentNPL L p).pl)).const_mul 2).const_mul (2:ℝ)⁻¹)))).mono ?_
 filter_upwards with i; apply le_of_eq; apply congrArg abs; unfold Dcoat ZxT Z E U γ F; unfold V; ring

lemma unchanged(p':BudgetPoint)(e:p.order=p'.order)(x:ℝ):
 Fcoat L p m h a c b r x=Fcoat L p' m h a c b r x ∧ Dcoat L p m h a c b r x=Dcoat L p' m h a c b r x:=by
 unfold Fcoat Dcoat ZxT rNPLΓ feeF feeB ep bright dull fhFee barFee warFee oneWave foFee txFee treeEarnings reefCost
 rw [e]; exact ⟨rfl,rfl⟩

open Paige Vault
variable {G B R₀ :Side}{j:ℕ}{jY:Odd R₀.val}{U:Pricing j R₀ jY (Thread j)}{e:ℝ}
variable (g: Grasp U B e)
local notation "Ω"=> mid G B
variable {q:ℕ}{Z:ℝ}
variable (R: GramM (mid G B))(x:ℝ)(K:Scree.Loom (mid G B))
local notation "λ_" => R.p
local notation "proj0"=> funde j R.J.M Ω
local notation "vis"=>Moire.bloom R.J.P
local notation "amp"=>hueW L x
-- p exponent rate
structure License (R:GramM (mid G B))(L:Side)(x:ℝ)(K:Scree.Loom (mid G B))
 (g:Grasp U B e)(a c h t:ℝ)(m q:ℕ):Prop where
  dock : DockPulse R.p K t e a h 32 24 q
  ps : Solo a c (funde j R.J.M (mid G B)) e
  ws : Solo a c (Moire.bloom R.J.P) e
  reach : R.p.B+2*m≤24*R.p.B
  old : Sectoral R.p q (scald R.p (head_L R.F)) h (rScale R.p+(R.p.B:ℝ)⁻¹) (RΓK R.p L x)


  moves :∀s:Sweep (mid G B), Steers s (funde j R.J.M _) (Moire.bloom R.J.P) e
  okay:g.roundZ ≤ (mid G B).val
  base:R.slip=0
  width:R.p.B=radiusB x
  qpos:0 < pinpr L x

theorem nestB (u:License R L x K g a c h Z m q)
 (o:Site Ω)(J T:Axis→SOp Ω)(X Y:SOp Ω)
 (A:Strip proj0 vis o m a e b (exponentialR r x*b) J T X Y)
 (vp:p.order= R.p.order)(s:Sweep Ω):
 ∃F:Bag Ω,Nest g R K q 24 (boxA s (node o)) h (rScale R.p)
   ((amp:ℂ) • scene0 s K (leanLatticeFieldEstimates R.p o m J X))
   F
   (Fcoat L p m h a c b r x)
   (Dcoat L p m h a c b r x*pinpr L x):=by
 obtain ⟨he,ke⟩:=unchanged L p m h a c b r R.p vp x
 rw [he,ke,Dcoat,div_mul_cancel₀ _ u.qpos.ne']
 let X0:=scene0 s K (leanLatticeFieldEstimates R.p o m J X)
 let d:ℝ:=(R.p.B:ℝ)⁻¹
 have hd:0<d:=inv_pos.mpr (Nat.cast_pos.mpr R.p.B_pos)
 have hp: Fence proj0 vis K R.p q 24 (boxA s (node o)) h
             (rScale R.p+d+d) X0 (feeF R.p m h a c b r x) (feeB R.p m h a c b r x):=
    downFence (m:=0) (ered s A u.reach u.dock (u.moves s) u.ps u.ws) (rateEx R.p)


 let y:=feeF R.p m h a c b r x
 have hx:∃F:Bag Ω,Nest g R K q 24 (boxA s (node o)) h (rScale R.p) X0 F
   (y+τΓK R.p L x y) (feeB R.p m h a c b r x+τΓK R.p L x y):=by
   have a1 := knock g R K u.dock.roof u.okay u.base
     (by unfold rScale; positivity : 0≤rScale R.p) hd hp u.old
   dsimp only at a1; simpa only [d,inv_inv] using a1
 obtain ⟨F,F'⟩:=hx
 have hV:0 ≤ amp:= by
   unfold hueW stemS
   exact mul_nonneg (div_nonneg u.qpos.le (sq_nonneg _)) (Real.rpow_nonneg (drift_pos _).le _)
 have he0:τΓK R.p L x y=ZxT L R.p x y:=(lifeS L h a c m R.p R.p rfl x u.width y b).1
 have t:= nestScale g R K (amp:ℂ) F'
 rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hV,he0] at t
 exact ⟨_,t⟩
end YM.CF.Merino.Brooch


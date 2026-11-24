import Merino.Brooch.Price
import Merino.Retinue.Livery
import Merino.Retinue.Bridle

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Retinue

open Function Finset Fock Scroll Spire Sault
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Lattice Cube Scree Skye Sour Drapes Tulip Lat Branch Swell
open Thera Hest Levier RG Salt Mew Stax
open Dial Vow Brooch

open Py Rate LocalLimit Preparation BPress
open BProof Tenant Tap Paige Vault

/-- same fee for birth. -/
def saddle(L:Side)(p:BudgetPoint)(h a c b:ℝ)(x:ℝ):ℝ:=
 let C := foFee 24 p 32 h a c b
 C+ZxT L p x C

lemma bills(L:Side)(p:BudgetPoint)(h a c b:ℝ):
  BPress.PL (saddle L p h a c b):=by
 let C := foFee 24 p 32 h a c b
 exact (BPress.PL.const _).add ((tallCostP _ _ _ (BPress.PL.const C)).pl)
lemma sameS(L:Side)(p q:BudgetPoint)(h a c b:ℝ)(x:ℝ)(k:p.order=q.order):
 saddle L p h a c b x=saddle L q h a c b x:=by
 unfold saddle ZxT rNPLΓ foFee txFee treeEarnings reefCost
 rw [k]

variable {G B R₀ :Side}{j:ℕ}{jY:Odd R₀.val}{U:Pricing j R₀ jY (Thread j)}{e:ℝ}
variable {g: Grasp U B e}
variable {q:ℕ}{Z h a b c a' x v :ℝ}
variable {R: GramM (mid G B)}{L:Side}{K:Scree.Loom (mid G B)}{y:Spool (mid G B)}
local notation "Ω"=> mid G B
local notation "λ_" => R.p
local notation "proj0"=> funde j R.J.M Ω
local notation "vis"=>Moire.bloom R.J.P
local notation "Q"=>pinpr L x

open Rive


variable {m:ℕ}(u:License R L x K g a c h Z m q)
variable (s:Sweep (mid G B))(i:Axis)
variable (t:y.Hem K R.p a' b e)(z: a≤ a')
include u t z

def tonic (A:ℝ):ℝ→ℝ:= fun v=>|v*A|

theorem seats(p:BudgetPoint)(k:p.order=R.p.order):
 let A:= tonic (saddle L p h a c b x) v * Q
 ∃F:Bag Ω,Nest g R K q 24 (boxA s y.post) h (rScale R.p)
   (lance y K R.p s i (v*Q)) F A A:=by
 let C:=foFee 24 R.p 32 h a c b
 let T:=scene0 s K (hookeye y R.p i)
 let d:ℝ:=(R.p.B:ℝ)⁻¹
 have hd:0<d:=inv_pos.mpr (Nat.cast_pos.mpr R.p.B_pos)
 have hp: Fence proj0 vis K R.p q 24 (boxA s y.post) h
             (rScale R.p+d+d) T C C:=by
    have h := act_metal s u.dock u.ps u.ws (drop (t.spurt i).pay z)
    exact downFence (m:=0)
         (pane_fee (m:=m) (o:=y.origin) s u.reach (by simp) _ _ _ h true) (rateEx R.p)

 let B' := saddle L p h a c b x
 have e:B'=C+τΓK R.p L x C:=by
    rw [show τΓK _ _ _ _=_ from (lifeS L h a c m R.p R.p rfl x u.width C b).1]
    exact sameS L p R.p h a c b x k


 have ja:∃ F:Bag Ω,Nest g R K q 24 (boxA s y.post) h (rScale R.p)
   T F B' B':=by
   rw [e]
   have a1 := knock g R K u.dock.roof u.okay u.base
     (by unfold rScale; positivity : 0≤rScale R.p) hd hp u.old
   dsimp only at a1; simpa only [d,inv_inv] using a1
 obtain ⟨F,hc⟩:=ja
 have jm:= nestScale g R K ((v*pinpr L x:ℝ):ℂ) hc
 have hk:‖((v*pinpr L x:ℝ):ℂ)‖*B'≤tonic B' v * Q:=by
   simp only [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos u.qpos,tonic,mul_right_comm _ (pinpr L x)]
   gcongr; exact le_abs_self _
 exact ⟨_,nestUp g R K hk hk jm⟩


theorem credits (p:BudgetPoint)(k:p.order=R.p.order)(o:Site Ω)
 (l:inReach R.p o s y)(hp:12 ≤ R.p.B)(g':24*y.stepY≤R.p.B):
 let A:= tonic (saddle L p h a c b x) v * Q
 ∃ F,Office g R K q h A A o (visage y K R.p s i (v*Q))
           (lance y K R.p s i (v*Q)) F:=by
 obtain ⟨F,r⟩:=seats (v:=v) u s i t z p k
 have b1:=touches y R.p g' hp l
 have e0:=issuance s i (v*Q) t
 refine ⟨F, BProof.Bide.mode_p (plainC s i _ t) b1,?_,r.science,?_,fun Z p'=>(e0 Z p').1⟩
 · obtain ⟨E,J,G₁,L,V⟩:=r.pouch.price
   have ht:node o ∈ grooveB 24 R.p ((boxA s) y.post):=halo_spec.mpr ⟨_,mem_singleton_self _,by
       rw [separation_comm]
       exact l.trans (by omega)⟩
   exact ⟨E,J,G₁,fun j H=> L j fun v'=> H (singleton_subset_iff.mpr (v' ht)),V⟩
 intro Z p'
 exact BProof.Garden.scope (e0 Z p').2 (fun i' h'=>(mem_modes ..).mpr (b1 ((mem_modes ..).mp h')))
end YM.CF.Merino.Retinue


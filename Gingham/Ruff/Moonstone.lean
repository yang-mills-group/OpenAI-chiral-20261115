import Gingham.Ruff.Glory
import Gingham.Ruff.Bustle

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}

open RG Vow Hake Tenant
set_option linter.unusedSimpArgs false

open Sour Rill
attribute [local instance] Rill.boreKSpace Rill.boreXN Sour.loreM Sour.loreN
open scoped Classical

open Nacre


open Buffered
open Reed (Fine think)
set_option synthInstance.maxSize 16000

namespace GarlandBook

variable {p:BudgetPoint}{u:Side}{r l:ℕ}{E a c e:ℝ}
    {U':Scree.Loom N}{f h:Chin N→OP N}
    (B:GarlandBook u a c e f h)(g:Briefly p r e U')
    (G:Tagbill a E u l r p.B)
    (d:Shape)(U:UNI SpinIdx)
    (T:Plumes f h a c e)(j:JetS d.s false (detX d.s) U)


open Py Py.Rate.LocalLimit.Preparation Yoke




variable {M:OP N}{ρ:ℝ}

lemma untarnished (s:Finset (Single N)) (hp:0≤ρ):
  Bright ρ (𝒿 (cutM s) M) ((1+ρ^2)*parce M):=by
  unfold 𝒿
  have h: Bright ρ (Matrix.trace (cutM s*M) • (1:FC (Single N))) (parce M):=
    (Bright.mint.scale _).raise ((mul_one _).le.trans ((PE_trace _).trans (PE_crop s M).1))
  rw [add_mul, one_mul]
  apply h.either
  exact (Bright.triumph _ hp).raise (mul_le_mul_of_nonneg_left
    ((PE_crop _ _).2.trans (PE_crop s M).1) (sq_nonneg _))

lemma mintcake (M:OP N) (hp:0≤ρ):
  Bright ρ (ribbonSign d (portico (tickA N) (tackfee d 0 M) M)) ((2+ρ^2)*parce M):=by
  have q:=PE_tack d 0 M
  have y:parce (0:OP N)=0:=by simp [parce]
  rw [y,zero_add] at q
  have t:Bright ρ (portico (tickA N) (tackfee d 0 M) M) ((2+ρ^2)*parce M):=by
      unfold portico;rw [touchP]
      have q:=PE_tack d 0 M;rw [y,zero_add] at q
      exact (((Bright.mint.scale _).raise ((mul_one _).le.trans q)).either (untarnished _ hp)).raise
          ((by ring:parce M+(1+ρ^2)*parce M=(2+ρ^2)*parce M).le)
  unfold ribbonSign
  split
  · simpa only [norm_neg,norm_one,neg_one_smul,one_mul] using t.scale (-1)
  exact t

#print style
#print Matinee.pay
#check Bright.triumph

def milk(ρ:ℝ)(u:Side)(a c:ℝ):ℝ:=(2+ρ^2)*(tableland^2*pepCharge u a c)
include G
lemma readySnow
 (word:List (Axis×ℤ))(i:Axis)(hp:0≤ρ):
 Shines ρ (maiden word (B.bassin g i)) (milk ρ u a c):=by
 let d':=maidS word
 let U₀:=maidU word
 let L:= coinF g (framed d' U₀ (B.point i))
 intro x
 rw [procession word (B.bassin_premier g G i).good]
 let C:=B.eye g i (pitchK (marksleeve word x))
 change Bright ρ (rotary d' U₀ (𝒿 (tickA N) C)) _
 have t: rotary d' U₀ (𝒿 (tickA N) C)=ribbonSign d' (portico (tickA N)
   (tackfee d' 0 (plinth d' U₀ C)) (plinth d' U₀ C)):=by
   simpa only [map_zero, Matrix.trace_zero,portico,zero_smul,zero_add] using
      rotary_portico d' U₀ (maidJ word) 0 C
 rw [t]
 let Z:=B.point i
 have b:L true (pitchK x)=plinth d' U₀ C:=cologne d' U₀ g Z G _ (pitchK (marksleeve word x)) rfl
 rw [←b]
 exact (mintcake _ _ hp).raise (mul_le_mul_of_nonneg_left
    ((opera g G (framed d' U₀ Z)).pay (pitchK x)) (by positivity:0≤ 2+ρ^2))


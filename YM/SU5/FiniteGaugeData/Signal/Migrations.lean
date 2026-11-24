import YM.SU5.FiniteGaugeData.Signal.Portage
import YM.CF.Hive.Hen
import YM.CF.Buffered.RiseReflect
/-! # Coats on actual Pane, tag law moved by donor pressure (in later file).
 Here needed registrations on the exact field arguments. -/
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Advance Reef Hom
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
namespace Momentum
variable {n L B: Side}{e a u v b z:ℝ}{i j:ℕ} {h: Odd L.val}{Y:Pricing j L h (Thread j)}{P:Grasp Y B e}
variable (D:P.roundZ ≤ n.val) -- tune d=round
variable (A:Aim n)(M:Male)(x:Pane n)
local notation "Z"=> P.broadness n D M
local notation "J" i=> spar j M (i:Pane n)
def pullP (j:ℕ)(A:Aim n)(M:Male)(x:Pane n): Op (Single n):= Kennel.capT (spar j M x) (A.den x)
local notation "Ž" i:max => pullP j A M (i:Pane n)
include D
lemma pillar (p:Guard x e):IsStarProjection (spar j M x):= (Z).projection x p
lemma refuge (p:Guard x e):TagG (spar j M x) (Ž x):= tag_g (A.den x) (pillar D M x p)
omit D
local notation "K" f => tradew n f
variable (g:Seat n→ SU.E)(p: Guard x e)
include D p
lemma price_gauge (l:A.toll a b u v) (H:ℝ) : twist (tradew n g) (Furnace.upstairs ((J x)) H * (1- Ž x)) = Furnace.upstairs (J (gauge g x)) H * (1-Ž (gauge g x)):=by
 let T:=tradew n g; have he: A.den (gauge g x)=twist T (A.den x):=(Pec.den_r l).ripe x g
 have ht: twist T ((J x))= J (gauge g x):= ((Z).covary x g p).symm; unfold pullP Kennel.capT; rw [he]; unfold T at ht ⊢; simp only [map_mul,map_sub,map_one,Furnace.upstairs,Furnace.twisting,ht];
local notation "F" a z=> fling a z n
lemma ornaments (t: Stamped j L h Y)(hs:1≤j)(l:A.toll a b u v)(c:Cry A)(z:ℤ)(i:Axis) : twist (carR i z n) (spar j M x)=1-spar j M (fling i z n x) ∧ pullP j A M (fling i z n x)=-(twist (carR i z n) (star (pullP j A M x))) ∧ Guard (fling i z n x) e:=by
 let X:=carR i z n; let S:=plane i z
 have hw: JetS S.s false true (pinLift i):= mirrorX i
 have hu: detX S.s=true:= Spire.det_t _
 let V:= fling i z n x; have hp:sings false X ((J x))=swapX true (J V):= funde_f S inert (pinLift i) hw x j hs _ _ (t.fields_one _ (P.needed.trans D)) (p.shrink P.gem)
 have ht:=Levier.prism_x false S A l c x (pinLift i) (hu.symm ▸ hw); rw [Moire.bloom_P,Moire.bloom_P,hu] at ht
 have h': Guard V e:= keepC inert S x e p
 have hv: Thera.jazz true (twist X (pullP j A M x))=Kennel.capT (J V) (Thera.jazz true (twist X (A.den x))):= Kennel.soil _ _ _ _ X (pillar D M x p) (pillar D M V h') hp
 refine ⟨hp,?_,h'⟩; unfold pullP; change Kennel.capT (J V) (A.den V)=_; rw [show A.den V=Thera.jazz true (twist X (A.den x)) from ht,←hv, map_star]; rfl
end Momentum
end YM.CF.Signal

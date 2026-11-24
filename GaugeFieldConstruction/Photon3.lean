import GaugeFieldConstruction.RiotB3
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Ladder3 Salt Levier Thera Urn Hest Sault Pastry Haro
open XGarden XGarden.MastTin SeasonH Branch Tenant Drapes Rill Nacre Broc SliceRoof
open XGarden.Shield
open Leaf
attribute [local instance] boreKSpace boreXN opCStarAlgebra
variable {R:Loom n}{k:ℕ}{t d a c e r h:ℝ} 
variable (F:Elm n Unit d a c)(R:Loom n)(k:ℕ)(t:ℝ)
-- halves option. Cell width one.V orientation motion.
variable (X S D:Support (More n))(W:Orbit n)
local notation "Vx"=> uplift F R k D S t
local notation "Y"=> Single n
local notation "GL"=> LeanV (Single n)
variable (u:Roof n t d k R)(q:0<d)
open MintB
variable (o:Seat n)
local notation "Zd"=> Pach o
section steer
variable (p q:Bool)(A:ChartP n)
-- easy reindex using stripe_Q.Reading.Navigator.X
lemma βLeg (U:UNI (Single n))(A:ChartP n)(f:FC (Dwell n)→+* FC (Dwell n))(M N:Wa n→ FC (Dwell n)) (h:∀ z x,f (z • x)= cSignX (p.xor q) z • f x) (v:∀ i,f (M i)=∑ j:Wa n,boostX U q i j • N j): f (∑ i:Wa n,A i • M i)=∑ i:Wa n, steerZ U p q A i • N i:=by
 rw [map_sum]; simp_rw [h,v, stripeQ,sum_smul, smul_sum,smul_smul]; rw [Finset.sum_comm]; apply sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [mul_comm]
variable (U:UNI (Single n)) (q':Sweep n)
lemma χLeg (f:FC (Dwell n)→+*FC (Dwell n))(P P' S S': LeanV (Single n) → FC (Dwell n))(h:∀ b i,f (P (b,i))=∑ j:Single n,moko U q b j i • P' (b.xor q,j))(v:∀ b i,f (S (b,i))=∑ j:Single n,moko U q b j i • S' (b.xor q,j))(D D':Wa n→ FC (Dwell n))(hp:f (D none)=D' none)(g:∀ b i j,D (some (b,i,j))=P (b,i)*S (!b,j))(h':∀ b i j,D' (some (b,i,j))=P' (b,i)*S' (!b,j))(i:Wa n): f (D i)=∑ j:Wa n, boostX U q i j • D' j:=by
    rw [Fintype.sum_option]; rcases i with _|⟨b,i,j⟩
    · rw [hp]; simp [boostX]
    rw[g,map_mul,h,v]; simp only [boostX,zero_smul,zero_add]; rw [Fintype.sum_prod_type (α₁:=Bool) (α₂:=Y × Y), sum_eq_single (b.xor q)]
    · rw [Fintype.sum_prod_type (α₁:=Y) (α₂:=Y),sum_mul]; apply Finset.sum_congr rfl; intro i p; rw [mul_sum]; apply sum_congr rfl; intro t h; dsimp only [ite_true,↓reduceIte]; rw [h',Algebra.smul_mul_assoc,Algebra.mul_smul_comm, smul_smul,show (!b).xor q= (!(b.xor q)) from (by cases b<;>cases q<;>rfl)]; rw [if_pos rfl]
    · intro p _ v; exact sum_eq_zero fun j _=>by rw[if_neg v.symm,zero_smul]
    simp
end steer
open Next.SectorChange.Motion Ione
section
-- Ex.P.Portal express Berry.F.Price.Need map.Basis.TP.
lemma Carrier_Y (U:UNI (Single n))(p q:Bool)(G H:Support (More n)→ LeanV (Single n)→ LeanV (Single n)→ℂ)(R T:L3 n)(F:ChartP n) (u:τPure R=τPure T)(s:∀ b i, lotY p q U (pinMode G R.1 (b,i))=∑ j:Single n,moko U q b j i • pinMode H T.1 (b.xor q,j))(t:∀ b i,lotY p q U (pinMode G R.2 (b,i))=∑ j:Single n,moko U q b j i • pinMode H T.2 (b.xor q,j)) : lotY p q U (wax F R G)=wax (steerZ U p q F) T H:=by
 apply βLeg p q U F _ (tokenMode G R) (tokenMode H T) (fun z x=>G_lot ..) -- args
 refine χLeg q U (lotY p q U) (pinMode G R.1) (pinMode H T.1) (pinMode G R.2) (pinMode H T.2) s t _ _ ?_ (fun _ _ _=>rfl) (fun _ _ _=>rfl)
 change lotY p q U (ite _ _ _)=ite _ _ _; rw [u]; split; exact map_one _; exact map_zero _
variable (a:L3 n)(Z:Paper n)(A:Sweep n)
abbrev actX3 (i:SP3 n):= i.map (actY A)
abbrev upX3 (x:L3 n):L3 n:= ⟨actX3 A x.1,actX3 A x.2⟩
local notation "U1"=> Elev F R k t D W
noncomputable def twistW' (s:Sweep n)(V:Orbit n):Orbit n:= (flashA s V.1,bun s V.2)
include u q
section
variable (p:pure_Rim F) (H:groupShape F)
local notation "V"=> Elev F R k t (actY A D) (twistW' A W)
local notation "G'"=> lotY A.charge (detX A.s) (launchZ A)
local notation "B" b:max=> moko (launchZ A) (detX A.s) b
include p H
lemma Riderq3 (w:Injective (priorP W.2))(Z:ChartP n): G' (wax Z a (Elev F R k t D W))=wax (steerZ (launchZ A) A.charge (detX A.s) Z) (upX3 A a) (V):=by -- q
 have he(x:SP3 n)(b:Bool)(i:Y): G' (pinMode U1 x (b,i))=∑ j:Y,(B b) j i • pinMode V (actX3 A x) (b.xor (detX A.s),j):=by
    cases x with |none=> exact L_mile A.charge _ (launchZ A) b i| some x=> exact ΗLeg A.charge (detX A.s) (launchZ A) (gainH F R k t x W D) (giftH F R k t x W D) (gainH F R k t (actY A x) (twistW' A W) (actY A D)) (giftH F R k t (actY A x) (twistW' A W) (actY A D)) (movedΥ F R k t x D W u q A H p w) b i -- order
 refine Carrier_Y (launchZ A) A.charge (detX A.s) U1 V a (upX3 A a) Z ?_ (he a.1) (he a.2)
 unfold τPure upX3; simp [actX3]
omit H
lemma Gaugeq3 (g: Agora n)(C:ChartP n): let X:=tradew n g; let K:=lotY false false X
 K (wax C a (U1))=wax (steerZ X false false C) a (Elev F R k t D (GA g W.1,threadG g W.2)):=by
 intro X' P; let Z':= Elev F R k t D (GA g W.1, threadG g W.2); let U' := (U1)
 have hp(y:SP3 n)(b:Bool)(i:Y): P (pinMode U' y (b,i))=∑ j:Y,moko X' false b j i • pinMode Z' y (b.xor false,j):=by
    cases y with |none=> exact L_mile ..| some y=> exact ΗLeg _ _ _ _ _ _ _ (gauge_γ F R k t y D W u q g p) b i
 exact Carrier_Y X' _ _ U' Z' a a C rfl (hp a.1) (hp a.2)
end
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end

import YM.CF.Chaff.Time
import YM.CF.Vale.Sail
import YM.CF.Fief.Vex
import YM.CF.Hype.Ace
import YM.CF.Ione.Mesh
import YM.CF.Fief.Lucid
import YM.CF.Char.Gel
import YM.Next.STATIONARY.Joint.OnShell
import YM.CF.Rill.Pott
import YM.CF.Skye.Hark
import YM.CF.Prism.Pecu
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Chaff
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Pressure
open Cube Lat Tenant Tulip Gully Spire Scroll Scree Jet Ave Skye Gas Pastry Dial Fock
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B N: Side}{a e K H C:ℝ}{n:ℕ}
local notation "Λ" => CSide m B
local notation "ξ"=> Domain m B
local notation "G"=>SU.group
open Phase Branch
variable {D:Ave.Briar m B e→ Scree.Cipher (CSide m B)}{S:Stamp m B}
variable (p:0≤e)(h:Inscribed K e n S H D C)
local notation "Γ"=> tangD Λ
variable {s:ℝ}{R:Scree.Loom (CSide m B)}{P:BudgetPoint}{c:ℕ}(A:Roof (CSide m B) a s c R)(pH: P.threshold ≤ a)(v:s < e)(l:c≤P.B)
open MultiNext.SignedSource
variable (o:Seat (CSide m B))(y:o∈S) 
variable {r Y V x μ b θ C' ρ:ℝ}
open Gloss Maize Ione Salt Hive Vow
open Hom Vale Vale.Grace Kea Nova RP RP.Str Spark
open Wilson Precision Next.Free Gauge Paige Vault Brace
variable {L:Patch}{Z:Teller SU.group}{W:ChartRatio SU.group}{N0:Postal}(D':Grace Z L W){X:Grasp D'.U B e}{R':Scree.Loom (CSide m B)}{k:ℕ}{u:ℝ}
-- offset aligns Tier output, not yet beta subtraction
abbrev fulvia (A:RegBudget N)(s:ℝ) (Z:GramM N):GramM N:={ Z with F:=A,v:=s}
lemma matter_Re(f:Sweep N)(x:Cipher N): Pastry.pane (Ione.suit_Y f x)=payZ f (Pastry.pane x):=by
 let r:= detX f.s; let b:= f.charge; let S:= Levier.spinU b f.s; let W:= prepU (castX f) S (xtra b) N; let V:= Scree.spice W r
 let L:Dough (LeanV (Single N)):= ⟨windX (b.xor r) x.val,Wtrans _ (fineShape x)⟩; change Pastry.pane (Pastry.fold V L)=_; rw [center_b]; change crumb (windX (b.xor r) x.val) ∅=cSignX (b.xor r) (Pastry.pane x); cases b.xor r <;> rfl
lemma rama {F:Oil (e:=e) m B}(z:MotionY F)(S:Stamp m B)(p:0≤e): ((Pastry.pane (F S (floorP m B p))).im)=0:=by
 let t:Era m:=⟨1,0,true⟩; let s:=netB m B t; have ht:s=⟨1,0,true⟩:=by unfold s t netB; simp; exact map_zero (rBar m B).root -- tune
 have he:boxA s = Equiv.refl _:=by
    apply Equiv.ext; intro x; rw [ht,sitA]; change affine 1 ((assembly Λ).root 0) x=x; rw [map_zero]; simp [affine]
 have hu: linkQ t S=S:=by change _=S; unfold linkQ Hive.actS; change S.map (boxA s).symm.toEmbedding=S; rw [he]; ext; simp
 let X:=floorP m B p; have hx:= z t S X; rw [hu,show shotV t X=_ from waxK p t] at hx
 let V:= F S X; have hq:Pastry.pane V= cSignX (wageZ s) (Pastry.pane V):= (congrArg (@Pastry.pane _ _ _) hx).trans (matter_Re s V)
 have hh:wageZ s=true:=by rw [ht]; change true.xor (detX 1)=true; rw [det_i]; rfl
 rw [hh] at hq; have hv:=congrArg Complex.im hq; change (Pastry.pane V).im= -(Pastry.pane V).im at hv; change _= _; exact eq_zero_of_neg_eq hv.symm -- lemma
variable (β:ℝ)(v':Roof (CSide m B) a u k R')(hd:P.threshold≤a)(t:u<e)(hx:X.roundZ ≤ (CSide m B).val)(hy:Z.top.clip.direct≤1) (q:0≤e)
include v' hd t hx hy
lemma dusk_m (E:RegBudget Λ)(s:ℝ)(P':Briar m B e→ Cipher Λ)(F:∀ i:Briar m B e,pingS P.threshold univ i.val→ exponentL P E i.val=P' i-hollow (s:ℂ))(x:Skye.Orbit Λ)(h:Rue.FleetS P.threshold x.1):
 denZ (fulvia E s (launch D'.L β P Λ)) X R' x= ((Nova.primal Z.top.clip ξ β P.threshold x.1:ℝ):ℂ) • setD X (polarU m B q x.1) (P' (polarU m B q x.1)):=by
 let D:=Z.top.clip; let V:= R' x; let U:=x.1; let W:=launch D'.L β P Λ; let Z':= fulvia E s W; have hX: Guard V e:= (v'.paid x).shrink t.le; let V':= spar Z.j firstM V; have ht:IsStarProjection V':= frame_first X.topB X.baseY (X.couture hx firstM) hX; unfold denZ; by_cases u: flags P.threshold U=∅
 · have hQ:V=U:=Robes.solar x R' v' P hd u; have hp:U∈ Calm G ξ P.threshold:=u
   have hY: Guard U e:= hQ ▸ hX; let y:Briar m B e:=⟨U,hY⟩; let S:= (nursery V' ht); have he: exponentL P E U=P' y-hollow (s:ℂ):=by have hv:pingS P.threshold (univ:Support ξ) U:= (Rue.shoreK P.threshold U (show Rue.FleetS P.threshold U from h) (univ:Support ξ)).mp (show Healthy P.threshold (univ:Support ξ) U from by unfold Healthy; rw [u]; simp); exact F y hv
   have hk: Z'.board x= exp (P' y-hollow (s:ℂ)):=by unfold GramM.board; rw [show exponentL Z'.p Z'.F x.1=P' y-hollow _ from he,show exponentL _ Z'.slip x.1=0 from still_Footprint .., add_zero, show fueled Z'.p Z'.K x=1 from fuel_one _ _ x u,mul_one]
   let Y:=P' y; have hz: Z'.betaL R' x=(s:ℂ)-↑(β*basicP D U):=by
      unfold GramM.betaL; change (s:ℂ)-↑( (D'.L.path 0).inChannels Z.top.clip P β U)-Pec.pigment 0 _= _; rw [pig_b, D'.L.born,plainB Z.top.clip hy P β U u,sub_zero]
   have hC: relV X Z'.J V=changeM X V firstM:= curtain X _ R' {v' with paid:=fun x=>(v'.paid x).shrink t.le} hx V
   change Complex.exp (Z'.betaL R' x) • acts (tank V' (Z'.board x)) (relV X Z'.J V)=(↑(primal D ξ β P.threshold U):ℂ) • setD X (polarU m B q U) _; unfold primal; rw [hz,hk,hC, Set.indicator_of_mem hp,claw]; swap; · exact hY
   have hw(e:ℂ)(T:Cipher Λ):S.cook (exp (hollow e+T))= Complex.exp e • exp (S.cook T):=expReal S _ _
   let a:ℂ:=-(s:ℂ); have ha:hollow a+Y = Y-hollow (s:ℂ):=by
      have he:hollow a= -(hollow (n:=Dwell Λ) (s:ℂ)):=Subtype.ext (neg_smul _ _); rw [he,add_comm]; exact (sub_eq_add_neg ..).symm
   let L:=changeM X U firstM; change _ • acts (tank V' (exp (Y-hollow _))) _= ((Real.exp (-(β*basicP D U)):ℝ):ℂ) • acts (tank (spar Z.j firstM U) (exp Y)) L
   rw [show spar _ _ U= V' from hQ ▸ rfl, tank_eq V' _ ht, tank_eq V' _ ht, ←ha, hw,act_smul, hQ]; letI : NormedAlgebra ℚ (Cipher Λ):= NormedAlgebra.restrictScalars ℚ ℝ _; letI : NormedAlgebra ℚ (FC (Single Λ)) := NormedAlgebra.restrictScalars ℚ ℝ _; rw [←map_exp S.cook S.cookC,smul_smul]; apply congrArg (fun p:ℂ=> p • acts _ _); rw [←Complex.exp_add,Complex.ofReal_exp]; congr 1; unfold a; push_cast; ring
 unfold primal; rw [Set.indicator_of_notMem (show x.1∉_ from u),Complex.ofReal_zero,zero_smul]
 have hg:Z'.board x=0:=by unfold GramM.board; rw [show fueled Z'.p Z'.K x= _ from still_force P x u]; exact mul_zero _
 change _ • acts (tank V' (Z'.board x)) _=_ ; rw [hg,tank_eq _ _ ht,map_zero,act_zero,smul_zero]
end YM.CF.Chaff

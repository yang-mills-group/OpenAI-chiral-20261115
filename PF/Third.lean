import PF.SeaBench
import PF.Movie
import PF.Fountain
import PF.Checkpoint1
import PF.LambdaG
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
namespace PureForce
namespace Third
open Pose Products Hive Stars Vessel Cascade Hake Material
variable (P:Spine)
set_option quotPrecheck false
local notation "Λ"=>P.par
local notation "Y"=>P.run
local notation "cA" => ((Λ).d+(Λ).J.roomX)/2
local notation "d0"=>(Λ).d
local notation "B1"=>(Λ).block
local notation "m1" s:max i:max=>Vale.mesh ((Y).ir i) (Λ).R.L s
local notation "Ns" s:max i:max=>Papal.count (Y) s i
local notation "Φ" s:max i:max k:max=>(Papal.gram (Y) s i k).J
local notation "roomA" s:max i:max=>Papal.room (Y) s i
local notation "personify" s:max i:max k:max V:max =>changeM (m:=m1 s i) (Λ).U V (Φ s i k).M
-- Hold previous election + pose budget all lifts at sufficient i,k. For all h' fee simultaneously even late.
variable (h:P.par |> LocalLimit.Solstitial)(t:P.par |> LocalLimit.Fountain)
include h t
lemma studio : ∃ z c C rate:ℝ,0<z∧0<c∧0<C∧0<rate ∧ ∀ fee:ℝ,1≤fee→∃ κ:ℝ,0≤κ∧ ∀ s:ℕ,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s ≤ P.run.uv k →
    Products.License (Ns s i) (Φ s i k) (Λ).K.j (2*z) cA d0 c C ∧
    (∀ a:Orbit (Ns s i),Guard ((roomA s i) a) cA) ∧ (Λ).U.roundZ ≤ (Ns s i).val ∧
    ∀ (v:gaugeLink (Ns s i))(b:Bool), ∃ (I:Type)(_ : Fintype I)(D:I→Finset (Seat (Ns s i)))(F:I→List (Oboe (Single (Ns s i))))(Wζ:I→Pose.Test (Ns s i) cA z→ℂ)(cc:I→ℝ),
     VistaDelta (m1 s i) B1 (Λ).U (Φ s i k) v b cA z fee rate κ I D F Wζ cc:=by
 obtain ⟨z,c,C,hz,hc,hC,H⟩:=Pose.assigned_rulers P h
 obtain ⟨K,k0,w,v,f,w',E⟩:=t.flow; obtain ⟨k,e⟩:=E.exists
 -- shrink License to z/2. need adjust Peers by pull. alternative delta.policy with margin r=z and then shrink; extend License on z keep Pose issuing on z (not necessarily exactly same z half): rewrite public keep License 2*z. Vista separate on z. easy. Or radius cA global continuity supplies ε_U >0 from Pose.radius, choose shrink; declare both in statement, later min.
 have hd:cA < d0:=by linarith only [(Λ).J.hr]
 refine ⟨z/2,c,C,w,half_pos hz,hc,hC,w',fun fee hf=>?_⟩
 let u0:=(Fintype.card Play:ℝ)*fee; have hg:1 ≤ u0:= one_le_mul_of_one_le_of_one_le (by exact_mod_cast (show 0<Fintype.card Play from Fintype.card_pos)) hf -- note Nonempty Prod
 refine ⟨Vessel.deter⁻¹*Real.exp (2*w)*Real.exp (k0*2*u0^2),by have hx:=deter_pos; positivity,fun s=>?_⟩
 filter_upwards [H s,(Papal.count_grows (Y) s).eventually (eventually_ge_atTop k)] with i hi ht L hL
 obtain ⟨S,u,l⟩:=hi _ hL
 refine ⟨?_,fun t=>Cube.Guard.shrink (u t) ?_,l,fun a b=>?_⟩
 · rwa [show 2*(z/2)=z by ring]
 · linarith only [(Λ).J.hr]
 let n:= Ns s i; let R:= Φ s i L
 let H2:=((Y).voyage i).X (P.run.uv L); have vp:= H2.pull.owns s hL
 have HV: Hom.InterestX (Λ).W.C _ R := by change Hom.InterestX (Λ).W.C _ (H2.gram s).J; exact vp.taste ▸ (((Λ).W.arm ..).sound s)
 obtain ⟨T,F⟩:= e (m1 s i) ht R HV fee hf
 · obtain ⟨I,IF,D,F,W,cc,A⟩:=Vessel.policy a b (Λ).U R F hd z hz (fun x hx z g=> (S.fit a b ( (⟨x,hx⟩,⟨z,g⟩):Pose.Test n cA _)).1) v (zero_le_one.trans hg) w'.le f.le
   letI:=IF; refine ⟨I,inferInstance,D,F,W,cc,{A with hire:= le_trans (sum_le_sum (fun j _=>?_ )) A.hire}⟩; change _ ≤ Real.exp _*u0^_*cc _
   have hn:= (A.price j).1; have hv:1 ≤ (Fintype.card Play:ℝ):=by exact_mod_cast (show 0<Fintype.card Play from Fintype.card_pos)
   gcongr; exact le_mul_of_one_le_left (zero_le_one.trans hf) hv
open Hake
lemma tableau
 (s i k:ℕ)(z c D:ℝ) (hz:0≤z) (hp:Products.License (Ns s i) (Φ s i k) (Λ).K.j (2*z) cA d0 c D)
 {rate fee κ:ℝ} (e:gaugeLink (Ns s i))(b:Bool){I:Type}[Fintype I]{T:I→_}{F:I→_}{X:I→Pose.Test (Ns s i) cA z→ℂ}{A:I→ℝ}(p:VistaDelta (m1 s i) B1 (Λ).U (Φ s i k) e b cA z fee rate κ I T F X A)(hx:P.par.U.roundZ ≤ (Ns s i).val)(x:Pose.Test (Ns s i) cA z):
   let U:=x.1.val; let V:=after e b x; let J:=Φ s i k; let ω:=(Λ).K.j;
   let C:=curt J ω U; let L:=sheet J ω .L U V; let q:=personify s i k U; let g:=personify s i k V;
   let phase:= inner ℂ (acts (quant (exp L)) q) g;
   let f:= rolled J ω U; let y:=rolled J ω V;
   U∈ {U|Guard U d0} ∧ Guard V d0 ∧
   ∃ v:UNI (Single (Ns s i)),v.val=exp L ∧ g=phase • acts (exp (dg L)) q ∧ ‖phase‖=1 ∧
   (∀ R:UNI (Single (Ns s i)), theta R (quant v.val)=quant (twist R v.val)) ∧
   (∀ F:Pastry.ribbon (Single (Ns s i)), star (quant v.val)*tank y F*quant v.val=tank f (paintR false false (star v) F)) ∧
   phase = inner ℂ q (acts (exp (dg (sheet J ω .LK U V))) (acts (quant (1-C)) (acts (1+∑ i,X i x • Hive.drum (F i)) (acts (quant (1+C)) q)))):=by
 intro U V J ω C L q g ph f Y'
 let x':Pose.Test (Ns s i) cA (2*z):=(x.1,⟨x.2.val,x.2.property.trans (by linarith only [hz])⟩)
 obtain ⟨W,ht,w,hb,_,tN,hF,hl⟩:= Stars.algebraic J ω hp e b x'; have hg :=(hp.fit e b x').1
 have hu:Guard U d0:= x.1.property.shrink (show cA≤ d0 by linarith only [(Λ).J.hr]); obtain ⟨q1,q2,q3⟩:=hl q g (sea_g hx U hu _) (sea_g hx V hg _)
 change W.val=exp L at ht; have hP:Stars.pay W q g=ph:=congrArg (fun x:Op (Single (Ns s i))=>inner ℂ (acts (quant x) q) g) ht
 rw [hP] at q1 q2 q3
 refine ⟨hu,hg,W,ht,?_,q2,tN,hF,q3 _ ?_⟩
 · change exp (dg L)=_ at hb; rwa [←hb] at q1
 have he (t:Pane (Ns s i))(u:IsStarProjection (rolled J ω t)): Hive.nest (Λ).U J.P J.M t=acts (quant (1+curt J ω t)) (personify s i k t):=by
    let F:= Dial.spar ω J.M t; let L:= Kennel.capT F (J.P.den t)
    have hh: F*(1-F)=0:=by rw [mul_sub,mul_one,show F*F=F from u.isIdempotentElem.eq,sub_self]
    have ht:exp (dg L)=quant (1+L):= tallied L ?_
    · exact congrArg (fun x=> acts x (personify s i k t)) ht
    unfold L Kennel.capT; change (_*_*F)*((1-F)*_*_)=_; rw [mul_assoc,←mul_assoc F,←mul_assoc F,hh,zero_mul,zero_mul,mul_zero]
 have hT:=p.valuation x; change acts _ (Hive.nest (Λ).U J.P J.M U)=Hive.nest _ _ _ V at hT; rwa [he U (hp.fit e b x').2.1,he V (hp.fit e b x').2.2.1] at hT
end Third
end PureForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

import ZecaRaw
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 800000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric

open scoped TensorProduct
open Six
local notation "κ"=> P.calibration
local notation "R"=> ruler P.par.block
local notation "H"=> P.large
local notation "Y"=> P.run
local notation "Φ"=> P.stateSpace j x
local notation "X"=> P.PortionHil j x
local notation "σ"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "R₀"=> P.history
local notation "J"=> P.Slabs j
local notation "T"=> P.Test


variable (s w:ℕ)


lemma glowPure(z:ℤ){F:P.Test}(h:PureGauge P.calibration F):PureGauge P.calibration (aureole κ j z F):=by
 let K':=P.calibration
 let a:=j
 obtain ⟨S,f,p,o⟩:=h
 let F := Lifted.moveC a z; let g(x:PairsC):=star (f (F x.1,F x.2))
 have ht: Tower.mirror K' a z (scalar K' f)=scalar K' g:= by funext m x; unfold scalar mirror reflMark; rw [Fock.theta_smul,Fock.theta_one]; apply congrArg (fun u :ℂ=> u • (1:Fock.FC (Single _))); unfold g; simp only [reflFields,Prod.map_fst, Prod.map_snd,reflect_onC]; rfl
 refine ⟨Tower.reflectedBox a z S,g,?_,show Tower.mirror K' a z _=_ from ((congrArg (Tower.mirror K' a z) o).trans ht)⟩
 refine ⟨fun v=> ?_, Girt.pole_w _ star continuous_star (Env.along (g:=Prod.map F F) p.env ((move_cont ..).prodMap (move_cont ..)).measurable),fun x y c d=>?_⟩
 · obtain ⟨c,h,e⟩:= p.narrow v; refine ⟨fun x=>star (c (F x)),(h.comp (move_cont ..)).star,?_⟩; rw [show g=fun x=>star (f (F x.1,F x.2)) from rfl,e]; rfl
 exact congrArg star (p.locus (F x.1,F x.2) (F y.1,F y.2) (moved_agree _ _ c) (moved_agree _ _ d))
lemma beamPure(z:ℤ){f:P.Test}(h:PureMatter P.calibration f):PureMatter P.calibration (aureole κ j z f):=
 fun _ x y=>congrArg (theta (carR j z _)) (h _ (reflFields j z x) (reflFields j z y))

lemma facade(z:ℤ)(f:T): P.shifts j z f=aureole κ j (gaugeT κ z) (aureole κ j 0 f):=
 Subtype.ext (mirror_at κ j (sub_zero (gaugeT κ z)) ((marque ..).1 f.property) |>.symm)

variable (hw:0<w)
local notation:max "θ" n:max=> (aureole P.calibration j (gaugeT P.calibration n))

lemma straight_ref (f:T)(h:P.straight j s w f):P.straight j s w (θ w f):=by
 obtain ⟨p,rfl⟩:=h

 exact ⟨inverse Y H s j false w p,rfl⟩
local notation "A" n:max "[" k "]"=> P.chairs j x s n k

lemma chairs_adj (f:T) (p:P.straight j s w f):
 (A w [hw]) (θ w f)= star ((A w [hw]) f):=by
 obtain ⟨p,rfl⟩:=p
 change (A w [hw]) (P.entryTest _ _ (inverse Y H s j false w p))=star _
 rw [P.chairs_card,P.chairs_card,←P.grainStar,map_star]
variable (v:ℕ)(t:0<v)
local notation "σw"=>P.shifts j w
lemma straight_cat (f g:T)(p:P.straight j s w f) (q:P.straight j s v g):
 P.straight j s (w+v) (f*σw g):=by
 obtain ⟨p,rfl⟩:=p; obtain ⟨q,rfl⟩:=q
 exact ⟨edit Y H s j false w v p q, Subtype.ext (editor ..)⟩
lemma chairs_cat (f g:T)(p:P.straight j s w f)(q:P.straight j s v g):
 (A (w+v) [add_pos hw t]) (f*σw g)=(A w [hw]) f*(A v [t]) g:=by
 obtain ⟨p,rfl⟩:=p; obtain ⟨q,rfl⟩:=q
 have e:P.voxTest j s (edit Y H s j false w v p q).val=P.entryTest j s p*P.shifts j w (P.entryTest j s q):=
    Subtype.ext (editor ..)
 rw [← e]
 change (A (w+v) [_]) (P.entryTest _ _ _)=_
 rw [P.chairs_card,P.chairs_card,P.chairs_card, ← P.concat j _ _ _ hw t,map_mul]

local notation "B" n:max "[" k "]"=> P.pith j x s n k
lemma pith_cat (f g:T)(p:P.straight j s w f)(q:P.straight j s v g):
 (B (w+v) [add_pos hw t]) (f*σw g)=(B w [hw]) f*(B v [t]) g:=by
 obtain ⟨I,d,a,b,rfl,up⟩:=P.straight_exhaust j s w f p
 obtain ⟨I',d',a',b',rfl,uq⟩:=P.straight_exhaust j s v g q
 rw [map_sum σw,map_sum (B w [hw]),map_sum (B v [t]), Finset.sum_mul, Finset.sum_mul,map_sum]
 refine sum_congr rfl fun i _=>?_
 rw [Finset.mul_sum, Finset.mul_sum,map_sum]
 refine sum_congr rfl fun m _=>?_
 specialize up i; specialize uq m
 have h₁:PureGauge κ (σw (a' m)):=by rw [facade]; exact P.glowPure _ _ (P.glowPure _ _ uq.2.2.1)
 have h₂:PureMatter κ (σw (b' m)):=by rw [facade]; exact P.beamPure _ _ (P.beamPure _ _ uq.2.2.2)

 rw [map_mul (σw), mul_mul_mul_comm (a i), 
    P.pithFactors j x s w hw _ _ up.2.2.1 up.2.2.2,
    P.pithFactors j x s v t _ _ uq.2.2.1 uq.2.2.2]
 rw [P.pithFactors j x s _ _ _ _ (gaugePure_mul κ up.2.2.1 h₁) (matterPure_mul κ up.2.2.2 h₂),
     P.chairs_cat j x s w hw v t _ _ up.1 uq.1, P.chairs_cat j x s w hw v t _ _ up.2.1 uq.2.1,
     TensorProduct.mapL_mul]

private lemma precious {U:Hilbert} (f g:U.Op) (z y:U.space ⊗[ℂ] U.space):
 inner ℂ (TensorProduct.mapL (star f) (star g) z) y=inner ℂ z (TensorProduct.mapL f g y) :=by
 induction z using TensorProduct.induction_on with
 | zero=> simp
 | tmul x z=> 
   induction y using TensorProduct.induction_on with
   | zero=>simp
   | tmul u v=>
     change inner ℂ (f.adjoint x) u * inner ℂ (g.adjoint z) v=inner ℂ x (f u)*inner ℂ z (g v)
     rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
   | add a b p q=>rw [map_add,inner_add_right,inner_add_right,p,q]
 | add a b p q=>rw [map_add,inner_add_left,inner_add_left,p,q]

lemma pith_adj(f:T)(p:P.straight j s w f)(z y:P.TwinPort j x):
 inner ℂ (P.pith j x s w hw (θ w f) z) y=inner ℂ z (P.pith j x s w hw f y):=by
 obtain ⟨I,d,a,b,rfl,up⟩:=P.straight_exhaust j s w f p
 rw [map_sum,map_sum,map_sum, _root_.sum_apply,_root_.sum_apply,
     sum_inner,inner_sum]
 refine sum_congr rfl fun i _=>?_
 specialize up i

 have h: θ w (a i*b i)=θ w (a i)*θ w (b i):=Subtype.ext (Tower.mirror_times ..)
 rw [h,P.pithFactors j x s w hw _ _ (P.glowPure _ _ up.2.2.1) (P.beamPure _ _ up.2.2.2),
     P.pithFactors j x s w hw _ _ up.2.2.1 up.2.2.2,
     P.chairs_adj j x s w hw _ up.1,P.chairs_adj j x s w hw _ up.2.1]
 exact precious (U:=X) .. 

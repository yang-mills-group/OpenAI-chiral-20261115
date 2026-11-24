import Anomaly.M2
import Anomaly.Apert.Staple
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock Preparation.Yoke

namespace Spine
universe u
open Ione Vow Swell Sour BScale _root_.Zephyr.Chern Mew TreasuryFog Roots Rive
set_option maxHeartbeats 800000

/-- Kept from project's 129 appointment, for Passage.We thread pre-price `TintDemand`
so that scales here are claimed *post-election*, even in the presence of the later
basis-engine demands. m: multiplicity in each lifted parent call. -/
structure TintedShelf (P: Spine)(T:TintDemand)(m:ℕ)(n:ℕ) (Pay kc Γ:ℝ)(Tξ:Hove.Grant P.par.K.j 2)(Z V K W : ℝ→ℝ) : Prop where
  gates : 0 ≤ Pay ∧ 0 ≤ kc ∧ 0 ≤ Γ ∧ Taxi.DayT 6 Γ ∧ crayon T P.par.K P.par.L Pay kc Γ Tξ ≤ P.par.R.L.val ∧ (Neon.KX 5)^3<P.par.R.L.val∧ (Neon.PKard 5)^3<P.par.R.L.val∧10≤ P.par.R.L.val
  blade : BladeQ P.par.R Z W V K
  board : ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s<P.run.uv k → Preparation.qaChairs P.run Pay kc Γ Tξ n m Z V K W s i k

lemma canopy (m:ℕ)(T: TintDemand) :
 ∃ (P:Spine)(K:P.Register)(Pay kc G:ℝ)(Tξ:Hove.Grant P.par.K.j 2)(n:ℕ)(Z V F W:ℝ→ℝ), TintedShelf P T m n Pay kc G Tξ Z V F W ∧ Orbital P K m∧ ∀ R:P.Spectrum0 3→Prop,(∀ᵐ x∂ P.pillars 3,R x)→∃ x:P.Spectrum0 3,R x∧ JointTuple.{u} P K x:=by
  obtain ⟨n,h⟩:= exists_nat_gt ((2+(m:ℝ))*strive_E 6)
  have hz:0 ≤ strive_E 6:=by unfold strive_E Jet.composeCost; positivity
  obtain ⟨P,K,q,r,H,⟨T',t⟩,_,_,hv,hy,_,⟨C,_,_,p⟩,a,k⟩:=bookedS n (le_trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg _):(2:ℝ) ≤ 2+m) hz) h.le) T blankSupplier 1 1 zero_lt_one
  obtain ⟨Pay,kC,Γ,Tξ,u,v,s,Z,y,p1,p2,πx,m'⟩:= T'.fromCrew
  have ht : Odd P.par.R.L.val:= ⟨P.par.R.L.val/2,by omega⟩
  let Rz := reside.{u} P K q r H ht k p
  let Ux:= bandRadius P.run ((RateCover.includes _ _ _ m').staysOn (by rw [P.par.kJ]; exact ⟨2,rfl⟩) P.par.kJ.ge u v Z s p1 p2 m ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) hz).trans h.le)) r.prepared
  obtain ⟨Zv,W',V1,Kf,h0,w⟩:= Ux.scene
  exact ⟨P,K,Pay,kC,Γ,Tξ,n,Zv,V1,Kf,W',⟨⟨u,v,s,Z,y,p1,p2,πx⟩,h0,w⟩,⟨q,r,hy,EarningsRate.atMask P.run (RateCover.stepRate m') r.prepared,visa_onPath P.run r.prepared t,Pay,kC,Γ,Tξ,n,Ux⟩,Rz⟩
variable {P:Spine}{K:P.Register}{Pay kc Γ:ℝ}{Tξ:Hove.Grant P.par.K.j 2}{n m:ℕ}{Z V F W:ℝ→ℝ}
local notation "θS" s:max=> hat P.par.R.L P.par.x s

-- cost statement through request at this Gram. expose Actual and fee, movement qualifiers.
structure Cupwork (P: Spine)(T: TintDemand) (m:ℕ)(n:ℕ)(Pay kc Γ:ℝ)(Tξ:Hove.Grant P.par.K.j 2)(Z V K W:ℝ→ℝ) : Prop extends TintedShelf P T m n Pay kc Γ Tξ Z V K W where
    -- start height s+1 going into P's s step. ANY fixed pos.S> minimum
    opens (mm k0:ℕ) (p:1 ≤ mm) (hk:1 ≤ k0):
       ∃ a b δ:ℝ,∃ F D U:ℝ→ℝ,0<a∧0<b∧ 0<δ∧BPress.NPL F ∧ BPress.NPL D ∧ Quench P.par.R U ∧
       let Y:=P.run; let v:=fun i=>D i * pinpr P.par.R.L i
       Quench P.par.R (chargeC Y Γ k0 v U) ∧ Quench P.par.R (wakeK k0 U) ∧ Quench P.par.R (fees Y v) ∧ Quench P.par.R (stageΛ Y Γ v) ∧
       ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, s+1<Y.uv k →
         let N:= P.par.Ctor (Y.ir i) (s+1); let p:=RootBook Y i k s; let R:=RootBook Y i k (s+1)
         let x:=hat P.par.R.L P.par.x (s+1)
         let r0:= R.p.B+12+2*mm
         (Preparation.passing Y Γ k0 m v U s i k ∧ 13*(P.par.R.L.val+1) ≤ R.p.B ∧ 13*(P.par.R.L.val+1)≤ p.p.B) ∧
         ∃ (J T:Axis→ SOp N)(X L:SOp N), CartPins Y i k (s+1) mm a b (F x) (D x) J T X L ∧
           (let f:=traceMeter R.p ((Y.voyage i).CapeT (s+1)) 0 X ∘ (Zephyr.Chern.petals (Zephyr.Chern.stream N)); Bud f ∧ δ < (bud f 2).re) ∧
           -- Stress copies. same ". Journal. Projection. -
           (∀ o:Site N, ∃ E G ψ φ,Plot R P.par.U ((Y.voyage i).CapeT (s+1)) o (offsetMask r0 o) r0 (tested Y o X J k mm) (puffKey Y X J k mm o) E G ψ φ P.par.R.L k0 P.par.h (chargeC Y Γ k0 v U x) (wakeK k0 U x) (stageΛ Y Γ v x) (fees Y v x)
            (‖(hueW P.par.R.L x:ℂ)‖ * framePay (Tenant.quota^2*b)) (2*Moto.peka_H (Y.meter.a 0).power * fees Y v x)) ∧
           (∀ {I:Type}[LinearOrder I][Fintype I](σ:I→ Site N), Force_M R.p.B (Cube.node ∘ σ) k0 →∀ (o:Site N)(v:I→Sweep N), (∀ j,Ione.Clock.mPath (v j) (σ j)=o) → ∀ l:List I, ψS (Cube.node∘σ) l → l.Pairwise fun i j=>Disjoint (Salt.actY (v i) (offsetMask r0 o)) (Salt.actY (v j) (offsetMask r0 o)))

private lemma gapLic {n:Side}(s:Sweep n)(o o':Site n)(a:ℕ)(p:Ione.Clock.mPath s o'=o) : Salt.actY s (offsetMask a o)=offsetMask a o' := by
 rw [← p]; ext i; unfold offsetMask Salt.actY; rw [Finset.mem_map_equiv]; rw [Ione.Clock.nodeA]; simp [halo_spec,Ione.Clock.nodeA,sitT]

lemma TintedShelf.buy {T:TintDemand}(q:TintedShelf P T m n Pay kc Γ Tξ Z V F W)(e:Orbital P K m) : Cupwork P T m n Pay kc Γ Tξ Z V F W:=by
  refine ⟨q,fun mm k0 p hk=>?_⟩
  obtain ⟨a,b,H,D,h,f,z,t,S⟩:= weighAll P.run e.roster.prepared e.compass e.reg mm
  obtain ⟨δ,p',H0⟩:=aperture_field P (SprigFee.paid _) a b h mm p
  let H':= fun i=> D i * pinpr P.par.R.L i; have T':Quench P.par.R H':= productQuench (npl_chill t)
  obtain ⟨u,U,Y⟩:= programSizes P.run k0 Γ q.gates.2.2.2.1 q.gates.2.2.1 e.roster.prepared Pay kc Tξ n m Z V F W H H' T' (npl_chill z) hk q.blade q.board -- tune binder order
  obtain ⟨y,r,l,w,v⟩:= quenchingStage P.run Γ k0 H' T' u U
  refine ⟨a,b,δ,H,D,u,h,f,p',z,t,U,?_⟩
  intro K Q; refine ⟨w,v,y,l,?_⟩
  filter_upwards [Y,(tendsto_add_atTop_nat 1).eventually S,(tendsto_add_atTop_nat 1).eventually H0,((Work.E01.radiusB_tendsto.comp (turnover P.par)).comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop 20] with s e sQ v hs; filter_upwards [e,sQ] with i e sQ k kk N P₀ R x r0
  obtain ⟨E,G⟩:=e k kk; obtain ⟨J,T,X,L,Y⟩:=sQ k kk
  refine ⟨G,J,T,X,L,Y,v i k kk _ _ _ _ _ _ Y,(fun i=> postPose P.run k0 Γ H D u s _ _ Y E kk hs i),?_⟩
  intro I _ _ σ h o t p l z
  have hb :20≤R.p.B:=(p_meters P.run i k (s+1) kk).1.symm ▸ hs
  have hp1:l.Pairwise fun i j=> node (σ i)≠ node (σ j):= List.pairwise_map.mp z
  refine hp1.imp ?_; intro i j v; rw [gapLic (t i) o (σ i) _ (p i),gapLic (t j) o (σ j) _ (p j)]; refine Contact.spacing 0 _ _ _ _ ?_; apply lt_of_le_of_lt ?_ (h.1 i j v)
  let b:= R.p.B; change b+12+2*mm+(b+12+2*mm) ≤ b^3+b^3+b+b
  have hv:b ≤ b^3:= le_self_pow₀ (show 1≤ b by change 20 ≤ b at hb; omega) (by norm_num)
  have hp:24*mm ≤ b:=Y.curtain; change 20≤ b at hb; omega

/-- CP3. Use mm say windSeparation P. Signed actual Tilt eligible for
Aperture normal step query with powers seeds. For exact readings see also
Preparation.stylusRead. -/
theorem currentApertCarte (T:TintDemand) (mc:ℕ) :∃ (P:Spine)(K:P.Register)(x:P.Spectrum0 3)(Pay kc Γ:ℝ)(Tξ:Hove.Grant P.par.K.j 2)(n:ℕ)(Z V F W : ℝ→ℝ), Orbital P K mc ∧ JointTuple.{u} P K x∧SprigFee P∧ Cupwork P T mc n Pay kc Γ Tξ Z V F W:=by
  obtain ⟨P,K,p,c,g,X,i,Z,V,F,W,U,D,M⟩:= canopy.{u} mc T
  obtain ⟨x,_,h⟩:= M (fun _=>True) (Filter.Eventually.of_forall fun _=>True.intro)
  exact ⟨P,K,x,p,c,g,X,i,Z,V,F,W,D,h,SprigFee.paid P,U.buy D⟩
#print axioms currentApertCarte
#print axioms Preparation.stylusRead
#print axioms Preparation.gaps
#print axioms Buffered.Advance.flies_theta
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

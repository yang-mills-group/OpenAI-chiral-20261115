import GaugeFieldConstruction.GlamorDewL
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke SelectionAnalysis
open Repertoire 
variable {P:Spine}
namespace Shower
open SignetS
variable {cost:ℕ→P.Test→ℂ} {j: Axis}(C:Porch P cost j)
open YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric FirstPackMars Stage Calibration Phys Calibration.Floor
open NSF.Table.Pairing
attribute [local instance] Ember.iG Ember.iF Ember.iX Ember.iU Ember.iT2 Ember.iW2 Ember.iV Ember.iS
variable {n:ℕ}{S: City} {P0:Axis→Empire.Across} {L:Sheds S P0} {Cu: Supplies L} {u:ℕ→Carat}
-- axis carried thru. CPI covariance proper. Suit has ALL axes declared, no H3 tilt for phase yet
variable (Cw:∀ j:Axis,Porch P cost j)
variable (R:ΧiMars →ₗ[ℂ]ScreensJ P) (G:CloudsL) (t:Ticket u Cu)
open NSF.Boundary NSF.OS.Semigroup -- no OS namespace clash
open NSF.LD
-- (137)-->(138) variant: projection joint on actual POS. norm displacement criterion; everything commutes on same Hil. use E2 costs, no invocation of L1 for chosen x until after L3!
variable (a:Axis)(p: Points n)(v:eastL n a p)(F:Fin n→ ΧiMars)(J:StallLeadMars a p P)
variable (χ:P.Spectrum0 3)(U:CheckΩL R)
open Set Complex
variable (J0: SunlitL P.publicH R G)(f: SurfCheckL.boisterL t G)
variable (E:∀ᵐ x∂P.pillars 3,P.lodestar 3 x) (Z:∀ᵐ x∂P.pillars 3, CriteriaL (P.privateH x) R)
open PlaneL
def feasibleL (s:SO)(n:ℕ): Set (Points n):= blueL n∩motionMoonMars s ⁻¹' blueL n
lemma easeL (s:SO)(n:ℕ):IsOpen (feasibleL s n):= (clearL n).inter ((clearL _).preimage (motionθL _))
def PureCovL (s:SO):Prop:=∀ (n:ℕ)(p:Points n)(F:Fin n→ ΧiMars), p∈feasibleL s n→ CoralL Cw R (compassPiMars t s ∘ F) (motionMoonMars s p)= CoralL Cw R F p
noncomputable def homeVoyL (g:SO)(n:ℕ):Points n≃ₜPoints n where
 toFun:= motionMoonMars g
 invFun:= motionMoonMars g⁻¹
 left_inv x:=by rw [←WindyMissionMars,inv_mul_cancel]; exact calend_oneMars x
 right_inv x:=by rw[←WindyMissionMars,mul_inv_cancel]; exact calend_oneMars x
 continuous_toFun:= motionθL _
 continuous_invFun:= motionθL _
lemma lensBlueL (n:ℕ):Dense (blueL n):= (Dash.full n).mono (show YM.generic n ⊆ blueL n from fun x h=> westBlueL timeAxis (h _)) -- tune binder fun
lemma BridgeCovL (H: Set (Points n))(h:Dense H) (s:SO) {f g:Points n→ℂ}(u: ∀ x∈feasibleL s n, ContinuousAt f x)(v:∀ x∈feasibleL s n, ContinuousAt g x)(t:Set.EqOn f g (feasibleL s n ∩ H)): Set.EqOn f g (feasibleL s n):=by
 let T:=feasibleL s n; intro x hx
 haveI:=mem_closure_iff_nhdsWithin_neBot.mp ((easeL s n).inter_closure (show x∈ T ∩ closure H from ⟨hx,h x⟩)); exact tendsto_nhds_unique_of_eventuallyEq ((u x hx).tendsto.mono_left (nhdsWithin_le_nhds (s:=T∩ H))) ((v x hx).continuousWithinAt) (t.eventuallyEq_of_mem self_mem_nhdsWithin)
include U
lemma LegitL (H:Set (Points n))(h:Dense H)(s:SO)(t': ∀ p∈feasibleL s n∩ H, CoralL Cw R (compassPiMars t s ∘ F) (motionMoonMars s p)= CoralL Cw R F p):∀ p∈feasibleL s n, CoralL Cw R (compassPiMars t s ∘ F) (motionMoonMars s p)= CoralL Cw R F p:=by
 intro p hp
 exact BridgeCovL H h s (f:=CoralL Cw R (compassPiMars t s ∘ F)∘ motionMoonMars s) (fun x h=> (BlueAtL Cw R _ _ U h.2).tendsto.comp ((motionθL _).tendsto x)) (fun x h=> BlueAtL Cw R x F U h.1) (fun z e=>t' z e) hp
lemma PureX_L (p v:SO)(h:PureCovL Cw R t p)(e:PureCovL Cw R t v):PureCovL Cw R t (p*v):=by
 intro n x F d; let s:= (homeVoyL v n) ⁻¹' blueL n
 refine LegitL Cw R t F U s ?_ (p*v) ?_ x d
 · exact (lensBlueL n).preimage (homeVoyL v n).isOpenMap -- tune
 intro x y; obtain ⟨⟨hx,hw⟩,q⟩:=y
 have he: motionMoonMars v x∈ feasibleL p n:=⟨q, by change motionMoonMars p (motionMoonMars v x)∈ blueL n; rw [←WindyMissionMars]; exact hw⟩
 rw[WindyMissionMars,show compassPiMars t (p*v)∘ F= compassPiMars t p ∘ (compassPiMars t v ∘ F) from funext fun i=> sailMulMars t _ _ _]
 exact (h n _ (compassPiMars t v ∘ F) he).trans (e n x F ⟨hx,q⟩)
omit U
lemma Pure1_L: PureCovL Cw R t 1:=fun n p F _=> congrArg₂ (CoralL Cw R) (funext fun i=> sailOneMars t _) (calend_oneMars p)
lemma PureInv_L (s:SO)(p: PureCovL Cw R t s): PureCovL Cw R t s⁻¹:=by
 intro n x F e; let y:= motionMoonMars s⁻¹ x; let K:= compassPiMars t s⁻¹; have hv:motionMoonMars s y=x:= (homeVoyL s n).right_inv x
 have h:= p n y (K ∘ F) ⟨e.2,(show motionMoonMars s y∈ blueL n from hv.symm ▸ e.1)⟩; unfold K at h; rw [hv,PiFlowCancelMars] at h; exact h.symm
include U Z E f J0
lemma PureLightL (i j:Axis)(h:i≠j):∀ᵐ x∂P.pillars 3,∀ s:ℝ, PureCovL (P.privateH x) R t (Ψ i j s):=by
 obtain ⟨k,q,p,_⟩:= moreKeyL 0 i j
 filter_upwards [eventually_countable_forall.mpr (fun n:ℕ=> GlamorAllL R G t U J0 f E Z h q p n)] with x e s n v F u
 exact LegitL (P.privateH x) R t F U (westL n k) ((Dash.full n).mono (show YM.generic n ⊆ westL n k from fun z b=>b k)) (Ψ i j s) (fun z w=> (e n s z w.2 F).symm) v u
lemma PureAllL: ∀ᵐ x∂P.pillars 3,∀ s:SO,PureCovL (P.privateH x) R t s:=by
 have he: ∀ᵐ x∂P.pillars 3,∀ i j: Axis,i≠j→ ∀ s:ℝ,PureCovL (P.privateH x) R t (Ψ i j s):=by
    apply ae_all_iff.mpr; intro i; apply ae_all_iff.mpr; intro j; by_cases p:i=j
    · subst j; exact Eventually.of_forall fun _ e=>(e rfl).elim
    exact (PureLightL R G t U J0 f E Z i j p).mono fun _ h _=> h
 filter_upwards [he] with x h s; exact solarL s (p:=PureCovL (P.privateH x) R t) (fun i j t e=>h i j e t) (Pure1_L _ _ _) (PureX_L _ _ _ U) (PureInv_L _ _ _)
omit U Z E f J0
abbrev ΩPairL (n:ℕ):= {p:Fin n×Fin n//p.1≠p.2}
abbrev LensPairL (v:ΩPairL n)(p:Points n)(a:Axis):Prop:= p v.val.1 a ≠ p v.val.2 a
lemma denseQuiverL (a:Axis)(p:Points n)(e:p∈conf n):∃ s:SO,motionMoonMars s p∈westL n a:=by
 suffices h:∀ l: Finset (ΩPairL n),∃ s:SO,∀ i∈l,LensPairL i (motionMoonMars s p) a from by
    obtain ⟨s,h⟩:=h Finset.univ; refine ⟨s,fun i j q=>?_⟩; by_contra v; exact h ⟨(i,j),v⟩ (Finset.mem_univ _) q
 intro l; induction l using Finset.induction_on with
 | empty=> exact ⟨1,by simp⟩
 | insert x l hx ih=>
    obtain ⟨s,H⟩:=ih; let p':= motionMoonMars s p; let y:=p' x.val.1; let z:= p' x.val.2
    have ht:y≠z:= fun v=> x.property (e (s.val.motion.injective v)) -- tune
    by_cases v:y a=z a
    swap; · exact ⟨s,fun i t=> by obtain rfl|hh:= Finset.mem_insert.mp t; exact v; exact H _ hh⟩ -- semicolon risk
    obtain ⟨b,u⟩:∃ b:Axis,y b≠ z b:=by by_contra! h; exact ht (PiLp.ext h)
    have g:a≠b:=fun h=> u (h ▸ v)
    let T':= fun r:ℝ=>motionMoonMars (Ψ a b r) p'; have he:Tendsto T' (𝓝 0) (𝓝 p'):= by
        have hp:= (angleθL a b p').tendsto 0; rw [basicSphereL,show motionMoonMars 1 p'=p' from calend_oneMars p'] at hp; exact hp
    have hw:∀ᶠ t in 𝓝[>] (0:ℝ),∀ i:ΩPairL n,i∈l→ LensPairL i (T' t) a:=by
        apply eventually_all.mpr; intro i; by_cases c:i∈l
        · let s':= {p:Points n | p i.val.1 a≠p i.val.2 a}; have e:IsOpen s':=  (show IsClosed {p:Points n | p i.val.1 a=p i.val.2 a} from isClosed_eq (by fun_prop) (by fun_prop)).isOpen_compl
          exact ((he.mono_left nhdsWithin_le_nhds).eventually (e.mem_nhds (H i c))).mono fun _ q _=> q
        exact Eventually.of_forall fun _ h=>(c h).elim
    obtain ⟨t,w,d,D⟩:= (hw.and (((show ∀ᶠ t in 𝓝[>] (0:ℝ),0<t from self_mem_nhdsWithin)) |>.and (((show ∀ᶠ t in 𝓝 (0:ℝ),t<Real.pi from gt_mem_nhds Real.pi_pos)).filter_mono nhdsWithin_le_nhds))).exists -- syntax
    have hE:LensPairL x (T' t) a:=by
        intro e; change Ortho.move (Ortho.oneParameter (Ortho.plane a b) _) y a= Ortho.move (Ortho.oneParameter (Ortho.plane a b) t) z a at e
        rw [(YM.Work.A13.plane_givens g y t).1,(YM.Work.A13.plane_givens g z t).1, v] at e
        exact u (mul_left_cancel₀ (Real.sin_pos_of_pos_of_lt_pi d D).ne' (add_left_cancel e))
    refine ⟨Ψ a b t*s,?_⟩; intro i c; rw[WindyMissionMars]; obtain rfl|p:= Finset.mem_insert.mp c; exact hE; exact w _ p
#print axioms PureAllL
#print axioms denseQuiverL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end

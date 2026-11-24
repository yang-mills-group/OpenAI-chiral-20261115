import GaugeFieldConstruction.EstreLiteL
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
variable {m:ℕ}
noncomputable def gluedYL (p:Points n)(y: Points m):Points (n+m):= points (Fin.append p.ofLp y.ofLp)
lemma brightLYL (y:Points m)(i:Fin n): gluedYL p y (Fin.castAdd m i)= p i:= Fin.append_left ..
lemma brightRYL (y:Points m)(i:Fin m): gluedYL p y (Fin.natAdd n i)=y i:= Fin.append_right ..
lemma GlueConfYL (x:Points n)(y:Points m)(h:x∈conf n)(v:y∈conf m)(e:∀ i j,x i≠y j): gluedYL x y ∈ conf (n+m):=by
 change ∀ ⦃i j⦄, _ → _ -- tune
 intro i; refine Fin.addCases ?_ ?_ i
 · intro u j; refine Fin.addCases ?_ ?_ j
   · intro w h'; exact congrArg _ (h ((brightLYL x y u).symm.trans (h'.trans (brightLYL x y w))))
   intro k g; exact (e u k ((brightLYL x y u).symm.trans (g.trans (brightRYL x y k)))).elim
 intro k j; refine Fin.addCases ?_ ?_ j
 · intro u g; exact (e u k ((brightLYL x y u).symm.trans (g.symm.trans (brightRYL x y k)))).elim
 intro w h'; exact congrArg _ (v ((brightRYL x y k).symm.trans (h'.trans (brightRYL x y w))))
abbrev apartYL (z:E4)(p:Points n)(y:Points m):= gluedYL p (NSF.Points.across z y)
abbrev EarYL (i:ℕ):E4:= (i:ℝ) • basis timeAxis
lemma streetsYL (x: Points n)(y:Points m)(h:x∈conf n)(v:y∈conf m):∀ᶠ i:ℕ in atTop, apartYL (EarYL i) x y∈conf (n+m):=by
 have hp:∀ᶠ i:ℕ in atTop,∀ u:Fin n,∀ w:Fin m,x u timeAxis<(y w timeAxis)+(i:ℝ):=by
    apply eventually_all.mpr; intro u; apply eventually_all.mpr; intro w; filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (x u timeAxis-y w timeAxis))] with i p; linarith
 filter_upwards [hp] with i p; refine GlueConfYL x _ h (NSF.Points.across_in _ v) fun j k v=>?_ ; have he:=congrArg (fun z:E4=>z timeAxis) v; change x j timeAxis=(y k+(EarYL i)) timeAxis at he; exact (p j k).ne (by simpa [EarYL] using he)
lemma motionGlueYL (s:SO) (x:Points n)(y:Points m): motionMoonMars s (gluedYL x y)=gluedYL (motionMoonMars s x) (motionMoonMars s y):=by ext1 i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i; rw[brightLYL]; exact congrArg s.val.motion (brightLYL x y i); rw [brightRYL]; exact congrArg s.val.motion (brightRYL x y i)
lemma motionApartYL (s:SO)(z:E4)(x:Points n)(y:Points m): motionMoonMars s (apartYL z x y)= apartYL (s.val.motion z) (motionMoonMars s x) (motionMoonMars s y):=by unfold apartYL; rw[motionGlueYL,TurnFolioL] -- tune
lemma DesGlueYL (z:E4)(x:Points n)(y:Points m)(h:apartYL z x y∈westL (n+m) a): x∈westL n a ∧ y∈westL m a:=by
 let Y:= NSF.Points.across z y
 have he:gluedYL x Y ∈ westL (n+m) a:=h
 refine ⟨?_, (basicWestL y a z).mp ?_⟩
 · intro i j h
   have ht:Fin.castAdd m i=Fin.castAdd m j:=he (by change _=_; change gluedYL x Y _ a= gluedYL x Y _ a; rw[brightLYL,brightLYL]; exact h)
   have hv:= congrArg Fin.val ht; exact Fin.ext hv
 intro i j h; have ht:Fin.natAdd n i=Fin.natAdd n j:=he (by change _=_; change gluedYL x Y _ a=gluedYL x Y _ a; rw [brightRYL,brightRYL]; exact h); exact Fin.ext (Nat.add_left_cancel (show n+i.val=n+j.val from congrArg Fin.val ht))
lemma OasisYL (x:Points n)(y:Points m)(h:x∈conf n)(v:y∈conf m): ∃ s:SO, motionMoonMars s x∈ westL n a ∧ motionMoonMars s y∈westL m a ∧ 0< s.val.motion (basis timeAxis) a:=by
 obtain ⟨r,p⟩:= (streetsYL x y h v).exists; let Q:= apartYL (EarYL r) x y
 let H:Points 2 := points (![0,basis timeAxis]); have hp:H∈ conf 2:=by
    intro i j h; have he: basis timeAxis≠0:=norm_pos_iff.mp (by simp)
    fin_cases i <;> fin_cases j <;> simp [H,he,eq_comm] at * -- bad simp unfolds all? use only
 obtain ⟨t,e⟩:= (streetsYL Q H p hp).exists
 obtain ⟨s,q⟩:= denseQuiverL a _ e; rw[motionApartYL] at q
 obtain ⟨u,hm⟩:=DesGlueYL a _ _ _ q; change motionMoonMars s Q∈_ at u; unfold Q at u; rw [motionApartYL] at u
 obtain ⟨X,Y⟩:= DesGlueYL a _ _ _ u
 let d:=s.val.motion (basis timeAxis)
 have he:d a≠0:=by
   intro z; apply (one_ne_zero (α:=Fin 2)) (hm ?_); change s.val.motion (H 1) a=s.val.motion (H 0) a; rw [show H 0= 0 by simp [H], show H 1=basis timeAxis by simp [H],map_zero]; exact z
 rcases lt_or_gt_of_ne he with h|h
 · obtain ⟨b,p,_,_⟩:=moreKeyL a a a
   let V:=QκL a b; have HN (x:E4):V.val.motion x a= -(x a):=by
      change Ortho.move _ _ _= _; rw [hemiKeyL,Ortho.move_mul,Signed.mirrored, Signed.mirrored]; split_ifs <;> simp_all [Jj] -- maybe recursive
   have hu{n:ℕ}(x:Points n)(X:motionMoonMars s x∈westL n a):motionMoonMars (V*s) x∈ westL n a:=by
      rw [WindyMissionMars]; intro i j h; apply X; change V.val.motion _ a= V.val.motion _ a at h; rw [HN,HN] at h; exact neg_injective h
   refine ⟨V*s,hu x X,hu y Y,?_⟩; change 0< Ortho.move (V.val*s.val) _ a; rw[Ortho.move_mul]; change 0< V.val.motion _ a; rw[HN]; exact neg_pos.mpr h
 exact ⟨s,X,Y,h⟩
#print axioms OasisYL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end

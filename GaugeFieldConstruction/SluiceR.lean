import GaugeFieldConstruction.SimaBoltR
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
variable {I:Type}[Fintype I][DecidableEq I]{cost:ℕ→P.Test→ℂ}{j:Axis}(C: Porch P cost j)
variable (σ:I→PermWallJ P)(A:I→P.Slabs j)(x y : I→Axis→ℝ)(i:I)(b:Option ℝ)(L:List I)
variable (c:Option ℝ)
local notation "ζ"=> C.BrightHab
local notation "Η" => C.DegreeHab
local notation "Ξ"=> C.ρ
local notation "η"=> C.groundHab
local notation "Z" t:max=> (ζ).E t
local notation "X"=> StageR σ C A
lemma freeze_diaR (i:Axis)(v w:Axis→ℝ) (t:∀ a≠i,v a=w a): diameter (a:=i) v=diameter (a:=i) w:=by
 apply Subtype.ext; ext a; by_cases p:a=i; subst a; exact (diameter (a:=i) v).property.trans (diameter (a:=i) w).property.symm
 exact (diameter_at _ _ p).trans ((t _ p).trans (diameter_at _ _ p).symm)
lemma StrutσR (e:∀ k≠j,x i k=y i k): Strut_R C σ A i (x i)= Strut_R C σ A i (y i):= by unfold Strut_R; rw [freeze_diaR j _ _ e,freeze_diaR j (-(x i)) (-(y i)) (fun a p=> by rw [Pi.neg_apply,Pi.neg_apply,e a p])]
-- spacings in unscaled units. U suit.PlaneS
variable (r B d:ℝ)
abbrev RollνR (k:ℝ) (p:Option ℝ) (x y:ℂ) := p.isSome
abbrev Cron_R (t:ℝ) (p:Option ℝ) (x:I→Axis→ℝ) (L:List I) :Prop:=
 (StageR σ C A).Correct L {z:ℝ × ℝ|t ≤ z.2-z.1} x p
abbrev PoleR(d:ℝ)(b c: Option ℝ):Prop := b=none ∧ c=none ∨ ∃ x y:ℝ,b=some x∧ c=some y∧ |x-y|≤ d
lemma CronBoardR (u:∀ i,‖A i‖≤ B)(p:0<r)(g:0≤d) (h:∀ i,|x i j-y i j|≤d)
 (e:∀ i k,k ≠ j→ x i k=y i k)
 (v:Cron_R C σ A (2*r) b x L)(w:Cron_R C σ A (2*r) c y L)(f: PoleR d b c)(F:0≤ B): ‖(X).roadList L x b - (X).roadList L y c‖≤ L.length*(r⁻¹*(2*d))*B^L.length:=by
 let T:=r⁻¹ * (2*d); have hT:0≤T:= mul_nonneg (inv_nonneg.mpr p.le) (mul_nonneg (by norm_num) g)
 induction L generalizing b c with
 | nil=> rw[List.length_nil]; simp only [roadList]; simp
 | cons i L ih=>
   obtain ⟨a,v⟩:=v; obtain ⟨a',w⟩:=w
   let t:=(X).sep b i (x i); let t':= (X).sep c i (y i)
   let o(x:I→Axis→ℝ):ℝ:=(X).endline (x i) i; let J(x:I→Axis→ℝ):Η:=(X).roadList L x (some (o x)); let D:L.Nodup→ℕ:= fun _=>0 -- tune
   let K:= Strut_R C σ A i (x i); let C₀:=(X).rise i
   have hh(K:I→Axis→ℝ): (X).frontend (K i) i= K i j-(C₀:ℝ):=rfl
   have hx: |(X).frontend (x i) i-(X).frontend (y i) i|≤d:=by rw[hh x,hh y,sub_sub_sub_cancel_right]; apply h
   have he:‖C.BrightHab.E t-C.BrightHab.E t'‖≤ T:=by
      rcases f with ⟨hb,hc⟩|⟨z,z',ht,hc,h'⟩
      · unfold t t'; rw[hb,hc]; change ‖C.BrightHab.E 0-C.BrightHab.E 0‖ ≤ _; rw[sub_self,norm_zero]; exact hT
      let F':=(X).frontend (x i) i; let V':=(X).frontend (y i) i
      have ha: 2*r ≤ F'-z:= a z ht; have hz:2*r ≤ V'-z':=a' z' hc
      have hp:0≤2*r:=mul_nonneg (by norm_num) p.le; have hg:(t:ℝ)= F'-z:=by unfold t; rw [ht]; exact Real.coe_toNNReal _ (hp.trans ha)
      have hf:(t':ℝ)=V'-z':=by unfold t'; rw [hc]; exact Real.coe_toNNReal _ (hp.trans hz)
      apply le_trans (RaateR _ _ _ t t' r p (by rw[hg]; exact ha) (by rw[hf]; exact hz)); rw[hg,hf]; apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr p.le)
      rw[show F'-z-(V'-z')=(F'-V')-(z-z') by ring,two_mul]; exact (abs_sub ..).trans (add_le_add hx h') -- check abs_sub
   have hq:‖K‖≤B:= (StrutF_R C σ A i (x i)).trans (u i); let Y:= B^L.length
   have V:‖J x-J y‖≤ L.length*T*Y:=ih _ _ v w (Or.inr (show ∃x₀ y₀:ℝ,some (o x)=some x₀∧some (o y)=some y₀∧ _ from ?_))
   swap; · refine ⟨_,_,rfl,rfl,?_⟩; unfold o; simp only [endline, add_sub_add_right_eq_sub]; exact hx
   let G:=(X).roadList (i::L) x b; let H:=(X).roadList (i::L) y c
   have hv : G= (C.BrightHab.E t * K) (J x):= DFunLike.congr_fun (gaitR C σ A x i b) (J x)
   have hw : H= (C.BrightHab.E t' * K) (J y):=by unfold K; rw [StrutσR C σ A x y i (e i)]; exact DFunLike.congr_fun (gaitR C σ A y i c) (J y)
   have hs:G-H= C.BrightHab.E t (K (J x-J y))+(C.BrightHab.E t-C.BrightHab.E t') (K (J y)):=by
      rw[hv,hw, map_sub,map_sub,ContinuousLinearMap.sub_apply]; change (C.BrightHab.E t) _-(C.BrightHab.E t') _=_; abel
   have hz:∀ y:Η, ‖K y‖≤B*‖y‖:= fun i=> (K.le_opNorm _).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg i))
   change ‖G-H‖≤ (i::L).length*T*B^(i::L).length; rw[hs,List.length_cons, pow_succ,Nat.cast_add,Nat.cast_one]; refine (norm_add_le ..).trans ?_
   let z:= K (J x-J y); let z':=K (J y); have hV: ‖C.BrightHab.E t z‖≤ B*(L.length*T*Y):= ((C.BrightHab.E t).le_opNorm z).trans ((mul_le_of_le_one_left (norm_nonneg z) ((ζ).shrinks t)).trans ((hz _).trans (mul_le_mul_of_nonneg_left V F)))
   refine (add_le_add hV ?_).trans_eq (show _+ T*(B*Y)=_ from ?_)
   · let W:= C.BrightHab.E t-C.BrightHab.E t'; exact (W.le_opNorm z').trans (mul_le_mul he ((hz _).trans (mul_le_mul_of_nonneg_left (FleetAmtR C σ A y (some (o y)) L B F u) F)) (norm_nonneg _) hT)
   unfold Y; ring
lemma CronΨR (u:∀ i,‖A i‖≤ B) (F:0≤ B) (p:0<r)(g:0≤d)(v:∀ i,|x i j-y i j|≤ d)(e:∀ i k,k ≠ j→x i k=y i k)(t:Cron_R C σ A (2*r) none x L)(t':Cron_R C σ A (2*r) none y L) : ‖Repertoire.reading (StageR σ C A) L x-Repertoire.reading (StageR σ C A) L y‖ ≤ L.length*(r⁻¹*(2*d))*B^L.length:=by
 unfold Repertoire.reading; rw [←inner_sub_right]; refine (norm_inner_le_norm ..).trans ?_; rw [show ‖(X).origin‖= 1 from C.normΩ,one_mul]; exact CronBoardR C σ A x y none L none r B d u p g v e t t' (Or.inl ⟨rfl,rfl⟩) F
#print axioms CronΨR
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end

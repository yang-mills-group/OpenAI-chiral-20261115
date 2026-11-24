import GaugeFieldConstruction.LayGateQ
import GaugeFieldConstruction.HitachiQ
import GaugeFieldConstruction.DresdenJ
import GaugeFieldConstruction.FrayTideJ
import GaugeFieldConstruction.SteepleJ
import GaugeFieldConstruction.MovingH
import GaugeFieldConstruction.ZagoraJ
import GaugeFieldConstruction.VirenneJ
import GaugeFieldConstruction.TrollopJ
import GaugeFieldConstruction.ZucatoJ
import GaugeFieldConstruction.KronenJ
import GaugeFieldConstruction.MapicoJ
import GaugeFieldConstruction.LongBowJ
import GaugeFieldConstruction.OrigamiJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.TuristaJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.MoonθεJ
import GaugeFieldConstruction.LucernaJ
import GaugeFieldConstruction.EmeraldYJ
import GaugeFieldConstruction.Limbra3
import GaugeFieldConstruction.AshtonM
import GaugeFieldConstruction.Accomplished
import GaugeFieldConstruction.Kabul
import GaugeFieldConstruction.Fana
import GaugeFieldConstruction.Garlic
import GaugeFieldConstruction.Ochre
import GaugeFieldConstruction.Coral
import GaugeFieldConstruction.Dales
import GaugeFieldConstruction.Harries
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
variable (P:Spine) {X:Type}[Fintype X][LinearOrder X]
open ProbeθJ Preparation Yoke
-- Pose. Film any from Advent plus f mirrors. only valid Stamps.S.
local notation "KΑ"=>P.calibration
local notation "Kγ"=>P.par
local notation "Lγ"=> P.par.R.L
local notation "ℓν"=>P.par.R.L.val
local notation "HΥ"=> inkΛJ
variable (x:P.VMark) (f s:ℕ) (j:Axis)
open Etch
local notation "zA" s:max=> GrowJ P f s
local notation "κs"=> (GrowJ P f s:ℤ)
local notation "W_η"=> WorkWJ P f
local notation "ws"=> GrowJ P f s* WorkWJ P f
local notation "Zγ"=>Mapnest P f x
local notation "ΚΩ"=> XûJ P.par P.width f
local notation "Θζ"=> HearthJ P f s x j
local notation "Vg"=> fShiftJ P f j x
local notation "ΕΦ"=> ruler (KΑ).B
local notation "ZΩ" => pet (Mapnest P f x) j 0
local notation "ℓχ" => P.par.R.L.val
open WallsQ
open SlabMark.Weir
abbrev AgateQ (P:Spine): Side:=⟨(tierW P.run).toNat,(by have t:= tierW_pos P.run; omega)⟩ -- maybe Side parity? only >0
lemma AgateBondQ:(↑(AgateQ P).val:ℤ)=tierW P.run:=Int.toNat_of_nonneg (tierW_pos _).le -- tune lemma typo
variable (m:ℕ)
-- required margin 30* lens in gauge clock anchor coordinates. a offset χ di.
abbrev cautionQ (P:Spine)(f:ℕ):ℕ:=30*XûJ P.par P.width f
abbrev chordQ(P:Spine)(f:ℕ):ℕ:=(2*cautionQ P f+1)
def WailsQ(P:Spine)(f m:ℕ): ℕ:= Nat.find (show ∃ a:ℕ,(m+1)*chordQ P f≤ P.par.R.L.val^a from by exact pow_unbounded_of_one_lt _ ((show 1<3 by decide).trans_le P.par.R.coarse)) -- pow_unbounded has lt
abbrev WoodQ (P:Spine)(f m:ℕ):ℕ:= (AgateQ P).val*P.par.R.L.val^(WailsQ P f m)
local notation "Z₁"=> AgateQ P
local notation "ιw"=> WailsQ P f m
local notation "wQ"=> WoodQ P f m
local notation "Vκ"=> chordQ P f
local notation "ζp"=> cautionQ P f
lemma WoodFloorQ:(m+1)* chordQ P f ≤ P.par.R.L.val^ WailsQ P f m:=by unfold WailsQ; apply Nat.find_spec (p:=fun a=> (m+1)*chordQ P f≤P.par.R.L.val^a)
lemma WoodQ_cast : (↑(WoodQ P f m):ℤ)= westW P.run (WailsQ P f m):=by unfold WoodQ westW; rw[Nat.cast_mul,Nat.cast_pow,AgateBondQ]
lemma WoodQ.sold (p:f≤ s): ((↑(GrowJ P f s*WoodQ P f m)):ℤ)=westW P.run (WailsQ P f m+(s-f)):=by rw[Nat.cast_mul,WoodQ_cast]; unfold westW GrowJ; rw [pow_add]; push_cast; ring
lemma WoodCeilQ : WoodQ P f m ≤ (AgateQ P).val*((m+1)*chordQ P f)*P.par.R.L.val:=by
 unfold WoodQ; rw[mul_assoc]; apply Nat.mul_le_mul_left
 generalize hv: WailsQ P f m=a
 cases a with
 | zero=> have t:= P.par.R.L.property; rw [pow_zero]; apply Nat.succ_le_of_lt; unfold chordQ; positivity
 | succ a=>
    rw [pow_succ]; gcongr; have h0:a<ιw:=by omega
    unfold WailsQ at h0; have hp:= Nat.find_min _ h0
    exact (not_le.mp hp).le
-- pigeon. Forbidden interval residual relative to cyclic grid. use ad hoc stride.
private lemma LuckK (i:ℤ)(n:ℕ)(w:0<n):∃ d:ℤ,(n:ℤ)*d ≤ i ∧ i< (n:ℤ)*(d+1):=by
 let a:= (n:ℤ); have ha:0<a:=by unfold a; exact_mod_cast w
 have t:= Int.emod_nonneg i ha.ne'; have hp:=Int.emod_lt_of_pos i ha; have h:= Int.emod_add_mul_ediv i a; use (i/a); rw [mul_add,mul_one]; unfold a at *; omega
private lemma LuckyQ (k r:ℕ)(p:f≤ s)(h:k≤ m) (L:Fin k→ℤ) :∃ x:ℤ,tierW P.run∣x ∧∀ i:Fin k,∃ c:ℤ,x+(WoodQ P f m:ℤ)*c+cautionQ P f≤ L i ∧ L i+cautionQ P f≤x+(WoodQ P f m:ℤ)*(c+1):=by
 let d:= (AgateQ P).val; let u:= cautionQ P f; let Q:= chordQ P f; let W:= WoodQ P f m
 let D:= (Q*d:ℤ); let S:=Fin (k+1); have e: (m+1)*Q*d ≤ W:=by unfold W; rw [mul_comm]; exact Nat.mul_le_mul_left _ (WoodFloorQ P f m)
 have d0:0<d:= (AgateQ P).property; have u0:Q=2*u+1:=rfl; have w0:0<W:=by
    apply lt_of_lt_of_le _ e; rw [u0]; positivity
 have Hp:(2:ℤ)*↑u <D:=by
    unfold D; rw[u0]; have hp:(1:ℤ)≤ d:=by omega
    push_cast; nlinarith
 have Hw:(k+1:ℕ)* D ≤ (W:ℤ):=by
    unfold D; rw [←mul_assoc]; exact_mod_cast (le_trans (show (k+1)*Q*d≤ _ from Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.succ_le_succ h))) e)
 let X(i:S):ℤ:=D*i.val; have ht(i:S):tierW P.run∣X i:=by
    refine ⟨Q*i.val,?_⟩; rw [←AgateBondQ]; unfold X D d; push_cast; ring
 let Lucky (i:Fin k)(x:ℤ):Prop:= ∃ c:ℤ,x+(W:ℤ)*c+u≤ L i∧ L i+u ≤ x+(W:ℤ)*(c+1)
 suffices e:∃ x:S,∀i,Lucky i (X x) by obtain ⟨x,h⟩:=e; exact ⟨_,ht x,h⟩
 by_contra! a
 classical
 choose I b using a
 have bad (i:Fin k)(j:S)(p:¬ Lucky i (X j)) :∃ c:ℤ,X j+(W:ℤ)*c-u ≤ L i ∧ L i ≤ X j+(W:ℤ)*c+u:=by
    obtain ⟨c,t,e⟩:=LuckK (L i-X j) W w0; by_cases h:X j+(W:ℤ)*c+u≤ L i
    · refine ⟨c+1,?_,?_⟩
      · have hx:¬ (L i+u ≤ X j+(W:ℤ)*(c+1)):=fun x=> p ⟨c,h,x⟩; omega
      omega
    exact ⟨c,by omega,by omega⟩
 have pos (i j:S)(t:i<j) (r q:ℤ)(a:r ≤ q) : X i + W*r + 2*(u:ℤ)< X j+ W*q:=by
    unfold X; have h1:= mul_le_mul_of_nonneg_left a (Nat.cast_nonneg (α:=ℤ) W); have hg: (i.val:ℤ)+1≤j.val:=by change i.val < j.val at t; omega
    nlinarith
 have neg (i j:S)(t:i<j)(r q:ℤ)(a:q<r): X j+ W*q+2*(u:ℤ)< X i+W*r:=by
    have h0:=mul_le_mul_of_nonneg_left (show q+1 ≤ r from a) (Nat.cast_nonneg (α:=ℤ) W); unfold X; have hj:(j.val:ℤ) ≤ (k:ℤ):=by have t:j.val< k+1:=j.isLt; omega
    push_cast at Hw; nlinarith
 have ltQ (i j:S)(t:i<j): I i≠ I j:=by
    intro h; have v:=b i; rw[h] at v; obtain ⟨r,b1,e1⟩:= bad _ _ v; obtain ⟨q,b2,e2⟩:=bad _ _ (b j); rcases le_or_gt r q with a|a
    · have ht:=pos i j t r q a; omega
    have he:=neg i j t r q a; omega
 have hp:Injective I:=by intro i j p; exact eq_of_le_of_ge (le_of_not_gt fun h=> ltQ j i h p.symm) (le_of_not_gt fun h=> ltQ i j h p)
 have hg:= Fintype.card_le_of_injective _ hp; simp only [S,Fintype.card_fin] at hg; omega
lemma AborQ(k:ℕ)(h:k ≤ m)(T:Fin k→ Cover):∃ (σ:Cover)(o:Fin k→ Cover), chute P.run σ ∧∀ x:Fin k,InsetQ (WoodQ P f m) σ (o x) (T x) (cautionQ P f):=by
 choose x hx o h0 v using fun j:Axis=> LuckyQ P f f m k 0 le_rfl h (fun i=>T i j)
 exact ⟨x,fun i j=>o j i,hx,fun i j=>⟨h0 _ _,v _ _⟩⟩
lemma chute_scale {o}(u:chute P.run o):chute P.run (fWigQ P f s o):=by
 intro i; exact dvd_mul_of_dvd_right (u i) _
#print axioms AborQ
#print axioms WoodCeilQ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end

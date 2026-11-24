import Ridgetop.Release
import Ridgetop.SignalR
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
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
namespace PledgeT
open Calico
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
open Ridgetop
local notation "Yx"=> P.par.x
local notation "Qt"=> P.par.K.top.clip
local notation "zL"=> P.par.R.L
local notation "β*" s:max=>hat zL Yx s -- check price.beta later
open CF.Onyx CF.Ember Next.SectorChange
local notation "τe"=> scaleY
abbrev mudF :ℝ:= @Ridgetop.extent SU.group (Qt)
lemma mud_pos: 0 ≤ mudF P:=by unfold mudF Ridgetop.extent wingN; have he:=kold (Qt); positivity
local notation "χ" s:max=> scaleY (hat P.par.R.L P.par.x s)
local notation "ρ" i:max=> P.period (P.projection.rows i)
local notation "ζ" i:max=> P.cutoff (P.projection.columns i)
local notation "Y"=> P.run
-- period side gauges
noncomputable abbrev showF(P:Spine)(s i:ℕ):Side:= More (count P.run s (P.period (P.projection.rows i)))
noncomputable abbrev pathM(P:Spine)(s i:ℕ):Bed:= P.par.V.L.H (P.run.uv (P.cutoff (P.projection.columns i))-s)
local notation "γ" s:max i:max=> gram Y s (ρ i) (ζ i)
local notation "y" s:max i:max=> Real.sqrt (β* s)*coupling (γ s i).beta
local notation "Nq" s:max i:max=> showF P s i
local notation "Mq" s:max i:max=> pathM P s i
noncomputable abbrev docket(P:Spine)(s i:ℕ)(o:Bool→ Cover):ℂ:= yoking (pathM P s i) (wrap (showF P s i) (nodeC (o false))) (wrap (showF P s i) (nodeC (o true)))
noncomputable abbrev adage(P:Spine)(s i:ℕ)(o:Bool→ Cover):ℝ:= sconeR (pathM P s i) (wrap (showF P s i) (nodeC (o false))) (wrap (showF P s i) (nodeC (o true)))
lemma legsCore:0<SU.group.lieDim:=by
 let G:= SU.group; haveI: Nontrivial G.Color:= Thera.yet_one.nontrivial_color
 change 0<G.lieDim; rw [Gauge.lieDim,← G.colorIso.finrank_eq]; exact Module.finrank_pos
lemma evenShow(i:ℕ): Even (showF P s i).val:= ⟨(count Y s (ρ i)).val,by change ((count Y s (ρ i)).val*2)=_; omega⟩
local notation "ν"=> ((Fintype.card SU.group.ColorIndex):ℝ)
lemma color₁:1 ≤ ν:= by
 norm_cast
 change 1 ≤ Fintype.card (Fin SU.group.lieDim); rw [Fintype.card_fin]; exact legsCore
lemma sweep_cast(i:ℕ): (adage P s i o:ℂ)=docket P s i o:=by
 let F:= P.run.uv (ζ i)-s; let a:= P.par.V; have g:=a.L.roof F
 exact (ofGeorge (a.L.mood F) (a.L.tied F) (g.2.1 _) (show SU.group.ColorIndex from ⟨0,legsCore⟩) a.W.reserve g.1 P.par.K.width (g.2.1 _) (evenShow P s i) _ _).symm
lemma sweep_primary(i:ℕ): let u:=y s i;
 |boarding P s A o true i - (u^4 * ν/2)*adage P s i o| ≤ mudF P*(hatch A (β* s)).cost⁻¹ ^2 * |u|^6:=by
 intro u
 let F:= P.run.uv (ζ i)-s; let a:= P.par.V; have g:=a.L.roof F; let X:= pedestal o (count Y s (ρ i)); let B0:=P.par.V.L.mood F; let P0:=P.par.V.L.tied F
 have h:= section_is B0 P0 (g.2.1 (Nq s i)) (X false) (X true) (hatch A (β* s)) a.W.reserve u
 rw [pewter B0 P0 (g.2.1 _) _ _ a.W.reserve (g.2.2 _)] at h; unfold boarding berlin; dsimp only
 rw [show (fun i:Bool=> if i then X true else X false)=X from funext fun i=> by cases i<;>rfl] at h
 rw [show ∀ i:ℝ,u^4/4*(2*ν*i)=u^4*ν/2*i from (fun i=>by ring)] at h; exact h
noncomputable abbrev ocore(P:Spine)(s i:ℕ):ℝ:= let uν:ℝ:= Fintype.card SU.group.ColorIndex; (Real.sqrt (hat P.par.R.L P.par.x s)* coupling (gram P.run s (P.period (P.projection.rows i)) (P.cutoff (P.projection.columns i))).beta)^4*uν/2
lemma ration(i:ℕ)(ht: s ≤ P.run.uv (ζ i)): 1/32 ≤ ocore P s i ∧
  |boarding P s A o true i- (ocore P s i)*adage P s i o| ≤ (mudF P*64)*(χ s)⁻¹ ^(2*heightH A):=by
 have hv:0<β* s:= ((Real.exp_pos 1).trans_le P.large).trans_le (Vale.crown zL Yx s)
 obtain ⟨_,_,_,b0,w⟩:= prices_plot Y s (ρ i) (ζ i) ht
 have hp:Set.Icc (1/2:ℝ) 2 (y s i):= Regis.Head.Etch.railB b0.1 b0.2 hv
 let u:=y s i; have H:1/2 ≤ u:=hp.1; have V:u ≤ 2:=hp.2; have h0:0 ≤ u:=by linarith
 have he:=mud_pos P
 constructor
 · change 1/32 ≤ u^ (4:ℕ)*ν/2
   calc _ ≤ ((1/2:ℝ)^ (4:ℕ))*1/2:=by norm_num
        _ ≤ _:= by gcongr; exact color₁
 have h:=sweep_primary P s A o i; change _ ≤ mudF P*_⁻¹ ^ (2:ℕ)*_ at h
 apply h.trans; change mudF P*((χ s)^heightH A)⁻¹^(2:ℕ)* |u|^6 ≤ _
 rw [← inv_pow,← pow_mul,mul_comm (heightH A),abs_of_nonneg h0]; have hg:0 ≤ (χ s)⁻¹ := inv_nonneg.mpr (zero_le_one.trans (summitT _))
 have hv:u^6 ≤64:= (pow_le_pow_left₀ h0 V 6).trans (by norm_num)
 exact (mul_le_mul_of_nonneg_left hv (mul_nonneg he (by positivity))).trans_eq (by ring)
#print axioms ration
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
